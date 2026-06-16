(** This module implements a bidirectional type checker for Hopix. *)

open HopixAST

(** Error messages *)

let invalid_instantiation pos given expected =
  HopixTypes.type_error pos (
      Printf.sprintf
        "Invalid number of types in instantiation: \
         %d given while %d were expected." given expected
    )
let check_equal_types pos ~expected ~given =
  if expected <> given
  then
    HopixTypes.(type_error pos
                  Printf.(sprintf
                            "Type mismatch.\nExpected:\n  %s\nGiven:\n  %s"
                            (string_of_aty expected)
                            (string_of_aty given)))

(** linearity-checking code for patterns *)

(** verifie qu'une variable n'est pas deja liee dans le motif *)
let check_pattern_Pvariable vars id position =
  let x = Position.value id in
  if List.mem x vars then
    HopixTypes.type_error position 
      (Printf.sprintf "The variable %s has already appeared in this pattern." 
         (match x with Id s -> s))
  else
    x :: vars

(**
  on verifie qu'il n'y a pas de variable dupliquee
  pour "POr" (p1 | p2), chaque branche est verifiee a part 
*)
let rec check_pattern_linearity vars motif =
  let Position.{ value = valeur; position; } = motif in
  match valeur with
  | PWildcard -> vars
  | PLiteral _ -> vars
  | PVariable id -> check_pattern_Pvariable vars id position
  | PTypeAnnotation (pat, _) -> check_pattern_linearity vars pat
  | PTuple motifs -> List.fold_left check_pattern_linearity vars motifs
  | PTaggedValue (_, _, motifs) -> List.fold_left check_pattern_linearity vars motifs
  | PRecord (champs, _) ->  List.fold_left (fun acc (_, pat) -> check_pattern_linearity acc pat) vars champs
  | POr motifs ->
      List.iter (fun p -> ignore (check_pattern_linearity [] p)) motifs;
      (match motifs with
       | [] -> vars
       | premier :: _ -> check_pattern_linearity vars premier)
  | PAnd motifs -> List.fold_left check_pattern_linearity vars motifs

(** Type-checking code *)

let check_type_scheme :
      HopixTypes.typing_environment ->
      Position.t ->
      HopixAST.type_scheme ->
      HopixTypes.aty_scheme * HopixTypes.typing_environment
  = fun env pos (ForallTy (ts, ty)) ->
  let env = HopixTypes.bind_type_variables pos env (List.map Position.value ts) in
  let aty = HopixTypes.internalize_ty env ty in  
  (HopixTypes.Scheme (List.map Position.value ts, aty), env)


let rec synth_literal : HopixAST.literal -> HopixTypes.aty =
  fun l ->
  match l with
  | LInt _ -> HopixTypes.hint
  | LString _ -> HopixTypes.hstring
  | LChar _ -> HopixTypes.hchar

(** 
  verifie qu'un motif a le type attendu
  retourne le nouvelle environnement etendu
  - bind_value: ajoute la varible dans l'environnement
  - monomorphic_type_scheme: cree un schema de type sans variables liees
*)
and check_pattern :
          HopixTypes.typing_environment ->
          HopixAST.pattern Position.located ->
          HopixTypes.aty ->
          HopixTypes.typing_environment
  = fun env Position.({ value = p; position = pos; }) attendu ->
  match p with
  | PVariable id -> HopixTypes.bind_value (Position.value id) (HopixTypes.monomorphic_type_scheme attendu) env
  | PWildcard -> env
  | PLiteral lit -> check_equal_types pos ~expected:attendu ~given:(synth_literal (Position.value lit)); env  
  | PTypeAnnotation (motif, ty) -> check_pattern_annotation env pos motif ty attendu
  | PTuple motifs -> check_pattern_tuple env pos motifs attendu
  | PTaggedValue (k, ty_opt, motifs) -> check_pattern_tagged_value env pos k ty_opt motifs attendu
  | PRecord (champs, ty_opt) -> check_pattern_record env pos champs ty_opt attendu
  | POr motifs -> check_pattern_or env motifs attendu
  | PAnd motifs -> check_pattern_and env motifs attendu

(**
  - internalize_ty: convertit un type ast en type aty
*)
and check_pattern_annotation env pos pattern ty expected =
  let annotated_ty = HopixTypes.internalize_ty env ty in
  check_equal_types pos ~expected ~given:annotated_ty;
  check_pattern env pattern annotated_ty

(**
  - destruct_product_type: extrait les types des elements d'un type produit
*)
and check_pattern_tuple env pos pattern expected =
  let expected_tys = HopixTypes.destruct_product_type pos expected in
  if List.length pattern <> List.length expected_tys then
    HopixTypes.type_error pos 
      (Printf.sprintf "Tuple pattern has %d elements but type has %d"
        (List.length pattern) (List.length expected_tys));
  List.fold_left2 (fun env' pat' ty' -> check_pattern env' pat' ty') env pattern expected_tys

(** chaque branche doit avoir le meme type *)
and check_pattern_or env motifs attendu =
  match motifs with
  | [] -> env
  | premier :: reste ->
      let env' = check_pattern env premier attendu in
      List.iter (fun pat' -> ignore (check_pattern env pat' attendu)) reste;
      env'

(** on fusionne les environnements *)
and check_pattern_and env pattern expected =
  List.fold_left (fun env' pat' -> check_pattern env' pat' expected) env pattern

(**
  - lookup_type_scheme_of_constructor: recupere le schema de type d'un constructeur
  - internalize_ty: convertit un type ast en type aty
  - instantiate_type_scheme: instancie un schema de type avec des types concrets
  - destruct_function_type_maximally: extrait tous les arguments et le type de retour
*)
and check_pattern_tagged_value env pos k ty_opt motifs attendu =
  let k_scheme = HopixTypes.lookup_type_scheme_of_constructor pos (Position.value k) env in
  let k_ty = 
    match ty_opt with
    | Some tys ->
        let atys = List.map (HopixTypes.internalize_ty env) tys in
        (try HopixTypes.instantiate_type_scheme k_scheme atys
         with HopixTypes.InvalidInstantiation { expected = e; given = g } ->
           invalid_instantiation pos g e)
        (* sans annotation on utilise des variables nouvelles *)
    | None -> HopixTypes.instantiate_type_scheme k_scheme []
  in
  (* extraire les types des arguments du constructeur et le type de retour *)
  let types_arg, type_ret = HopixTypes.destruct_function_type_maximally pos k_ty in
  (* verifier que le type de retour correspond au type attendu *)
  check_equal_types pos ~expected:attendu ~given:type_ret;
  (* verifier le nombre d'arguments *)
  if List.length motifs <> List.length types_arg then (
    let KId k_name = Position.value k in
    HopixTypes.type_error pos 
      (Printf.sprintf "Constructor %s expects %d arguments but %d given"
        k_name (List.length types_arg) (List.length motifs))
  );
  (* verifier chaque sous-motif *)
  List.fold_left2 (fun env' pat' ty' ->
    check_pattern env' pat' ty'
  ) env motifs types_arg

(**
  verifie un motif d'enregistrement
  - lookup_type_constructor_of_label: recupere le constructeur de type associe a un label
  - internalize_ty: convertit un type ast en type aty
  - instantiate_type_scheme: instancie un schema de type avec des types concrets
  - lookup_type_scheme_of_label: recupere le schema de type d'un label
  - destruct_function_type: extrait le type argument et le type retour d'un type fonction
*)
and check_pattern_record env pos champs ty_opt attendu =
  let tc, arity, labels = check_record_get_type_info env pos champs in
  let type_enreg = check_record_instantiate_type env pos tc arity ty_opt attendu in
  check_equal_types pos ~expected:attendu ~given:type_enreg;
  check_record_all_fields_present pos champs labels;
  check_record_fields env pos champs ty_opt

(** recupere le constructeur de type et les labels d'un enregistrement *)
and check_record_get_type_info env pos champs =
  match champs with
  | [] -> HopixTypes.type_error pos "Empty record pattern"
  | (l, _) :: _ ->
      try HopixTypes.lookup_type_constructor_of_label pos (Position.value l) env
      with HopixTypes.Unbound (_, HopixTypes.Label (LId nom_label)) ->
        HopixTypes.type_error pos 
          (Printf.sprintf "There is no type definition for label `%s'." nom_label)

(** instancie le type de l'enregistrement *)
and check_record_instantiate_type env pos tc arity ty_opt attendu =
  match ty_opt with
  | Some tys ->
      let atys = List.map (HopixTypes.internalize_ty env) tys in
      if List.length atys <> arity then
        invalid_instantiation pos (List.length atys) arity;
      HopixTypes.ATyCon (tc, atys)
  | None -> attendu

(** verifie que tous les champs sont presents *)
and check_record_all_fields_present pos champs labels =
  let labels_motif = List.map (fun (l, _) -> Position.value l) champs in
  let tous_presents = List.for_all (fun l -> List.mem l labels_motif) labels in
  if not tous_presents then
    HopixTypes.type_error pos "Incomplete record pattern"

(** verifie chaque champ de l'enregistrement *)
and check_record_fields env pos champs ty_opt =
  List.fold_left (fun env' (l, pat') ->
    let schema_l = check_record_get_label_scheme env pos l in
    let type_l = check_record_get_label_type env schema_l ty_opt in
    let _, type_champ = HopixTypes.destruct_function_type pos type_l in
    check_pattern env' pat' type_champ
  ) env champs

(** recupere le schema de type d'un label *)
and check_record_get_label_scheme env pos l =
  try HopixTypes.lookup_type_scheme_of_label pos (Position.value l) env
  with HopixTypes.Unbound (_, HopixTypes.Label (LId nom_label)) ->
    HopixTypes.type_error pos 
      (Printf.sprintf "There is no type definition for label `%s'." nom_label)

(** calcule le type d'un label *)
and check_record_get_label_type env schema_l ty_opt =
  match ty_opt with
  | Some tys ->
      let atys = List.map (HopixTypes.internalize_ty env) tys in
      HopixTypes.instantiate_type_scheme schema_l atys
  | None ->
      let HopixTypes.Scheme (_, ty) = schema_l in
      ty

and synth_pattern :
      HopixTypes.typing_environment ->
      HopixAST.pattern Position.located ->
      HopixTypes.aty * HopixTypes.typing_environment
  = fun env Position.{ value = p; position = pos; } ->
  match p with
  | PLiteral lit -> synth_pattern_literal env lit
  | PTypeAnnotation (motif, ty) -> synth_pattern_annotation env motif ty
  | PTaggedValue (k, ty_opt, motifs) -> synth_pattern_tagged env pos k ty_opt motifs
  | _ -> HopixTypes.type_error pos "Cannot synthesize type for this pattern"

and synth_pattern_literal env lit =
  let ty = synth_literal (Position.value lit) in
  (ty, env)

and synth_pattern_annotation env motif ty =
  let type_annote = HopixTypes.internalize_ty env ty in
  let env' = check_pattern env motif type_annote in
  (type_annote, env')

and synth_pattern_tagged env pos k ty_opt motifs =
  let schema_k = HopixTypes.lookup_type_scheme_of_constructor pos (Position.value k) env in
  let type_k = match ty_opt with
    | Some tys -> 
        let types = List.map (HopixTypes.internalize_ty env) tys in
        HopixTypes.instantiate_type_scheme schema_k types
    | None -> 
        HopixTypes.instantiate_type_scheme schema_k []
  in
  let types_arg, type_ret = HopixTypes.destruct_function_type_maximally pos type_k in
  let env' = List.fold_left2 (fun env' motif ty ->
    check_pattern env' motif ty
  ) env motifs types_arg in
  (type_ret, env')

let synth_variable env pos id ty_list_opt =
  let schema = HopixTypes.lookup_type_scheme_of_identifier pos (Position.value id) env in
  let types = match ty_list_opt with
    | Some tys -> List.map (HopixTypes.internalize_ty env) tys
    | None -> []
  in
  HopixTypes.instantiate_type_scheme schema types

let rec synth_tuple env exprs =
  let tys = List.map (synth_expression env) exprs in
  HopixTypes.hprod tys

and synth_tagged env pos k ty_opt exprs =
  let schema_k =
    HopixTypes.lookup_type_scheme_of_constructor pos (Position.value k) env
  in
  let type_k =
    match ty_opt with
    | Some tys ->
        let types = List.map (HopixTypes.internalize_ty env) tys in
        (try HopixTypes.instantiate_type_scheme schema_k types with
         | HopixTypes.InvalidInstantiation { expected = attendu; given = donne } ->
             invalid_instantiation pos donne attendu)
    | None ->
        HopixTypes.instantiate_type_scheme schema_k []
  in
  let rec appliquer_constructeur ty = function
    | [] -> ty
    | expr :: reste ->
        let type_arg, type_ret = HopixTypes.destruct_function_type pos ty in
        check_expression env expr type_arg;
        appliquer_constructeur type_ret reste
  in
  appliquer_constructeur type_k exprs

and synth_apply env pos f arg =
  let type_f = synth_expression env f in
  let type_arg, type_ret = HopixTypes.destruct_function_type pos type_f in
  check_expression env arg type_arg;
  type_ret

and synth_case env pos expr branches =
  let type_expr = synth_expression env expr in
  let type_resultat = ref None in
  List.iter (fun branche ->
    match Position.value branche with
    | Branch (motif, corps) ->
        let _ = check_pattern_linearity [] motif in
        let env' = check_pattern env motif type_expr in
        let type_corps = synth_expression env' corps in
        match !type_resultat with
        | None -> type_resultat := Some type_corps
        | Some ty -> check_equal_types pos ~expected:ty ~given:type_corps
  ) branches;
  match !type_resultat with
  | Some ty -> ty
  | None -> HopixTypes.type_error pos "Empty case expression"

and synth_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty
  = fun env Position.{ value = e; position = pos; } ->
    match e with
    | Literal l -> synth_literal (Position.value l)
    | Variable (id, ty_list_opt) -> synth_variable env pos id ty_list_opt
    | Tuple exprs -> synth_tuple env exprs
    | Tagged (k, ty_opt, exprs) -> synth_tagged env pos k ty_opt exprs
    | Record (fields, ty_opt) -> synth_record env pos fields ty_opt
    | Field (expr, l, _) -> synth_field env pos expr l 
    | Define (vdef, expr) -> synth_define env vdef expr
    | Apply (f, arg) -> synth_apply env pos f arg
    | Sequence exprs -> synth_sequence env exprs
    | Case (expr, branches) -> synth_case env pos expr branches
    | Ref expr -> synth_ref env expr
    | Read expr -> synth_read env pos expr
    | Assign (lhs, rhs) -> synth_assign env pos lhs rhs
    | While (cond, body) -> synth_while env cond body
    | For (id, start_e, end_e, body) -> synth_for env id start_e end_e body
    | Fun _ | TypeAnnotation _ ->
        HopixTypes.type_error pos "Cannot synthesize type for this expression (use type annotation)"
    | _ -> failwith "synth_expression: unhandled case"

(** synthetise le type d'un enregistrement *)
and synth_record env pos champs ty_opt =
  let (l, _) = List.hd champs in
  let tc, _, _ = HopixTypes.lookup_type_constructor_of_label pos (Position.value l) env in
  let type_enreg = match ty_opt with
    | Some tys ->
        let types = List.map (HopixTypes.internalize_ty env) tys in
        HopixTypes.ATyCon (tc, types)
    | None ->
        HopixTypes.type_error pos "Record construction requires type annotation"
  in
  List.iter (fun (l, expr) ->
    let schema_l = HopixTypes.lookup_type_scheme_of_label pos (Position.value l) env in
    let _, a = HopixTypes.destruct_constructed_type pos type_enreg in
    let type_champ = HopixTypes.instantiate_type_scheme schema_l a in
    let _, type_resultat = HopixTypes.destruct_function_type pos type_champ in
    check_expression env expr type_resultat
  ) champs;
  type_enreg

and synth_field env pos expr l  =
  let type_expr = synth_expression env expr in
  let schema_l = HopixTypes.lookup_type_scheme_of_label pos (Position.value l) env in
  let _, tys = HopixTypes.destruct_constructed_type pos type_expr in
  let type_champ = HopixTypes.instantiate_type_scheme schema_l tys in
  let _, type_resultat = HopixTypes.destruct_function_type pos type_champ in
  type_resultat

and synth_define env vdef expr =
  let env' = check_value_definition env vdef in
  synth_expression env' expr

and synth_sequence env exprs =
  let rec aux = function
    | [] -> HopixTypes.hunit
    | [e] -> synth_expression env e
    | e :: reste ->
        check_expression env e HopixTypes.hunit;
        aux reste
  in
  aux exprs

and synth_ref env expr =
  let ty = synth_expression env expr in
  HopixTypes.href ty

and synth_read env pos expr =
  let type_ref = synth_expression env expr in
  HopixTypes.destruct_reference_type pos type_ref

and synth_assign env pos gauche droite =
  let type_ref = synth_expression env gauche in
  let ty = HopixTypes.destruct_reference_type pos type_ref in
  check_expression env droite ty;
  HopixTypes.hunit

and synth_while env cond corps =
  check_expression env cond HopixTypes.hbool;
  check_expression env corps HopixTypes.hunit;
  HopixTypes.hunit

and synth_for env id debut fin corps =
  check_expression env debut HopixTypes.hint;
  check_expression env fin HopixTypes.hint;
  let env' = HopixTypes.bind_value (Position.value id) (HopixTypes.monomorphic_type_scheme HopixTypes.hint) env in
  check_expression env' corps HopixTypes.hunit;
  HopixTypes.hunit

and check_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty ->
      unit
  = fun env (Position.{ value = e; position = pos; } as exp) attendu ->
    match e with
    | Literal l -> check_expression_literal pos l attendu
    | IfThenElse (cond, alors, sinon) -> check_expression_if env cond alors sinon attendu
    | Fun (FunctionDefinition (motif, corps)) -> check_expression_fun env pos motif corps attendu
    | TypeAnnotation (expr, ty) -> check_expression_annotation env pos expr ty attendu
    | _ -> check_expression_synth env exp pos attendu

(** verifie un litteral *)
and check_expression_literal pos l attendu =
  let type_lit = synth_literal (Position.value l) in
  check_equal_types pos ~expected:attendu ~given:type_lit

(** verifie une conditionnelle *)
and check_expression_if env cond alors sinon attendu =
  check_expression env cond HopixTypes.hbool;
  check_expression env alors attendu;
  check_expression env sinon attendu

(** verifie une fonction anonyme *)
and check_expression_fun env pos motif corps attendu =
  let type_arg, type_ret = HopixTypes.destruct_function_type pos attendu in
  let _ = check_pattern_linearity [] motif in
  let env' = check_pattern env motif type_arg in
  check_expression env' corps type_ret

(** verifie une annotation de type *)
and check_expression_annotation env pos expr ty attendu =
  let type_annote = HopixTypes.internalize_ty env ty in
  check_expression env expr type_annote;
  check_equal_types pos ~expected:attendu ~given:type_annote

(** verifie par synthese puis comparaison *)
and check_expression_synth env exp pos attendu =
  let donne = synth_expression env exp in
  check_equal_types pos ~expected:attendu ~given:donne

(** verifie une valeur simple et retourne son type *)
and check_simple_value env id ty_opt expr =
  let type_actuel = 
    match ty_opt with
    | Some schema_ty ->
        let (HopixTypes.Scheme (vars, type_attendu)), _ = 
          Position.located_pos (check_type_scheme env) schema_ty in
        check_expression env expr type_attendu;
        HopixTypes.Scheme (vars, type_attendu)
    | None ->
        let type_infere = synth_expression env expr in
        HopixTypes.generalize_type env type_infere
  in
  HopixTypes.bind_value (Position.value id) type_actuel env

(** construit l'environnement avec les signatures des fonctions recursives *)
and build_recursive_env env fdefs =
  List.fold_left (fun env' (id, schema_opt, _) ->
    let pos = Position.position id in
    match schema_opt with
    | Some schema_ty ->
        let schema, _ = Position.located_pos (check_type_scheme env) schema_ty in
        HopixTypes.bind_value (Position.value id) schema env'
    | None -> HopixTypes.type_error pos "Recursive functions must be annotated with their type"
  ) env fdefs

(** verifie une definition de fonction recursive *)
and check_recursive_function  env pos  schema_ty motif corps fdefs =
  let schema, env_avec_vars = Position.located_pos (check_type_scheme env) schema_ty in
  let HopixTypes.Scheme (_, ty) = schema in
  let type_arg, type_ret = HopixTypes.destruct_function_type pos ty in
  let _ = check_pattern_linearity [] motif in
  let env_avec_funs = List.fold_left (fun e (id, schema_opt, _) ->
    match schema_opt with
    | Some ts ->
        let s, _ = Position.located_pos (check_type_scheme env) ts in
        HopixTypes.bind_value (Position.value id) s e
    | None -> e
  ) env_avec_vars fdefs in
  let env'' = check_pattern env_avec_funs motif type_arg in
  check_expression env'' corps type_ret

(** verifie toutes les fonctions recursives *)
and check_all_recursive_functions  env fdefs =
  List.iter (fun (id, schema_opt, def_fun) ->
    let pos = Position.position id in
    match schema_opt, def_fun with
    | Some schema_ty, FunctionDefinition (motif, corps) -> check_recursive_function  env pos schema_ty motif corps fdefs
    | None, _ -> HopixTypes.type_error pos "Recursive functions must be annotated with their type"
  ) fdefs

and check_value_definition :
      HopixTypes.typing_environment ->
      HopixAST.value_definition ->
      HopixTypes.typing_environment
  = fun env def ->
  match def with
  | SimpleValue (id, ty_opt, expr) -> check_simple_value env id ty_opt expr
  | RecFunctions fonctions ->
      let env_avec_noms = build_recursive_env env fonctions in
      check_all_recursive_functions env fonctions;
      env_avec_noms

let check_definition env = function
  | DefineValue vdef ->
     check_value_definition env vdef

  | DefineType (t, ts, tdef) ->
     let ts = List.map Position.value ts in
     HopixTypes.bind_type_definition (Position.value t) ts tdef env

  | DeclareExtern (x, tys) ->
     let tys, _ = Position.located_pos (check_type_scheme env) tys in
     HopixTypes.bind_value (Position.value x) tys env

let typecheck env programme =
  try
    List.fold_left (fun env d -> Position.located (check_definition env) d) env programme
  with 
  | HopixTypes.Unbound (pos, liaison) -> HopixTypes.type_error pos (Printf.sprintf "Unbound %s." (HopixTypes.string_of_binding liaison))
  | HopixTypes.InvalidInstantiation { expected = attendu; given = donne } -> HopixTypes.type_error Position.dummy ( Printf.sprintf "Invalid number of types in instantiation: %d given while %d were expected." donne attendu )

type typing_environment = HopixTypes.typing_environment

let initial_typing_environment = HopixTypes.initial_typing_environment

let print_typing_environment = HopixTypes.string_of_typing_environment
