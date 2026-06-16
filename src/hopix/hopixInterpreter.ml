open Position
open Error
open HopixAST

(** [error pos msg] reports execution error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of Hopix evaluates into a [value].

   The [value] type is not defined here. Instead, it will be defined
   by instantiation of following ['e gvalue] with ['e = environment].
   Why? The value type and the environment type are mutually recursive
   and since we do not want to define them simultaneously, this
   parameterization is a way to describe how the value type will use
   the environment type without an actual definition of this type.

*)
type 'e gvalue =
  | VInt       of Mint.t
  | VChar      of char
  | VString    of string
  | VUnit
  | VTagged    of constructor * 'e gvalue list
  | VTuple     of 'e gvalue list
  | VRecord    of (label * 'e gvalue) list
  | VLocation  of Memory.location
  | VClosure   of 'e * pattern located * expression located
  | VPrimitive of string * ('e gvalue Memory.t -> 'e gvalue -> 'e gvalue)

(** Two values for booleans. *)
let ptrue  = VTagged (KId "True", [])
let pfalse = VTagged (KId "False", [])

(**
    We often need to check that a value has a specific shape.
    To that end, we introduce the following coercions. A
    coercion of type [('a, 'e)] coercion tries to convert an
    Hopix value into a OCaml value of type ['a]. If this conversion
    fails, it returns [None].
*)

type ('a, 'e) coercion = 'e gvalue -> 'a option
let fail = None
let ret x = Some x
let value_as_int      = function VInt x -> ret x | _ -> fail
let value_as_char     = function VChar c -> ret c | _ -> fail
let value_as_string   = function VString s -> ret s | _ -> fail
let value_as_tagged   = function VTagged (k, vs) -> ret (k, vs) | _ -> fail
let value_as_record   = function VRecord fs -> ret fs | _ -> fail
let value_as_location = function VLocation l -> ret l | _ -> fail
let value_as_closure  = function VClosure (e, p, b) -> ret (e, p, b) | _ -> fail
let value_as_primitive = function VPrimitive (p, f) -> ret (p, f) | _ -> fail
let value_as_bool = function
  | VTagged (KId "True", []) -> true
  | VTagged (KId "False", []) -> false
  | _ -> assert false
  

(**
   It is also very common to have to inject an OCaml value into
   the types of Hopix values. That is the purpose of a wrapper.
 *)
type ('a, 'e) wrapper = 'a -> 'e gvalue
let int_as_value x  = VInt x
let bool_as_value b = if b then ptrue else pfalse

(**

  The flap toplevel needs to print the result of evaluations. This is
   especially useful for debugging and testing purpose. Do not modify
   the code of this function since it is used by the testsuite.

*)
let print_value m v =
  (** To avoid to print large (or infinite) values, we stop at depth 5. *)
  let max_depth = 5 in

  let rec print_value d v =
    if d >= max_depth then "..." else
      match v with
        | VInt x ->
          Mint.to_string x
        | VChar c ->
          "'" ^ Char.escaped c ^ "'"
        | VString s ->
          "\"" ^ String.escaped s ^ "\""
        | VUnit ->
          "()"
        | VLocation a ->
          print_array_value d (Memory.dereference m a)
        | VTagged (KId k, []) ->
          k
        | VTagged (KId k, vs) ->
          k ^ print_tuple d vs
        | VTuple (vs) ->
           print_tuple d vs
        | VRecord fs ->
           "{"
           ^ String.concat ", " (
                 List.map (fun (LId f, v) -> f ^ " = " ^ print_value (d + 1) v
           ) fs) ^ "}"
        | VClosure _ ->
          "<fun>"
        | VPrimitive (s, _) ->
          Printf.sprintf "<primitive: %s>" s
    and print_tuple d vs =
      "(" ^ String.concat ", " (List.map (print_value (d + 1)) vs) ^ ")"
    and print_array_value d block =
      let r = Memory.read block in
      let n = Mint.to_int (Memory.size block) in
      "[ " ^ String.concat ", " (
                 List.(map (fun i -> print_value (d + 1) (r (Mint.of_int i)))
                         (ExtStd.List.range 0 (n - 1))
               )) ^ " ]"
  in
  print_value 0 v

let print_values m vs =
  String.concat "; " (List.map (print_value m) vs)

module Environment : sig
  (** Evaluation environments map identifiers to values. *)
  type t

  (** The empty environment. *)
  val empty : t

  (** [bind env x v] extends [env] with a binding from [x] to [v]. *)
  val bind    : t -> identifier -> t gvalue -> t

  (** [update pos x env v] modifies the binding of [x] in [env] so
      that [x ↦ v] ∈ [env]. *)
  val update  : Position.t -> identifier -> t -> t gvalue -> unit

  (** [lookup pos x env] returns [v] such that [x ↦ v] ∈ env. *)
  val lookup  : Position.t -> identifier -> t -> t gvalue

  (** [UnboundIdentifier (x, pos)] is raised when [update] or
      [lookup] assume that there is a binding for [x] in [env],
      where there is no such binding. *)
  exception UnboundIdentifier of identifier * Position.t

  (** [last env] returns the latest binding in [env] if it exists. *)
  val last    : t -> (identifier * t gvalue * t) option

  (** [print env] returns a human readable representation of [env]. *)
  val print   : t gvalue Memory.t -> t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)

  exception UnboundIdentifier of identifier * Position.t

  let lookup' pos x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier (x, pos))
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux

  let lookup pos x e = !(lookup' pos x e)

  let update pos x e v =
    lookup' pos x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty -> None

  let print_binding m (Id x, v) =
    x ^ " = " ^ print_value m !v

  let print m e =
    let b = Buffer.create 13 in
    let push x v = Buffer.add_string b (print_binding m (x, v)) in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, EEmpty) -> push x v; aux EEmpty
      | EBind (x, v, e) -> push x v; Buffer.add_string b "\n"; aux e
    in
    aux e

end

(**
    We have everything we need now to define [value] as an instantiation
    of ['e gvalue] with ['e = Environment.t], as promised.
*)
type value = Environment.t gvalue

(**
   The following higher-order function lifts a function [f] of type
   ['a -> 'b] as a [name]d Hopix primitive function, that is, an
   OCaml function of type [value -> value].
*)
let primitive name ?(error = fun () -> assert false) coercion wrapper f
: value
= VPrimitive (name, fun x ->
    match coercion x with
      | None -> error ()
      | Some x -> wrapper (f x)
  )

type runtime = {
  memory      : value Memory.t;
  environment : Environment.t;
}

type observable = {
  new_memory      : value Memory.t;
  new_environment : Environment.t;
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives =
  let intbin name out op =
    let error m v =
      Printf.eprintf
        "Invalid arguments for `%s': %s\n"
        name (print_value m v);
      assert false (* By typing. *)
    in
    VPrimitive (name, fun m -> function
      | VInt x ->
         VPrimitive (name, fun m -> function
         | VInt y -> out (op x y)
         | v -> error m v)
      | v -> error m v)
  in
  let bind_all what l x =
    List.fold_left (fun env (x, v) -> Environment.bind env (Id x) (what x v))
      x l
  in
  (* Define arithmetic binary operators. *)
  let binarith name =
    intbin name (fun x -> VInt x) in
  let binarithops = Mint.(
    [ ("`+`", add); ("`-`", sub); ("`*`", mul); ("`/`", div) ]
  ) in
  (* Define arithmetic comparison operators. *)
  let cmparith name = intbin name bool_as_value in
  let cmparithops =
    [ ("`=?`", ( = ));
      ("`<?`", ( < ));
      ("`>?`", ( > ));
      ("`>=?`", ( >= ));
      ("`<=?`", ( <= )) ]
  in
  let boolbin name out op =
    VPrimitive (name, fun _ x -> VPrimitive (name, fun _ y ->
        out (op (value_as_bool x) (value_as_bool y))))
  in
  let boolarith name = boolbin name (fun x -> if x then ptrue else pfalse) in
  let boolarithops =
    [ ("`||`", ( || )); ("`&&`", ( && )) ]
  in
  let generic_printer =
    VPrimitive ("print", fun m v ->
      output_string stdout (print_value m v);
      flush stdout;
      VUnit
    )
  in
  let print s =
    output_string stdout s;
    flush stdout;
    VUnit
  in
  let print_int =
    VPrimitive  ("print_int", fun _ -> function
      | VInt x -> print (Mint.to_string x)
      | _ -> assert false (* By typing. *)
    )
  in
  let print_string =
    VPrimitive  ("print_string", fun _ -> function
      | VString x -> print x
      | _ -> assert false (* By typing. *)
    )
  in
  let bind' x w env = Environment.bind env (Id x) w in
  Environment.empty
  |> bind_all binarith binarithops
  |> bind_all cmparith cmparithops
  |> bind_all boolarith boolarithops
  |> bind' "print"        generic_printer
  |> bind' "print_int"    print_int
  |> bind' "print_string" print_string
  |> bind' "true"         ptrue
  |> bind' "false"        pfalse
  |> bind' "nothing"      VUnit

let initial_runtime () = {
  memory      = Memory.create (640 * 1024 (* should be enough. -- B.Gates *));
  environment = primitives;
}

let rec evaluate runtime ast =
  try
    let runtime' = List.fold_left definition runtime ast in
    (runtime', extract_observable runtime runtime')
  with Environment.UnboundIdentifier (Id x, pos) ->
    Error.error "interpretation" pos (Printf.sprintf "`%s' is unbound." x)


and definition runtime d = 
  match Position.value d with
  | DefineValue value -> definition_de_valeur runtime value
  | _ -> runtime

and definition_de_valeur runtime = function
  | SimpleValue (id, _, expr) -> simple_value runtime id expr
  | RecFunctions functions -> fonction_recursive runtime functions

(** définit une valeur simple dans l'environnement
    - évalue l'expression dans le contexte actuel (environnement + mémoire)
    - Lie l'identifiant à la valeur obtenue
    - Retourne un nouveau runtime avec l'environnement étendu 
*)
and simple_value runtime id expr =
  let v = expression (Position.position expr) runtime.environment runtime.memory (Position.value expr) in
  { runtime with environment = Environment.bind runtime.environment (Position.value id) v }

(** définit des fonctions récursives mutuelles
    
    Étape 1 : construction de l'environnement initial
    - parcourt toutes les fonctions du groupe
    - pour chaque fonction, crée une closure temporaire
    - ces closures capturent l'environnement AVANT l'ajout des fonctions
    - ajoute toutes ces closures à l'environnement

    Étape 2 : mise à jour pour la récursion
    - parcourt à nouveau toutes les fonctions
    - remplace chaque closure par une nouvelle version
    - les nouvelles closures capturent l'environnement AVEC toutes les fonctions
    - grâce à l'utilisation de références dans Environment, la mise à jour
      est visible par toutes les closures
*)
and fonction_recursive runtime functions =
  (* Étape 1 *)
  let new_env = List.fold_left (fun env (id, _, def) ->
    match def with
    | FunctionDefinition (pattern, body) -> Environment.bind env (Position.value id) (VClosure (runtime.environment, pattern, body))
    | _ -> Error.error "interpretation" (Position.position id) "definition de fonction incorrecte"
  ) runtime.environment functions
  in
  (* Étape 2 *)
  List.iter (fun (id, _, def) ->
    match def with
    | FunctionDefinition (pattern, body) -> Environment.update (Position.position id) (Position.value id) new_env  (VClosure (new_env, pattern, body))
    | _ -> ()
  ) functions;
  { runtime with environment = new_env }

(** [expression' environment memory e] evaluates the expression [e]
    into a value [v] if

                          E, M ⊢ e ⇓ v, M'

   and E = [environment], M = [memory].

and expression' environment memory e =
  expression (position e) environment memory (value e)*)

(** évaluer une expression *)
and evaluer_expression env mem expr_loc =
  expression (Position.position expr_loc) env mem (Position.value expr_loc)

(** évaluer une liste expression *)
and evaluer_liste_expressions env mem exprs =
  List.map (evaluer_expression env mem) exprs

and expression pos env mem = function
  | Literal lit -> evaluer_litteral lit
  | Variable (x, _) -> evaluer_variable pos x env
  | Tuple exprs -> evaluer_tuple exprs env mem
  | Tagged (constr, _, exprs) -> evaluer_constructeur constr exprs env mem
  | Record (champs, _) -> evaluer_record champs env mem
  | Field (expr_record, etiquette, _) -> evaluer_acces_champ expr_record etiquette env mem
  | Define (def_valeur, expr) -> evaluer_definition_locale pos def_valeur expr env mem
  | Fun def_fonc -> evaluer_fonction def_fonc env
  | Apply (expr_f, expr_arg) -> evaluer_application pos expr_f expr_arg env mem
  | IfThenElse (cond, alors, sinon) -> evaluer_conditionnelle cond alors sinon env mem
  | Sequence exprs -> evaluer_sequence exprs env mem
  | While (cond, corps) -> evaluer_boucle_while cond corps env mem
  | For (id, debut, fin, corps) -> evaluer_boucle_for id debut fin corps env mem
  | Case (expr, branches) -> evaluer_filtrage pos expr branches env mem
  | Ref expr -> evaluer_allocation expr env mem
  | Assign (gauche, droite) -> evaluer_affectation pos gauche droite env mem
  | Read expr -> evaluer_dereferencement pos expr env mem
  | _ -> Error.error "interpretation" pos "expression pas reconnue"

(** règle E-INT, E-CHAR, E-STRING *)
and evaluer_litteral lit =
  match Position.value lit with
  | LInt x -> VInt x
  | LChar c -> VChar c
  | LString s -> VString s

(** évalue une variable en cherchant sa valeur dans l'environnement | Règle E-VAR *)
and evaluer_variable _pos x env =
  Environment.lookup (Position.position x) (Position.value x) env

(** évalue un tuple d'expressions | Règle E-TUPLE
    - évalue chaque expression du tuple
    - construit une VTuple avec les valeurs obtenues *)
and evaluer_tuple exprs env mem =
  VTuple (evaluer_liste_expressions env mem exprs)

(** évalue un constructeur tagué avec ses arguments | Règle E-CONSTRUCTOR
    - évalue tous les arguments du constructeur
    - crée une valeur VTagged avec le constructeur et les valeurs *)
and evaluer_constructeur constr exprs env mem =
  let valeurs = evaluer_liste_expressions env mem exprs in
  VTagged (Position.value constr, valeurs)

(** Règle E-RECORD    
    - pour chaque champ, évalue son expression
    - associe le champ à sa valeur
    - construit un VRecord avec tous les champs *)
and evaluer_record champs env mem =
  let evaluer_un_champ (etiquette, expr) =  (Position.value etiquette, evaluer_expression env mem expr) in 
  VRecord (List.map evaluer_un_champ champs)

(** évalue l'accès à un champ d'un record | Règle E-FIELD
    - évalue l'expression du record
    - vérifie que c'est bien un record
    - recherche le champ demandé
    - retourne la valeur associée *)
and evaluer_acces_champ expr_record etiquette env mem =
  let valeur_record = evaluer_expression env mem expr_record in
  match valeur_record with
  | VRecord champs -> List.assoc (Position.value etiquette) champs
  | _ -> Error.error "interpretation" (Position.position expr_record) "pas un record"

(** évalue une définition locale | Règle E-LOCALDEFINITION
    - crée un runtime temporaire avec l'environnement et la mémoire actuels
    - évalue la définition dans l'ancienne environnement
    - évalue l'expression dans le nouvel environnement
    - retourne la valeur *)
and evaluer_definition_locale pos def_valeur expr env mem =
  let runtime = definition { environment = env; memory = mem }  (Position.with_pos pos (DefineValue def_valeur)) in
  expression pos runtime.environment runtime.memory (Position.value expr)

(** évalue une fonction, création de closure  *)
and evaluer_fonction def_fonc env =
  match def_fonc with
  | FunctionDefinition (motif, corps) -> VClosure (env, motif, corps)

(** évalue une application de fonction | Règle E-APPLICATION
    - évalue la fonction 
    - évalue l'argument
    - si c'est une closure :
       - lie le motif des paramètres à la valeur de l'argument
       - évalue le corps dans le nouvel environnement
    - si c'est une primitive, applique directement la fonction d'OCaml *)
and evaluer_application pos expr_f expr_arg env mem =
  let valeur_fonction = evaluer_expression env mem expr_f in
  let valeur_argument = evaluer_expression env mem expr_arg in
  match valeur_fonction with
  | VClosure (env_closure, motif, corps) ->
      let nouvel_env = lier_motif (Position.position motif) env_closure motif valeur_argument in
      evaluer_expression nouvel_env mem corps
  | VPrimitive (_, f) -> f mem valeur_argument
  | _ -> Error.error "interpretation" (Position.position expr_f) "pas une fonction"

(** évalue une expression conditionnelle | Règles E-IF-TRUE et E-IF-FALSE
    - évalue la condition
    - Convertit en booléen
    - Si vrai, évalue la branche 'alors'
    - Sinon, évalue la branche 'sinon' *)
and evaluer_conditionnelle cond alors sinon env mem =
  let valeur_cond = evaluer_expression env mem cond in
  if value_as_bool valeur_cond then
    evaluer_expression env mem alors
  else
    evaluer_expression env mem sinon

(** lie un motif à une valeur dans l'environnement
    Correspond à : σ ⊢ v ∼ m ⇝ σ' *)
and lier_motif pos env motif valeur =
  match (Position.value motif, valeur) with
  | PVariable id, v -> Environment.bind env (Position.value id) v
  | PWildcard, _ -> env
  | PTypeAnnotation (p, _), v -> lier_motif (Position.position p) env p v
  | PLiteral lit, v -> verifier_litteral_egal pos lit v env
  | PTaggedValue (constr, _, motifs), VTagged (constr', valeurs) ->  lier_motif_constructeur pos constr motifs constr' valeurs env
  | PTuple motifs, VTuple valeurs -> lier_motif_tuple pos motifs valeurs env
  | PRecord (champs, _), VRecord champs_valeur -> lier_motif_record pos champs champs_valeur env
  | POr motifs, v -> lier_motif_disjonctif pos motifs v env
  | PAnd motifs, v -> lier_motif_conjonctif motifs v env
  | _ -> Error.error "interpretation" pos "pattern: incompatibilité de pattern"

(** vérifie qu'un littéral dans un motif correspond à une valeur *)
and verifier_litteral_egal pos lit valeur env =
  let valeur_lit = evaluer_litteral lit in
  if valeur_lit = valeur then env
  else Error.error "interpretation" pos "pattern: la valeur ne correspond pas au literal"

(** vérifie que :
    - Les constructeurs correspondent
    - Le nombre d'arguments est identique
    - Lie récursivement chaque sous-motif à la valeur correspondante *)
and lier_motif_constructeur pos constr motifs constr' valeurs env =
  if Position.value constr = constr' && List.length motifs = List.length valeurs then
    List.fold_left2 (fun env' m v -> lier_motif (Position.position m) env' m v) env motifs valeurs
  else
    Error.error "interpretation" pos "pattern: le constructeur ne correspond pas"

(** vérifie que :
    - Le nombre d'éléments correspond
    - Lie chaque élément du tuple *)
and lier_motif_tuple pos motifs valeurs env =
  if List.length motifs = List.length valeurs then
    List.fold_left2 (fun env' m v -> lier_motif (Position.position m) env' m v) env motifs valeurs
  else
    Error.error "interpretation" pos "pattern: le tuple ne correspond pas"

(** pour chaque champ du motif :
    - Recherche le champ dans le record
    - Lie le motif du champ à la valeur trouvée *)
and lier_motif_record pos champs champs_valeur env =
  List.fold_left (fun env' (etiquette, motif) ->
    try
      let valeur = List.assoc (Position.value etiquette) champs_valeur in
      lier_motif (Position.position motif) env' motif valeur
    with Not_found -> Error.error "interpretation" pos "pattern: champ manquant dans le record"
  ) env champs

(** lie un motif disjonctif (p1 | p2 | ...)
    - vérifie si le motif correspond à la valeur
    - Si oui, lie ce motif et termine
    - Sinon, essaie le motif suivant
    - Erreur si aucun motif ne correspond *)
and lier_motif_disjonctif pos motifs valeur env =
  let rec essayer_motifs = function
    | [] -> Error.error "interpretation" pos "pattern: aucun pattern dans le OR ne correspond"
    | m :: reste ->
        if motif_correspond (Position.position m) (Position.value m) valeur then
          lier_motif (Position.position m) env m valeur
        else
          essayer_motifs reste
  in
  essayer_motifs motifs

(** lie un motif conjonctif (p1 & p2 & ...)    
    - chaque motif lie ses variables dans l'environnement
    - tous les motifs doivent correspondre à la même valeur *)
and lier_motif_conjonctif motifs valeur env =
  List.fold_left (fun env' m -> lier_motif (Position.position m) env' m valeur) env motifs

(** évalue une séquence d'expressions (e1; e2; ...; en) | Règle E-SEQUENCE
    - si la liste est vide : retourne VUnit
    - si un seul élément : évalue et retourne sa valeur
    - sinon : évalue la première expression puis évalue le reste de la séquence *)
and evaluer_sequence exprs env mem =
  match exprs with
  | [] -> VUnit
  | [expr] -> evaluer_expression env mem expr
  | expr :: reste ->
      let _ = evaluer_expression env mem expr in
      evaluer_sequence reste env mem

(** évalue une boucle while | Règle E-WHILE
    - évalue la condition
    - Si la condition est vraie :
       - évalue le corps de la boucle
       - Recommence depuis le début
    - Si la condition est fausse : retourne VUnit *)
and evaluer_boucle_while cond corps env mem =
  let valeur_cond = evaluer_expression env mem cond in
  if value_as_bool valeur_cond then begin
    let _ = evaluer_expression env mem corps in
    evaluer_boucle_while cond corps env mem
  end else
    VUnit

(** évalue une boucle for | Règle E-FOR-LOOP , E-FOR-END
    - évalue l'expression de début 
    - évalue l'expression de fin 
    - vérifie que les deux valeurs sont des entiers
    - délègue à boucler_for pour l'exécution de la boucle *)
and evaluer_boucle_for id expr_debut expr_fin corps env mem =
  let valeur_debut = evaluer_expression env mem expr_debut in
  let valeur_fin = evaluer_expression env mem expr_fin in
  match (valeur_debut, valeur_fin) with
  | VInt debut, VInt fin -> boucler_for id debut fin corps env mem
  | _ -> Error.error "interpretation" (Position.position expr_debut)  "for: les bornes doivent être des entiers"

(** exécution de la boucle for    
    - vérifie si compteur > fin : si oui, termine avec VUnit
    - sinon :
       - lie la variable d'itération à la valeur du compteur
       - évalue le corps de la boucle dans ce nouvel environnement
       - incrémente le compteur et continue  *)
and boucler_for id compteur fin corps env mem =
  if Mint.(compteur > fin) then VUnit
  else begin
    let env_boucle = Environment.bind env (Position.value id) (VInt compteur) in
    let _ = evaluer_expression env_boucle mem corps in
    boucler_for id (Mint.add compteur Mint.one) fin corps env mem
  end

(** évalue un filtrage | Règle E-MATCH 
    - évalue l'expression à filtrer
    - on envoie analyse des branches à evaluer_branches *)
and evaluer_filtrage pos expr branches env mem =
  let valeur = evaluer_expression env mem expr in
  evaluer_branches pos valeur branches env mem

(** évalue les branches d'un filtrage
    - si aucune branche : erreur 
    - sinon : essaie la première branche
       - si elle correspond : lie le motif et évalue l'expression
       - sinon : essaie la branches suivante *)
and evaluer_branches pos valeur branches env mem =
  match branches with
  | [] -> Error.error "interpretation" pos "case: aucune branche ne correspond"
  | branche :: reste ->
      essayer_une_branche pos valeur branche reste env mem

(** essaie de faire correspondre une branche
    - extrait le motif et l'expression de la branche
    - vérifie si le motif correspond à la valeur
    - si oui :
       - lie le motif à la valeur 
       - évalue l'expression dans ce nouvel environnement
    - Si non : essaie les branches suivantes *)
and essayer_une_branche pos valeur branche reste env mem =
  let Branch (motif, expr) = Position.value branche in
  if motif_correspond (Position.position motif) (Position.value motif) valeur then
    let nouvel_env = lier_motif (Position.position motif) env motif valeur in
    evaluer_expression nouvel_env mem expr
  else
    evaluer_branches pos valeur reste env mem

(** vérifie si un motif correspond à une valeur *)
and motif_correspond pos motif valeur =
  match (motif, valeur) with
  | PVariable _, _ -> true
  | PWildcard, _ -> true
  | PLiteral lit, _ ->
      let valeur_lit = evaluer_litteral lit in
      valeur_lit = valeur
  | PTaggedValue (constr, _, motifs), VTagged (constr', valeurs) -> motif_constructeur_correspond constr motifs constr' valeurs
  | PTuple motifs, VTuple valeurs -> motif_tuple_correspond motifs valeurs
  | PRecord (champs, _), VRecord champs_valeur -> motif_record_correspond champs champs_valeur
  | PTypeAnnotation (m, _), v -> motif_correspond (Position.position m) (Position.value m) v
  | POr motifs, v -> List.exists (fun m -> motif_correspond (Position.position m) (Position.value m) v) motifs
  | PAnd motifs, v -> List.for_all (fun m -> motif_correspond (Position.position m) (Position.value m) v) motifs
  | _ -> false

(** vérifie un motif de constructeur
    - les constructeurs doivent être identiques
    - le nombre d'arguments doit correspondre
    - chaque sous-motif doit correspondre à la valeur correspondante *)
and motif_constructeur_correspond constr motifs constr' valeurs =
  Position.value constr = constr' && 
  List.length motifs = List.length valeurs &&
  List.for_all2 (fun m v -> motif_correspond (Position.position m) (Position.value m) v) motifs valeurs

(** vérifie la correspondance d'un motif de tuple
    - le nombre d'éléments doit correspondre
    - chaque sous-motif doit correspondre à l'élément correspondant *)
and motif_tuple_correspond motifs valeurs =
  List.length motifs = List.length valeurs &&
  List.for_all2 (fun m v -> motif_correspond (Position.position m) (Position.value m) v) motifs valeurs

(** vérifie la correspondance d'un motif de record
    - recherche le champ dans la valeur
    - vérifie que le motif du champ correspond à la valeur trouvée
    - tous les champs du motif doivent correspondre *)
and motif_record_correspond champs champs_valeur =
  List.for_all (fun (etiquette, motif) ->
    try
      let valeur = List.assoc (Position.value etiquette) champs_valeur in
      motif_correspond (Position.position motif) (Position.value motif) valeur
    with Not_found -> false
  ) champs

(** évalue l'allocation d'une référence | Règle E-ALLOCATE
    - évalue l'expression à allouer
    - Alloue un bloc dans la mémoire
    - Initialise le bloc avec la valeur
    - Retourne une VLocation pointant vers ce bloc *)
and evaluer_allocation expr env mem =
  let valeur = evaluer_expression env mem expr in
  let emplacement = Memory.allocate mem Mint.one valeur in
  VLocation emplacement

(** évalue une affectation | Règle E-ASSIGNMENT
    - évalue l'expression de gauche 
    - évalue l'expression de droite 
    - vérifie que la gauche est bien une VLocation
    - Déréférence la location pour obtenir le bloc mémoire
    - Écrit la nouvelle valeur 
    - Retourne VUnit *)
and evaluer_affectation pos gauche droite env mem =
  let valeur_gauche = evaluer_expression env mem gauche in
  let valeur_droite = evaluer_expression env mem droite in
  match valeur_gauche with
  | VLocation emplacement ->
      let bloc = Memory.dereference mem emplacement in
      Memory.write bloc Mint.zero valeur_droite;
      VUnit
  | _ -> Error.error "interpretation" pos "assign: le membre gauche doit être une référence"

(** évalue un déréférencement | Règle E-DEREFERENCE
    - évalue l'expression 
    - vérifie que c'est bien une VLocation
    - Déréférence la location pour obtenir le bloc
    - Lit la valeur
    - Retourne cette valeur *)
and evaluer_dereferencement pos expr env mem =
  let valeur = evaluer_expression env mem expr in
  match valeur with
  | VLocation emplacement ->
      let bloc = Memory.dereference mem emplacement in
      Memory.read bloc Mint.zero
  | _ -> Error.error "interpretation" pos "read: l'expression doit être une référence"

(** This function returns the difference between two runtimes. *)
and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.empty runtime.environment runtime'.environment;
    new_memory =
      runtime'.memory
  }

(** This function displays a difference between two runtimes. *)
let print_observable (_ : runtime) observation =
  Environment.print observation.new_memory observation.new_environment
