(** This module implements a compiler from Hobix to Fopix. *)

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)

module Source = Hobix
module S = Source.AST
module Target = Fopix
module T = Target.AST

(**

   The translation from Hobix to Fopix turns anonymous
   lambda-abstractions into toplevel functions and applications into
   function calls. In other words, it translates a high-level language
   (like OCaml) into a first order language (like C).

   To do so, we follow the closure conversion technique.

   The idea is to make explicit the construction of closures, which
   represent functions as first-class objects. A closure is a block
   that contains a code pointer to a toplevel function [f] followed by all
   the values needed to execute the body of [f]. For instance, consider
   the following OCaml code:

   let f =
     let x = 6 * 7 in
     let z = x + 1 in
     fun y -> x + y * z

   The values needed to execute the function "fun y -> x + y * z" are
   its free variables "x" and "z". The same program with explicit usage
   of closure can be written like this:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]

   (in an imaginary OCaml in which arrays are untyped.)

   Once closures are explicited, there are no more anonymous functions!

   But, wait, how to we call such a function? Let us see that on an
   example:

   let f = ... (* As in the previous example *)
   let u = f 0

   The application "f 0" must be turned into an expression in which
   "f" is a closure and the call to "f" is replaced to a call to "g"
   with the proper arguments. The argument "y" of "g" is known from
   the application: it is "0". Now, where is "env"? Easy! It is the
   closure itself! We get:

   let g y env = env[1] + y * env[2]
   let f =
      let x = 6 * 7 in
      let z = x + 1 in
      [| g; x; z |]
   let u = f[0] 0 f

   (Remark: Did you notice that this form of "auto-application" is
   very similar to the way "this" is defined in object-oriented
   programming languages?)

*)

(**
   Helpers functions.
*)

let error pos msg =
  Error.error "compilation" pos msg

let make_fresh_variable =
  let r = ref 0 in
  fun () -> incr r; T.Id (Printf.sprintf "_%d" !r)


let make_fresh_function_identifier =
  let r = ref 0 in
  fun () -> incr r; T.FunId (Printf.sprintf "_%d" !r)

let define e f =
  let x = make_fresh_variable () in
  T.Define (x, e, f x)

let rec defines ds e =
  match ds with
    | [] ->
      e
    | (x, d) :: ds ->
      T.Define (x, d, defines ds e)

let seq a b =
  define a (fun _ -> b)

let rec seqs = function
  | [] -> assert false
  | [x] -> x
  | x :: xs -> seq x (seqs xs)

let allocate_block e =
  T.(FunCall (FunId "allocate_block", [e]))

let write_block e i v =
  T.(FunCall (FunId "write_block", [e; i; v]))

let read_block e i =
  T.(FunCall (FunId "read_block", [e; i]))

let lint i =
  T.(Literal (LInt (Int64.of_int i)))

(** Fonctions auxiliaires pour gérer les primitives *)
let builtin_arity (S.Id x) : int option =
  (* Retourne l'arité d'une primitive si elle existe *)
  match x with
  | "allocate_block" -> Some 1
  | "read_block" -> Some 2
  | "write_block" -> Some 3
  | "equal_string" -> Some 2
  | "equal_char" -> Some 2
  | "observe_int" -> Some 1
  | "print_int" -> Some 1
  | "print_string" -> Some 1
  | "`+`" | "`-`" | "`*`" | "`/`" -> Some 2
  | "`<?`" | "`>?`" | "`<=?`" | "`>=?`" | "`=?`" -> Some 2
  | "`&&`" | "`||`" -> Some 2
  | _ -> None

let is_builtin id =
  (* Vérifie si un identifiant est une primitive *)
  builtin_arity id <> None

(** [free_variables e] returns the list of free variables that
     occur in [e].*)
let free_variables =
  let module M =
    Set.Make (struct type t = S.identifier let compare = compare end)
  in
  let rec unions f = function
    | [] -> M.empty
    | [s] -> f s
    | s :: xs -> M.union (f s) (unions f xs)
  in
  let rec fvs = function
    | S.Literal _ ->
       M.empty
    | S.Variable x ->
       M.singleton x
    | S.While (condition, corps) ->
       unions fvs [condition; corps]
    | S.Define (definition_valeur, suite) ->
       let variables_definies = match definition_valeur with
         | S.SimpleValue (nom_var, _) -> M.singleton nom_var
         | S.RecFunctions liste_fonctions -> 
             M.of_list (List.map (fun (nom_fonction, _) -> nom_fonction) liste_fonctions)
       in
       let variables_libres_def = match definition_valeur with
         | S.SimpleValue (_, expression) -> fvs expression
         | S.RecFunctions liste_fonctions ->
             unions (function
               | (_, S.Fun (parametres, corps)) ->
                   M.diff (fvs corps) (M.of_list parametres)
               | _ -> assert false
             ) liste_fonctions
       in
       
       M.union (M.diff variables_libres_def variables_definies) 
               (M.diff (fvs suite) variables_definies)
    | S.ReadBlock (a, b) ->
       unions fvs [a; b]
    | S.Apply (a, b) ->
       unions fvs (a :: b)
    | S.WriteBlock (a, b, c) | S.IfThenElse (a, b, c) ->
       unions fvs [a; b; c]
    | S.AllocateBlock a ->
       fvs a
    | S.Fun (parametres, corps) ->
       M.diff (fvs corps) (M.of_list parametres)
    | S.Switch (a, b, c) ->
       let c = match c with None -> [] | Some c -> [c] in
       unions fvs (a :: ExtStd.Array.present_to_list b @ c)
  in
  fun e -> M.elements (fvs e)

(**

    A closure compilation environment relates an identifier to the way
    it is accessed in the compiled version of the function's
    body.

    Indeed, consider the following example. Imagine that the following
    function is to be compiled:

    fun x -> x + y

    In that case, the closure compilation environment will contain:

    x -> x
    y -> "the code that extract the value of y from the closure environment"

    Indeed, "x" is a local variable that can be accessed directly in
    the compiled version of this function's body whereas "y" is a free
    variable whose value must be retrieved from the closure's
    environment.

*)
type environment = {
    vars : (HobixAST.identifier, FopixAST.expression) Dict.t;
    externals : (HobixAST.identifier, int) Dict.t;
}

let initial_environment () =
  { vars = Dict.empty; externals = Dict.empty }

let bind_external id n env =
  { env with externals = Dict.insert id n env.externals }

let is_external id env =
  Dict.lookup id env.externals <> None

let reset_vars env =
   { env with vars = Dict.empty }

(** Precondition: [is_external id env = true]. *)
let arity_of_external id env =
  match Dict.lookup id env.externals with
    | Some n -> n
    | None -> assert false (* By is_external. *)

(** Transforme une fonction en fermeture *)
let valeur_fonction_to_fermeture arite fonction_cible =
  (* Crée une fermeture pour une fonction externe ou primitive *)
  let id_fonction = make_fresh_function_identifier () in
  let parametres = List.init arite (fun _ -> make_fresh_variable ()) in
  let param_env = make_fresh_variable () in
  let corps =
    T.FunCall (fonction_cible, List.map (fun x -> T.Variable x) parametres)
  in
  let definition_fonction = T.DefineFunction (id_fonction, parametres @ [param_env], corps) in
  let expression_fermeture =
    define (allocate_block (lint 1)) (fun fermeture ->
      seq (write_block (T.Variable fermeture) (lint 0) (T.Literal (T.LFun id_fonction)))
        (T.Variable fermeture)
    )
  in
  ([definition_fonction], expression_fermeture)


(** [translate p env] turns an Hobix program [p] into a Fopix program
    using [env] to retrieve contextual information. *)
let translate (p : S.t) env =
  let rec program env defs =
    let env, defs = ExtStd.List.foldmap definition env defs in
    (List.flatten defs, env)
  and definition env = function
    | S.DeclareExtern (id, n) ->
       let env = bind_external id n env in
       (env, [T.ExternalFunction (function_identifier id, n)])
    | S.DefineValue vd ->
       (env, value_definition env vd)
  and value_definition env = function
    | S.SimpleValue (x, e) ->
       let fs, e = expression (reset_vars env) e in
       fs @ [T.DefineValue (identifier x, e)]
    | S.RecFunctions fdefs ->
       let fs, defs = define_recursive_functions fdefs in
       fs @ List.map (fun (x, e) -> T.DefineValue (x, e)) defs

  and define_recursive_functions definitions_recursives =
    let noms_fonctions = List.map (function
      | (nom, S.Fun (_, _)) -> nom
      | _ -> assert false
    ) definitions_recursives in
    (* Créer les fonctions toplevel avec leurs fermetures *)
    let rec creer_fermetures acc = function
      | [] -> acc
      | (nom_fonction, S.Fun (parametres, corps)) :: reste ->
          (* Calculer les variables libres de cette fonction *)
          let variables_libres =
            free_variables (S.Fun (parametres, corps))
            |> List.filter (fun v -> not (is_external v env || is_builtin v))
          in
          let vars_libres_non_rec = List.filter (fun v -> not (List.mem v noms_fonctions)) variables_libres in
          let id_fonction = function_identifier nom_fonction in
          let param_env = make_fresh_variable () in
          let env_corps = List.fold_left (fun acc x -> 
            { acc with vars = Dict.insert x (T.Variable (identifier x)) acc.vars }
          ) env parametres in      
          (* Variables libres extraites de la fermeture *)
          let env_corps = List.fold_left (fun acc_env (position, var_libre) ->
            let acces = read_block (T.Variable param_env) (lint (position + 1)) in
            { acc_env with vars = Dict.insert var_libre acces acc_env.vars }
          ) env_corps (List.mapi (fun i v -> (i, v)) vars_libres_non_rec) in
          (* Ajouter les fonctions récursives dans l'environnement *)
          let env_corps = List.fold_left (fun acc_env (position, nom_rec) ->
            let offset = 1 + List.length vars_libres_non_rec in
            let acces = read_block (T.Variable param_env) (lint (offset + position)) in
            { acc_env with vars = Dict.insert nom_rec acces acc_env.vars }
          ) env_corps (List.mapi (fun i f -> (i, f)) noms_fonctions) in
          (* Compiler le corps de la fonction *)
          let definitions_fonction, expression_corps = expression env_corps corps in
          let tous_parametres = List.map identifier parametres @ [param_env] in
          let def_fonction = T.DefineFunction (id_fonction, tous_parametres, expression_corps) in
          creer_fermetures (definitions_fonction @ [def_fonction] @ acc) reste
      | _ -> assert false
    in
    let definitions_fonctions = creer_fermetures [] definitions_recursives in
    (* Créer les fermetures pour chaque fonction *)
    let liaisons_fermetures = List.map (function
      | (nom_fonction, S.Fun (parametres, corps)) ->
      let variables_libres =
        free_variables (S.Fun (parametres, corps))
        |> List.filter (fun v -> not (is_external v env || is_builtin v))
      in
      let vars_libres_non_rec = List.filter (fun v -> not (List.mem v noms_fonctions)) variables_libres in
      let id_fonction = function_identifier nom_fonction in
      let taille_fermeture = 1 + List.length vars_libres_non_rec + List.length noms_fonctions in
      
      let x = identifier nom_fonction in
      let creer_fermeture =
        define (allocate_block (lint taille_fermeture)) (fun fermeture ->
          let ecritures = [
            (* Écrire le pointeur de code *)
            write_block (T.Variable fermeture) (lint 0) (T.Literal (T.LFun id_fonction))
          ] @ 
          (* Écrire les variables libres *)
          List.mapi (fun i var_libre ->
            write_block (T.Variable fermeture) (lint (i + 1)) (T.Variable (identifier var_libre))
          ) vars_libres_non_rec in
          seqs (ecritures @ [T.Variable fermeture])
        )
      in
      (x, creer_fermeture)
      | _ -> assert false
    ) definitions_recursives in
    let mises_a_jour_fermetures = List.flatten (List.mapi (fun _ -> function
      | (nom_fonction, S.Fun (parametres, corps)) ->
      let variables_libres =
        free_variables (S.Fun (parametres, corps))
        |> List.filter (fun v -> not (is_external v env || is_builtin v))
      in
      let vars_libres_non_rec = List.filter (fun v -> not (List.mem v noms_fonctions)) variables_libres in
      let offset = 1 + List.length vars_libres_non_rec in
      List.mapi (fun i nom_rec ->
        write_block (T.Variable (identifier nom_fonction)) 
                   (lint (offset + i)) 
                   (T.Variable (identifier nom_rec))
      ) noms_fonctions
      | _ -> assert false
    ) definitions_recursives) in

    let toutes_definitions = List.map (function
      | (nom_fonction, S.Fun _) ->
      (identifier nom_fonction, 
       defines liaisons_fermetures 
               (seqs (mises_a_jour_fermetures @ [T.Variable (identifier nom_fonction)])))
      | _ -> assert false
    ) definitions_recursives in
    (definitions_fonctions, toutes_definitions)
  and expression env = function
    | S.Literal l ->
      [], T.Literal (literal l)
    | S.While (cond, e) ->
       let cfs, cond = expression env cond in
       let efs, e = expression env e in
       cfs @ efs, T.While (cond, e)
    | S.Variable x ->
       (match Dict.lookup x env.vars with
        | Some expression_acces ->
            ([], expression_acces)
        | None ->
            (* Variable non locale: externe ou primitive *)
            if is_external x env then
              valeur_fonction_to_fermeture (arity_of_external x env) (function_identifier x)
            else
              match builtin_arity x with
              | Some arite -> 
                  valeur_fonction_to_fermeture arite (function_identifier x)
              | None -> 
                  ([], T.Variable (identifier x))
       )

    | S.Define (definition_valeur, suite) ->
      (match definition_valeur with
       | S.SimpleValue (nom_variable, expression_valeur) ->
           let defs_expr, expr_compilee = expression env expression_valeur in
           let defs_suite, suite_compilee = expression env suite in
           defs_expr @ defs_suite, T.Define (identifier nom_variable, expr_compilee, suite_compilee)
       | S.RecFunctions definitions_recursives ->
           let defs_fonctions, liaisons = define_recursive_functions definitions_recursives in
           let nouvel_env = List.fold_left2 (fun acc_env (nom_fonction, _) (id_variable, _) ->
             { acc_env with vars = Dict.insert nom_fonction (T.Variable id_variable) acc_env.vars }
           ) env definitions_recursives liaisons in
           let defs_suite, suite_compilee = expression nouvel_env suite in
           defs_fonctions @ defs_suite, defines liaisons suite_compilee)

    | S.Apply (fonction, arguments) ->
      let defs_args, args_compiles = expressions env arguments in
      (match fonction with
        | S.Variable x when is_external x env || is_builtin x ->
            (* Application d'une fonction externe ou primitive *)
            let arite =
              if is_external x env then arity_of_external x env
              else match builtin_arity x with Some n -> n | None -> assert false
            in
            
            if List.length arguments = arite then
              defs_args, T.FunCall (function_identifier x, args_compiles)
            else
              (* créer une fermeture *)
              let id_fonction = make_fresh_function_identifier () in
              let params_restants =
                List.init (arite - List.length arguments) (fun _ -> make_fresh_variable ())
              in
              let param_env = make_fresh_variable () in
              let args_captures =
                List.mapi (fun i _ -> read_block (T.Variable param_env) (lint (i + 1))) args_compiles
              in
              let tous_args = args_captures @ List.map (fun p -> T.Variable p) params_restants in
              let def_fonction = T.DefineFunction (
                id_fonction,
                params_restants @ [param_env],
                T.FunCall (function_identifier x, tous_args)
              ) in
              
              let taille_fermeture = 1 + List.length args_compiles in
              defs_args @ [def_fonction],
              define (allocate_block (lint taille_fermeture)) (fun fermeture ->
                let ecritures = [
                  write_block (T.Variable fermeture) (lint 0) (T.Literal (T.LFun id_fonction))
                ] @ List.mapi (fun i arg ->
                  write_block (T.Variable fermeture) (lint (i + 1)) arg
                ) args_compiles in
                seqs (ecritures @ [T.Variable fermeture])
              )
        | _ ->
            (* Application d'une fonction anonyme *)
            let defs_fonction, fonction_compilee = expression env fonction in
            defs_fonction @ defs_args,
            define fonction_compilee (fun fermeture ->
              let pointeur_code = read_block (T.Variable fermeture) (lint 0) in
              T.UnknownFunCall (pointeur_code, args_compiles @ [T.Variable fermeture])
            ))
    | S.IfThenElse (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs, T.IfThenElse (a, b, c)

    | S.Fun (parametres, corps) ->
      let variables_libres =
        free_variables (S.Fun (parametres, corps))
        |> List.filter (fun v -> not (is_external v env || is_builtin v))
      in
      let id_fonction = make_fresh_function_identifier () in
      let param_env = make_fresh_variable () in
      let env_corps = List.fold_left (fun acc param ->
        { acc with vars = Dict.insert param (T.Variable (identifier param)) acc.vars }
      ) env parametres in
      let env_corps = List.fold_left (fun acc (position, var_libre) ->
        let acces = read_block (T.Variable param_env) (lint (position + 1)) in
        { acc with vars = Dict.insert var_libre acces acc.vars }
      ) env_corps (List.mapi (fun i v -> (i, v)) variables_libres) in
      
      (*Compiler le corps de la fonction *)
      let defs_fonction, expression_corps = expression env_corps corps in
      let tous_parametres = List.map identifier parametres @ [param_env] in
      let def_fonction = T.DefineFunction (id_fonction, tous_parametres, expression_corps) in
      
      (* Créer la fermeture *)
      let taille_fermeture = 1 + List.length variables_libres in
      defs_fonction @ [def_fonction],
      define (allocate_block (lint taille_fermeture)) (fun fermeture ->
        let ecritures = [
          (* Écrire le pointeur de code *)
          write_block (T.Variable fermeture) (lint 0) (T.Literal (T.LFun id_fonction))
        ] @ List.mapi (fun i var_libre ->
          (* Écrire chaque variable libre *)
          let expr_var_libre = match Dict.lookup var_libre env.vars with
            | Some e -> e
            | None -> T.Variable (identifier var_libre)
          in
          write_block (T.Variable fermeture) (lint (i + 1)) expr_var_libre
        ) variables_libres in
        seqs (ecritures @ [T.Variable fermeture])
      )
    | S.AllocateBlock a ->
      let afs, a = expression env a in
      (afs, allocate_block a)
    | S.WriteBlock (a, b, c) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      let cfs, c = expression env c in
      afs @ bfs @ cfs,
      T.FunCall (T.FunId "write_block", [a; b; c])
    | S.ReadBlock (a, b) ->
      let afs, a = expression env a in
      let bfs, b = expression env b in
      afs @ bfs,
      T.FunCall (T.FunId "read_block", [a; b])
    | S.Switch (a, bs, default) ->
      let afs, a = expression env a in
      let bsfs, bs =
        ExtStd.List.foldmap (fun bs t ->
                    match ExtStd.Option.map (expression env) t with
                    | None -> (bs, None)
                    | Some (bs', t') -> (bs @ bs', Some t')
                  ) [] (Array.to_list bs)
      in
      let dfs, default = match default with
        | None -> [], None
        | Some e -> let bs, e = expression env e in bs, Some e
      in
      afs @ bsfs @ dfs,
      T.Switch (a, Array.of_list bs, default)


  and expressions env = function
    | [] ->
       [], []
    | e :: es ->
       let efs, es = expressions env es in
       let fs, e = expression env e in
       fs @ efs, e :: es

  and literal = function
    | S.LInt x -> T.LInt x
    | S.LString s -> T.LString s
    | S.LChar c -> T.LChar c

  and identifier (S.Id x) = T.Id x

  and function_identifier (S.Id x) = T.FunId x

  in
  program env p