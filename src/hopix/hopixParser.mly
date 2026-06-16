%{ (* -*- tuareg -*- *)

  open HopixAST
  open Position

%}

%token EOF
%token<string> ID KID TID
%token<int> INT
%token<char> CHAR
%token<string> STRING 
%token LET FOR MATCH WHILE DO IF THEN ELSE FUN FROM TO UNTIL REF TYPE EXTERN AND
%token ASSIGN COLON EXCLAMATION LPAREN RPAREN LSQUARE RSQUARE LBRACE RBRACE POINT_VIRGULE EQUAL BAR COMMA GT LT BSLASH RARROW POINT PLUS MOINS STAR DIV AND_LOG OR_LOG EQ LEQ GEQ LE GE UNDERSCORE AMP

%right RARROW
%right POINT_VIRGULE
%nonassoc FUN  
%nonassoc ASSIGN
%left OR_LOG
%left AND_LOG
%left EQ LEQ GEQ LE GE
%left PLUS MOINS
%left STAR DIV
%left POINT
%nonassoc REF EXCLAMATION
%left AMP
%left BAR
%left COLON
%nonassoc NOARGS
%left LPAREN

%start<HopixAST.t> program

%%

(*
Une séquence entre crochets est optionnelle, comme `[ ref ]`.
Une séquence entre accolades se répète zéro fois ou plus, comme `( arg { , arg } )`.

p ::= { definition }                          Programme

definition ::= 
             | type type_con [ < type_variable { , type_variable } > ] [ = tdefinition ]   Définition de type
             | extern var_id : type_scheme                                                Valeurs externes
             | vdefinition                                                                Définition de valeur(s)

tdefinition ::= 
              | [ | ] constr_id [ ( type { , type } ) ]  { | constr_id [ ( type { , type } ) ] }         Type somme
              | { label_id : type { , label_id : type } }       Type produit étiqueté

vdefinition ::= 
              | let var_id [ : type_scheme ] = expr              Valeur simple
              | fun fundef { and fundef }                        Fonction(s)

fundef ::= [ : type_scheme ] var_id pattern = expr           

type ::= 
       | type_con [ < type { , type } > ]                        Application d’un constructeur de type
       | type -> type                                            Fonctions
       | type * type { * type }                                  N-uplets (N > 1)
       | type_variable                                           Variables de type
       | ( type )                                                Type entre parenthèses

type_scheme ::= [ [ type_variable { , type_variable } ] ] type

type ::= type_con [ < type { , type } > ]                        Application d’un constructeur de type
       | type -> type                                            Fonctions
       | type * type { * type }                                  N-uplets (N > 1)
       | type_variable                                           Variables de type
       | ( type )                                                Type entre parenthèses

type_scheme ::= [ [ type_variable { , type_variable } ] ] type

expr ::=
       | int                                                Entier positif
       | char                                               Caractère
       | string                                             Chaîne de caractères
       | var_id [ < [ type { , type } ] > ]                 Variable
       | constr_id [ < [ type { , type } ] > ] [ ( expr { , expr } ) ]  Construction d’une donnée
       | ( )                                                Construction d’un 0-uplet
       | ( expr , expr { , expr } )                         Construction d’un n-uplet (n > 1)
       | { label_id = expr { , label_id = expr } } [ < [ type { , type } ] > ]  Enregistrement
       | expr . label_id [ < [ type { , type } ] > ]        Projection d’un champ
       | expr ; expr                                        Séquencement
       | vdefinition ; expr                                 Définition locale
       | \ pattern -> expr                                  Fonction anonyme
       | expr expr                                          Application
       | expr binop expr                                    Application infixe
       | match ( expr ) { branches }                        Analyse de motifs
       | if ( expr ) then { expr } [ else { expr } ]        Conditionnelle
       | ref expr                                           Allocation
       | expr := expr                                       Affectation
       | ! expr                                             Lecture
       | while ( expr ) { expr }                            Boucle non bornée
       | do { expr } until ( expr )                         Boucle non bornée et non vide
       | for var_id from ( expr ) to ( expr ) { expr }      Boucle bornée
       | ( expr )                                           Parenthésage
       | ( expr : type )                                    Annotation de type

binop ::= + | - | * | / | && | || | =? | <=? | >=? | <? | >?      Opérateurs binaires
branches ::= [ | ] branch { | branch }                            Liste de cas
branch ::= pattern -> expr                                        Cas d’analyse

pattern ::=
          | var_id                                                Motif universel liant
          | _                                                     Motif universel non liant
          | ( [ pattern { , pattern } ] )                         N-uplets ou parenthésage
          | pattern : type                                        Annotation de type
          | int                                                   Entier
          | char                                                  Caractère
          | string                                                Chaîne de caractères
          | constr_id [ < [ type { , type } ] > ] [ ( pattern { , pattern } ) ]  Valeurs étiquetées
          | { label_id = pattern { , label_id = pattern } } [ < [ type { , type } ] > ]  Enregistrement
          | pattern | pattern                                     Disjonction
          | pattern & pattern                                     Conjonction

*)

program: defs=list(located(definition)) EOF { defs }

definition:
    | TYPE tc=located(type_constructor) type_vars=definition_de_type_variable type_def=definition_de_type_egalite
        { DefineType (tc, type_vars, type_def) } 
    | EXTERN var_id=located(identifier) COLON ts=located(type_scheme)
        { DeclareExtern (var_id, ts) }
    | vdef=vdefinition { DefineValue vdef }

// pour definition
definition_de_type_variable:
    | LT tvars=separated_nonempty_list(COMMA,located(tid)) GT  { tvars }
    | /* vide */                                               { [] }

// pour definition
definition_de_type_egalite:
    | EQUAL tdef=tdefinition    { tdef }
    | /* vide */                { Abstract }

type_scheme:
    | LSQUARE tvars=separated_nonempty_list(COMMA,located(tid)) RSQUARE t=located(_type) { ForallTy (tvars, t) }
    | t=located(_type)                                                                   { ForallTy ([], t) }

%inline vdefinition:
  | LET var_id=located(identifier) ts=definition_de_type_scheme EQUAL e=located(expr) { SimpleValue (var_id, ts, e) }
  | FUN funs=separated_nonempty_list(AND, fundef)                                     { RecFunctions funs }


fundef:
    | ts=definition_de_type_scheme fun_id=located(identifier) p=located(pattern) EQUAL e=located(expr) %prec FUN
        { (fun_id, ts, FunctionDefinition (p, e)) }


// pour vdefinition et fundef
definition_de_type_scheme:
    | COLON ts=located(type_scheme) { Some ts }
    | /* vide */                    { None }
  
_type:
    | t1=located(_type) RARROW t2=located(_type) { TyArrow (t1, t2) }
    | t=tuple_type                               { t }

tuple_type:
    | types=separated_nonempty_list(STAR,located(atomic_type)) { 
        (* n-uplet ou type simple *)
        match types with 
        | [t] -> t.value
        | _ -> TyTuple types 
    }

atomic_type:
    | tc=located(type_constructor)                                                   { TyCon (tc.value, []) }
    | tc=type_constructor LT types=separated_nonempty_list(COMMA,located(_type)) GT  { TyCon (tc, types) }
    | tv=tid                                                                         { TyVar tv }
    | LPAREN t=_type RPAREN                                                          { t }

pattern:
    | var_id=located(identifier)    { PVariable var_id }
    | UNDERSCORE                    { PWildcard }
    | LPAREN patterns=separated_list(COMMA,located(pattern)) RPAREN { 
        (* n-uplet ou parenthésage *)
        match patterns with
        | [p] -> p.value 
        | _ -> PTuple patterns 
      }
    | p=located(pattern) COLON t=located(_type) { PTypeAnnotation (p, t) }
    | lit=located(literal_int) { PLiteral lit }
    | lit=located(literal_char) { PLiteral lit }
    | lit=located(literal_string) { PLiteral lit }
    | constr_id=located(constructor) type_args=construction_donnee_type pattern_args=construction_de_valeur_etiquetee
{ PTaggedValue (constr_id, type_args, pattern_args) }
    | LBRACE labels=separated_nonempty_list(COMMA,equal_label_pattern) RBRACE type_args=construction_donnee_type
        { PRecord (labels, type_args) }
    | p1=located(pattern) BAR p2=located(pattern) { POr (p1::p2::[]) }
    | p1=located(pattern) AMP p2=located(pattern) { PAnd (p1::p2::[]) }

equal_label_pattern:
    | label=located(label) EQUAL pattern=located(pattern) { (label, pattern) }

construction_de_valeur_etiquetee:
    | /* vide */ { [] }
    | LPAREN patterns=separated_nonempty_list(COMMA,located(simple_pattern)) RPAREN { patterns }

simple_pattern:
    | var_id=located(identifier) { PVariable var_id }
    | UNDERSCORE                 { PWildcard }
    | LPAREN patterns=separated_list(COMMA,located(pattern)) RPAREN { PTuple patterns }
    | lit=located(literal_int) { PLiteral lit }
    | lit=located(literal_char) { PLiteral lit }
    | lit=located(literal_string) { PLiteral lit }
    | constr_id=located(constructor) type_args=construction_donnee_type pattern_args=construction_de_valeur_etiquetee
        { PTaggedValue (constr_id, type_args, pattern_args) }
    | LBRACE labels=separated_nonempty_list(COMMA,equal_label_pattern) RBRACE type_args=construction_donnee_type
        { PRecord (labels, type_args) }

branch:
    | p=located(pattern) RARROW e=located(expr) { Branch (p, e) }

branches:
    | BAR first_branch=located(branch) other_branches=autre_branches { first_branch :: other_branches }
    | first_branch=located(branch) other_branches=autre_branches     { first_branch :: other_branches }

autre_branches:
    | /* vide */ { [] }
    | BAR other_branches=separated_nonempty_list(BAR,located(branch)) { other_branches }

tdefinition:
    | BAR constr_id=located(constructor) type_args=definition_de_construction_donnee_type other_constrs=autre_type_somme
        { DefineSumType ((constr_id, type_args) :: other_constrs) }
    | constr_id=located(constructor) type_args=definition_de_construction_donnee_type other_constrs=autre_type_somme
        { DefineSumType ((constr_id, type_args) :: other_constrs) }
    | LBRACE labels=separated_nonempty_list(COMMA, type_produit) RBRACE
        { DefineRecordType labels }

autre_type_somme:
    | /* vide */ { [] }
    | BAR other_constrs=separated_nonempty_list(BAR,type_somme) { other_constrs }

type_somme:
    | c=located(constructor) type_args=definition_de_construction_donnee_type { (c, type_args) } 

type_produit:
    | label=located(label) COLON t=located(_type) { (label, t) }

definition_de_construction_donnee_type:
    | LPAREN types=separated_nonempty_list(COMMA,located(_type)) RPAREN { types }
    | /* vide */ { [] }

expr:
    | s=simple_expr { s }
    | e1=located(expr) POINT_VIRGULE e2=located(expr) { Sequence ([e1; e2])}
    | vdef=vdefinition POINT_VIRGULE e=located(expr) { Define (vdef, e) }
    | e1=located(simple_expr) ASSIGN e2=located(expr) { Assign (e1, e2) }
    | e1=located(expr) b=located(binop) e2=located(expr) { 
         let op_var = Position.with_poss $startpos $endpos (Variable (b, None)) in
        Apply (Position.with_poss $startpos $endpos (Apply (op_var, e1)), e2)
    }
    | i = ifthenelse { i }
    | MATCH LPAREN e=located(expr) RPAREN LBRACE b=branches RBRACE { Case (e, b) }
    | WHILE LPAREN e_cond=located(expr) RPAREN LBRACE e_body=located(expr) RBRACE { While (e_cond, e_body) }
    | DO LBRACE e_body=located(expr) RBRACE UNTIL LPAREN e_cond=located(expr) RPAREN { 
        let v = While(e_cond,e_body) in 
        let v_loc= Position.with_poss $startpos $endpos v in 
        Sequence(e_body::v_loc::[]) 
        }
    | FOR var_id=located(identifier) FROM LPAREN e_from=located(expr) RPAREN TO LPAREN e_to=located(expr) RPAREN LBRACE e_body=located(expr) RBRACE
        { For (var_id, e_from, e_to, e_body) }
    | BSLASH p=located(pattern) RARROW e=located(expr) { Fun(FunctionDefinition (p, e)) }
    
simple_expr:
    | a=located(simple_expr) b=located(very_simple_expr) { Apply (a, b) }
    | e=very_simple_expr { e }

very_simple_expr:
    | lit=located(literal_int) { Literal lit }
    | lit=located(literal_char) { Literal lit }
    | lit=located(literal_string) { Literal lit }
    | var_id=located(identifier) { Variable (var_id, None) }
    | var_id=located(identifier) LT GT { Variable (var_id, Some []) }
    | var_id=located(identifier) LT types=separated_nonempty_list(COMMA,located(_type)) GT { Variable (var_id, Some types) }
    | constr_id=located(constructor) type_args=construction_donnee_type args=construction_donnee_expr
        { Tagged (constr_id, type_args, args) }
    | LPAREN RPAREN { Tuple [] }
    | LPAREN first_expr=located(expr) COMMA other_exprs=separated_nonempty_list(COMMA,located(expr)) RPAREN
        { Tuple (first_expr :: other_exprs) }
    | LBRACE fields=separated_nonempty_list(COMMA, equal_label_expression) RBRACE type_args=construction_donnee_type
        { Record (fields, type_args) }
    | LPAREN e=expr RPAREN { e }
    | LPAREN e=located(expr) COLON t=located(_type) RPAREN { TypeAnnotation (e, t) }
    | EXCLAMATION e=located(very_simple_expr) { Read e }
    | REF e=located(very_simple_expr) { Ref e }
    | e=located(very_simple_expr) POINT label=located(label) type_args=construction_donnee_type { Field (e, label, type_args) }

ifthenelse :
    | IF LPAREN i=located(expr) RPAREN THEN LBRACE e=located(expr) RBRACE ELSE LBRACE e2=located(expr) RBRACE
        { IfThenElse(i,e, e2) }
    | IF LPAREN i=located(expr) RPAREN THEN LBRACE e=located(expr) RBRACE
        { IfThenElse(i,e, e) }

equal_label_expression:
    | label=located(label) EQUAL expr=located(expr) { (label, expr) }

construction_donnee_type:
    | LT types=separated_list(COMMA,located(_type)) GT { Some types }
    | /* vide */ { None }

construction_donnee_expr:
    | LPAREN exprs=separated_nonempty_list(COMMA,located(expr)) RPAREN  { exprs }
    | /* vide */ %prec NOARGS { [] }

%inline binop:
    | PLUS    { Id("`+`") }
    | MOINS   { Id("`-`") }
    | STAR    { Id("`*`") }
    | DIV     { Id("`/`") }
    | AND_LOG { Id("`&&`") }
    | OR_LOG  { Id("`||`") }
    | EQ      { Id("`=?`") }
    | LEQ     { Id("`<=?`") }
    | GEQ     { Id("`>=?`") }
    | LE      { Id("`<?`") }
    | GE      { Id("`>?`") }



// regles de base pour les identifiants
identifier: id=ID       { Id (id)  }
type_constructor: id=ID { TCon (id)  }  
tid: tid=TID { TId (tid) }
constructor: kid=KID    { KId (kid)  }
label: id=ID            { LId (id) }

// regles de base pour les littéraux
literal_int: n=INT       { LInt (Mint.of_int n) }
literal_char: c=CHAR     { LChar c }
literal_string: s=STRING { 
  let content = String.sub s 1 (String.length s - 2) in
  LString content 
}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
