{ (* -*- tuareg -*- *)
  open Lexing
  open Error
  open Position
  open HopixParser

  (* aller a la prochaine ligne *)
  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  (* gestion de erreurs  *)
  let error lexbuf =
    error "lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

  (* parser un char literal
    - si le char commence par \, on la decode
    - sinon on retourne le caractere tel quel
  *)
  let parse_char_literal s =
    let content = String.sub s 1 (String.length s - 2) in
    if String.length content > 1 && content.[0] = '\\' then
      match content.[1] with
      | 'n' -> '\n'
      | 't' -> '\t'
      | 'b' -> '\b'
      | 'r' -> '\r'
      | '\\' -> '\\'
      | '\'' -> '\''
      | '"' -> '"'
      | '0' when String.length content = 5 && (content.[2] = 'x' || content.[2] = 'X') ->
          int_of_string ("0x" ^ String.sub content 3 2) |> char_of_int
      | ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9') when String.length content = 4 ->
          int_of_string (String.sub content 1 3) |> char_of_int
      | _ -> content.[1]
    else
      content.[0]


  (* gestion des sequences d'echappement dans les string *)
  let handle_escape_sequence c =
    match c with
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | '\\' -> '\\'
    | '\'' -> '\''
    | '"' -> '"'
    | _ -> c

}


let newline = ('\010' | '\013' | "\013\010")
let blank   = [' ' '\009' '\012']
let digit = ['0'-'9']
let vlt = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let constr_id = ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let type_variable = '`' vlt+
let hexa = ['0'-'9' 'a'-'f' 'A'-'F']
let int = '-'? digit+ | "0x"hexa+ | "0b"['0'-'1']+ | "0o"['0'-'7']+
let printable = [' '-'~']
let special_char = '\\' ['n' 't' 'b' 'r' '\\' '\'' '"']
let nombre_special = '\\' ['0'-'1'] digit digit | "\\2" (['0'-'4'] digit | '5' ['0'-'5']) | "\\0x"hexa hexa
let atom = nombre_special  | [' '-'~'] # ['\'' '\\' '"'] | special_char
let char = '\'' atom '\''
let string = '"' (atom | '\'' | "\\'")* '"'

(* Comments *)
rule comment = parse
  | "*}"          { () }
  | "{*"          { comment lexbuf ; comment lexbuf }
  | newline       { next_line_and comment lexbuf }
  | eof           { error lexbuf "unterminated comment." }
  | _             { comment lexbuf }

and token = parse
  (** Layout *)
  | newline           { next_line_and token lexbuf }
  | blank+            { token lexbuf               }
  | "{*"              { comment lexbuf; token lexbuf }
  | "##" [^'\n''\r']* { token lexbuf } (* pour les commentaire *)
  | eof               { EOF       }

  | "let"           { LET       }
  | "for"           { FOR       }
  | "match"         { MATCH     }
  | "while"         { WHILE     }
  | "do"            { DO        }
  | "if"            { IF        }
  | "then"          { THEN      }
  | "else"          { ELSE      }
  | "fun"           { FUN       }
  | "from"          { FROM      }
  | "to"            { TO        }
  | "until"         { UNTIL     }
  | "ref"           { REF       }
  | "type"          { TYPE      }
  | "extern"        { EXTERN    }
  | "and"           { AND       }

  | vlt             { ID (lexeme lexbuf) }
  | constr_id       { KID (lexeme lexbuf) }
  | type_variable   { TID (lexeme lexbuf) }
  (* on verifie que le int n'est pas trop grand *)
  | int             { 
      try 
        INT (int_of_string (lexeme lexbuf))
      with Failure _ ->
        error lexbuf "Integer literal too large."
    }
  | '"'              { string_literal "" lexbuf }
  | char            { CHAR (parse_char_literal (lexeme lexbuf)) }

  | ":="            { ASSIGN    }
  | "->"            { RARROW    }
  | "&&"            { AND_LOG   }    
  | "||"            { OR_LOG    }
  | "=?"            { EQ        }
  | "<=?"           { LEQ       }
  | ">=?"           { GEQ       }
  | "<?"            { LE        }
  | ">?"            { GE        }

  | ":"             { COLON     }
  | "!"             { EXCLAMATION }
  | "("             { LPAREN  }
  | ")"             { RPAREN  }
  | "["             { LSQUARE   }
  | "]"             { RSQUARE   }
  | "{"             { LBRACE    }
  | "}"             { RBRACE    }
  | ";"             { POINT_VIRGULE }
  | "="             { EQUAL     }
  | "|"             { BAR       }
  | ","             { COMMA     }
  | ">"             { GT        }
  | "<"             { LT        }
  | "\\"            { BSLASH    }
  | "."             { POINT     }
  | "+"             { PLUS      }
  | "-"             { MOINS     }
  | "*"             { STAR      }
  | "/"             { DIV       }
  | "_"             { UNDERSCORE }
  | "&"             { AMP       }

  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }

(* gestion des string, des code hexadécimaux et des \ *)
and string_literal acc = parse
  | '"'                { STRING ("\"" ^ acc ^ "\"") }
  | "\\0x" (hexa hexa as hex_digits)
      { 
        let code = int_of_string ("0x" ^ hex_digits) in
        string_literal (acc ^ String.make 1 (char_of_int code)) lexbuf
      }
  | '\\' (['0'-'2'] digit digit as dec_digits)
      { 
        let code = int_of_string dec_digits in
        string_literal (acc ^ String.make 1 (char_of_int code)) lexbuf
      }
  | '\\' ((_ as c))    { string_literal (acc ^ String.make 1 (handle_escape_sequence c)) lexbuf }
  | eof               { error lexbuf "Unterminated string." }
  | _ as c            { string_literal (acc ^ String.make 1 c) lexbuf }

