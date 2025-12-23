
%{
open Ast
%}

%token <string> LIDENT UIDENT TYVAR
%token TYPE WHERE DEF FUN THEOREM FN LET IN IF THEN ELSE FORALL
%token LPAREN RPAREN BAR COMMA COLON COLONEQUAL DARROW ARROW
%token EOF EQUALS OF

%type <Ast.toplevel list> file
%type <Ast.toplevel> toplevel
%type <Ast.typ> typ atomic_typ
%type <string list> type_params
%type <Ast.constructor list> constructors
%type <Ast.constructor> constructor bar_constructor
%type <Ast.equation list> equations
%type <Ast.equation> equation bar_equation
%type <Ast.pattern> pattern atomic_pattern
%type <Ast.term> term app_term atomic_term

(* Types for Menhir's built-in list functions *)
%type <Ast.toplevel list> list(toplevel)
%type <Ast.pattern list> list(pattern)
%type <string list> nonempty_list(LIDENT)
%type <string list> nonempty_list(TYVAR)
%type <Ast.pattern list> nonempty_list(atomic_pattern)
%type <Ast.typ list> nonempty_list(atomic_typ)
%type <Ast.constructor list> nonempty_list(bar_constructor)
%type <Ast.equation list> nonempty_list(bar_equation)
%type <Ast.typ list> separated_nonempty_list(COMMA,typ)

%start file

%%


file:
  | toplevels = list(toplevel) EOF { toplevels }

toplevel:
  | TYPE typarams = type_params name = LIDENT WHERE ctors = constructors 
      { TypeDef { name; params = typarams; constructors = ctors } }
  | DEF name = LIDENT COLON ty = typ COLONEQUAL body = term
      { Def { name; typ = ty; body } }
  | FUN name = LIDENT COLON ty = typ WHERE eqs = equations 
      { Fun { name; typ = ty; equations = eqs } }
  | THEOREM name = LIDENT COLON stmt = term
      { Theorem { name; statement = stmt } }

type_params:
  | (* empty *) { [] }
  | tvs = nonempty_list(TYVAR) { tvs }

typ:
  | tv = TYVAR 
      { TyVar tv }
  | name = LIDENT 
      { TyCon (name, []) }
  | arg = atomic_typ name = LIDENT
      { TyCon (name, [arg]) }
  | LPAREN t1 = typ COMMA t2 = typ RPAREN name = LIDENT
      { TyCon (name, [t1; t2]) }
  | LPAREN t1 = typ COMMA t2 = typ COMMA rest = separated_nonempty_list(COMMA, typ) RPAREN name = LIDENT
      { TyCon (name, t1 :: t2 :: rest) }
  | t1 = atomic_typ ARROW t2 = typ
      { TyArr (t1, t2) }
  | LPAREN t = typ RPAREN
      { t }

constructors:
  | (* empty *) { [] }
  | ctors = nonempty_list(bar_constructor) { ctors }

bar_constructor:
  | BAR c = constructor { c }

constructor:
  | name = UIDENT 
      { (name, []) }
  | name = UIDENT OF args = nonempty_list(atomic_typ)
      { (name, args) }

atomic_typ:
  | tv = TYVAR { TyVar tv }
  | name = LIDENT { TyCon (name, []) }
  | LPAREN t = typ RPAREN { t }

equations:
  | eqs = nonempty_list(bar_equation) { eqs }

bar_equation:
  | BAR e = equation { e }

equation:
  | name = LIDENT pats = list(pattern) DARROW body = term
      { (name, pats, body) }

pattern:
  | v = LIDENT
      { PVar v }
  | c = UIDENT
      { PCon (c, []) }
  | c = UIDENT args = nonempty_list(atomic_pattern)
      { PCon (c, args) }
  | LPAREN p = pattern RPAREN
      { p }

atomic_pattern:
  | v = LIDENT { PVar v }
  | c = UIDENT { PCon (c, []) }
  | LPAREN p = pattern RPAREN { p }

term:
  | FN params = nonempty_list(LIDENT) DARROW body = term
      { List.fold_right (fun p acc -> Lam (p, acc)) params body }
  | LET v = LIDENT COLONEQUAL e = term IN body = term
      { Let (v, e, body) }
  | IF cond = term THEN t = term ELSE e = term
      { If (cond, t, e) }
  | FORALL vars = nonempty_list(LIDENT) COMMA body = term
      { List.fold_right (fun v acc -> Forall (v, acc)) vars body }
  | app = app_term
      { app }

app_term:
  | t = atomic_term { t }
  | f = app_term arg = atomic_term { App (f, arg) }

atomic_term:
  | v = LIDENT { Var v }
  | c = UIDENT { Con c }
  | LPAREN t = term RPAREN { t }
  | LPAREN t = term COLON ty = typ RPAREN { Ann (t, ty) }
