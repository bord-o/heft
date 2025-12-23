%{
open Ast
%}

%token <string> LIDENT UIDENT TYVAR
%token TYPE WHERE OF DEF FUN THEOREM FN LET IN IF THEN ELSE FORALL
%token LPAREN RPAREN BAR COMMA COLON COLONEQUAL DARROW ARROW
%token EOF EQUALS

%type <Ast.toplevel list> file
%type <Ast.toplevel> toplevel
%type <Ast.typ> typ app_typ base_typ arg_typ
%type <string list> type_params
%type <Ast.constructor list> constructors
%type <Ast.constructor> constructor bar_constructor
%type <Ast.equation list> equations
%type <Ast.equation> equation bar_equation
%type <Ast.pattern> pattern atomic_pattern
%type <Ast.term> term app_term atomic_term

%start file

%right ARROW

%%

file:
  | defs=list(toplevel) EOF { defs }

toplevel:
  | TYPE params=type_params name=LIDENT WHERE ctors=constructors
      { TypeDef { name; params; constructors = ctors } }
  | DEF name=LIDENT COLON ty=typ COLONEQUAL body=term
      { Def { name; typ = ty; body } }
  | FUN name=LIDENT COLON ty=typ WHERE eqs=equations
      { Fun { name; typ = ty; equations = eqs } }
  | THEOREM name=LIDENT COLON stmt=term
      { Theorem { name; statement = stmt } }

type_params:
  | (* empty *) { [] }
  | params=nonempty_list(TYVAR) { params }

(* Types: adjacency for application, -> for functions *)
typ:
  | t=app_typ ARROW rest=typ { TyArr (t, rest) }
  | t=app_typ { t }

app_typ:
  | t=base_typ { t }
  | args=nonempty_list(arg_typ) name=LIDENT { TyCon (name, args) }

base_typ:
  | tv=TYVAR { TyVar tv }
  | name=LIDENT { TyCon (name, []) }
  | LPAREN t=typ RPAREN { t }

arg_typ:
  | tv=TYVAR { TyVar tv }
  | LPAREN t=typ RPAREN { t }

(* Type constructors *)
constructors:
  | (* empty *) { [] }
  | ctors=nonempty_list(bar_constructor) { ctors }

bar_constructor:
  | BAR c=constructor { c }

constructor:
  | name=UIDENT { (name, []) }
  | name=UIDENT OF args=nonempty_list(atomic_typ) { (name, args) }

atomic_typ:
  | tv=TYVAR { TyVar tv }
  | name=LIDENT { TyCon (name, []) }
  | LPAREN t=typ RPAREN { t }

(* Function equations *)
equations:
  | eqs=nonempty_list(bar_equation) { eqs }

bar_equation:
  | BAR eq=equation { eq }

equation:
  | name=LIDENT pats=list(pattern) DARROW body=term
      { (name, pats, body) }

(* Patterns *)
pattern:
  | v=LIDENT { PVar v }
  | c=UIDENT { PCon (c, []) }
  | c=UIDENT args=nonempty_list(atomic_pattern) { PCon (c, args) }
  | LPAREN p=pattern RPAREN { p }

atomic_pattern:
  | v=LIDENT { PVar v }
  | c=UIDENT { PCon (c, []) }
  | LPAREN p=pattern RPAREN { p }

(* Terms *)
term:
  | FN params=nonempty_list(LIDENT) DARROW body=term
      { List.fold_right (fun p b -> Lam (p, b)) params body }
  | LET v=LIDENT COLONEQUAL e=term IN body=term
      { Let (v, e, body) }
  | IF cond=term THEN t=term ELSE e=term
      { If (cond, t, e) }
  | FORALL vars=nonempty_list(LIDENT) COMMA body=term
      { List.fold_right (fun v b -> Forall (v, b)) vars body }
  | t=app_term { t }

app_term:
  | t=atomic_term { t }
  | f=app_term arg=atomic_term { App (f, arg) }

atomic_term:
  | v=LIDENT { Var v }
  | c=UIDENT { Con c }
  | LPAREN t=term RPAREN { t }
  | LPAREN t=term COLON ty=typ RPAREN { Ann (t, ty) }
