%{
  open Syntax
%}

%token PLUSOP MULTOP EVALTO
%token PLUS MULT IS
%token LPAREN RPAREN

%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| n1=INTV PLUS n2=INTV IS n3=INTV { PlusExp (n1, n2, n3) }
| n1=INTV MULT n2=INTV IS n3=INTV { MultExp (n1, n2, n3) }
| e=Expr EVALTO n=INTV { EvalExp (e, n) }

Expr :
| e=PExpr { e }

PExpr :
| e1=PExpr PLUSOP e2=MExpr { Plus (e1, e2) }
| e=MExpr { e }

MExpr :
| e1=MExpr MULTOP e2=AExpr { Mult (e1, e2) }
| e=AExpr { e }

AExpr :
| n=INTV { Nat n }
| LPAREN e=Expr RPAREN { e }
