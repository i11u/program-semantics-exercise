%{
open Syntax
%}

%token EVALTO IF THEN ELSE TRUE FALSE
%token PLUS MULT MINUS LT
%token LPAREN RPAREN
%token ERROR

%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| e=Expr EVALTO i=INTV { EvalExp (e, ILit i) }
| e=Expr EVALTO TRUE { EvalExp (e, BLit true) }
| e=Expr EVALTO FALSE { EvalExp (e, BLit false) }
| e=Expr EVALTO ERROR { EvalExp (e, Error) }

Expr :
| e=LTExpr { e }

LTExpr :
| l=LTExpr LT r=PMExpr { BinOp (Lt, l, r) }
| e=PMExpr { e }

PMExpr :
| l=PMExpr PLUS r=MExpr { BinOp (Plus, l, r) }
| l=PMExpr MINUS r=MExpr { BinOp (Minus, l, r) }
| e=MExpr { e }

MExpr :
| l=MExpr MULT r=AExpr { BinOp (Mult, l, r) }
| e=AExpr { e }

AExpr :
| i=INTV { ILit i }
| TRUE { BLit true }
| FALSE { BLit false }
| LPAREN e=Expr RPAREN { e }
| IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }