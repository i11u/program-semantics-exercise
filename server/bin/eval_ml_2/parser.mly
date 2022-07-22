%{
open Syntax
%}

%token EVALTO IF THEN ELSE TRUE FALSE
%token PLUS MULT MINUS LT
%token PLUSC MULTC MINUSC LTC IS
%token LET EQ IN COMMA
%token LPAREN RPAREN
%token TURNSTILE

%token <Syntax.id> ID
%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| v=VarList TURNSTILE e=Expr EVALTO i=INTV { EvalExp (v, e, IntV i) }
| v=VarList TURNSTILE e=Expr EVALTO TRUE { EvalExp (v, e, BoolV true) }
| v=VarList TURNSTILE e=Expr EVALTO FALSE { EvalExp (v, e, BoolV false) }

VarList :
| hd=SingleVar COMMA tl=VarList { hd::tl } 
| v=SingleVar { v::[] }
| { [] }

SingleVar : 
| x=ID EQ i=INTV { (x, IntV i) }
| x=ID EQ TRUE { (x, BoolV true) }
| x=ID EQ FALSE { (x, BoolV false) }

Expr :
| e=LetExpr { e }

LetExpr :
| LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }
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
| i=ID { Var i }
| TRUE { BLit true }
| FALSE { BLit false }
| LPAREN e=Expr RPAREN { e }
| IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }