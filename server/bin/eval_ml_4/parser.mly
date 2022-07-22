%{
open Syntax
%}

%token EVALTO IF THEN ELSE TRUE FALSE
%token PLUS MULT MINUS LT
%token LET EQ IN COMMA
%token LPAREN RPAREN
%token TURNSTILE
%token FUN REC ARROW LBRACKET RBRACKET

%token <Syntax.id> ID
%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| v=VarList TURNSTILE e=Expr EVALTO i=INTV { EvalExp (v, e, IntV i) }
| v=VarList TURNSTILE e=Expr EVALTO TRUE { EvalExp (v, e, BoolV true) }
| v=VarList TURNSTILE e=Expr EVALTO FALSE { EvalExp (v, e, BoolV false) }
| v=VarList TURNSTILE e=Expr EVALTO p=ProcVExpr { EvalExp (v, e, p) }
| v=VarList TURNSTILE e=Expr EVALTO r=RecProcVExpr { EvalExp (v, e, r) }

VarList :
| hd=SingleVar COMMA tl=VarList { hd::tl } 
| v=SingleVar { v::[] }
| { [] }

SingleVar : 
| x=ID EQ i=INTV { (x, IntV i) }
| x=ID EQ TRUE { (x, BoolV true) }
| x=ID EQ FALSE { (x, BoolV false) }
| x=ID EQ p=ProcVExpr { (x, p) }
| x=ID EQ r=RecProcVExpr { (x, r) }

ProcVExpr :
| LPAREN v=VarList RPAREN LBRACKET FUN x=ID ARROW e=Expr RBRACKET { ProcV (x, e, ref v) }

RecProcVExpr :
| LPAREN v=VarList RPAREN LBRACKET REC x=ID EQ FUN y=ID ARROW e=Expr RBRACKET { RecProcV (x, y, e, ref v) }

Expr :
| e=FunExpr { e }

FunExpr :
| FUN x=ID ARROW e=FunExpr { FunExp (x, e) }
| e=LetExpr { e }

LetExpr :
| LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }
| LET REC x=ID EQ FUN y=ID ARROW e1=Expr IN e2=Expr { LetRecExp (x, y, e1, e2) }
| e=LTExpr { e }

LTExpr :
| l=LTExpr LT r=PMExpr { BinOp (Lt, l, r) }
| e=PMExpr { e }

PMExpr :
| l=PMExpr PLUS r=MExpr { BinOp (Plus, l, r) }
| l=PMExpr MINUS r=MExpr { BinOp (Minus, l, r) }
| e=MExpr { e }

MExpr :
| l=MExpr MULT r=AppExpr { BinOp (Mult, l, r) }
| e=AppExpr { e }

AppExpr :
| e1=AppExpr e2=AExpr { AppExp (e1, e2) }
| e=AExpr { e }

AExpr :
| i=INTV { ILit i }
| i=ID { Var i }
| TRUE { BLit true }
| FALSE { BLit false }
| LPAREN e=Expr RPAREN { e }
| IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }
