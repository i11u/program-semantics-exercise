%{
open Syntax
%}

%token EVALTO IF THEN ELSE TRUE FALSE
%token PLUS MULT MINUS LT
%token LET EQ IN COMMA
%token LPAREN RPAREN
%token TURNSTILE
%token FUN REC ARROW LBRACKET RBRACKET
%token NIL CONS
%token MATCH WITH BAR

%token <Syntax.id> ID
%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| vl=VarList TURNSTILE e=Expr EVALTO v=SingleValue { EvalExp (vl, e, v) }
| vl=VarList TURNSTILE e=Expr EVALTO c=ConsVExpr { EvalExp (vl, e, c) }

// Environment

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

// Value

// これだと行ける
ConsVExpr :
| v1=SingleValue CONS v2=ConsVExpr { ConsV (v1, v2) }
| v=SingleValue { v }
| NIL { NilV }

SingleValue :
| i=INTV { IntV i }
| TRUE { BoolV true }
| FALSE { BoolV false }
| v=ProcVExpr { v }
| v=RecProcVExpr { v }

// これだと行けない。なぜ？
// ConsVExpr :
// | v1=SingleValue CONS v2=ConsVExpr { ConsV (v1, v2) }
// | v=SingleValue { v }

// SingleValue :
// | NIL { NilV }
// | i=INTV { IntV i }
// | TRUE { BoolV true }
// | FALSE { BoolV false }
// | v=ProcVExpr { v }
// | v=RecProcVExpr { v }

ProcVExpr :
| LPAREN v=VarList RPAREN LBRACKET FUN x=ID ARROW e=Expr RBRACKET { ProcV (x, e, v) }

RecProcVExpr :
| LPAREN v=VarList RPAREN LBRACKET REC x=ID EQ FUN y=ID ARROW e=Expr RBRACKET { RecProcV (x, y, e, v) }

// Expression

Expr :
| e=FunExpr { e }
| e=ConsExpr { e }

ConsExpr :
| e1=FunExpr CONS e2=ConsExpr { ConsExp (e1, e2) }
| NIL { NilExp }

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
| MATCH e1=Expr WITH NIL ARROW e2=Expr BAR x=ID CONS y=ID ARROW e3=Expr { MatchExp (e1, e2, x, y, e3) }


