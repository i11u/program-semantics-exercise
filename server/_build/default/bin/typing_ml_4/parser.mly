%{
open Syntax
%}

%token EVALTO IF THEN ELSE TRUE FALSE
%token PLUS MULT MINUS LT
%token LET EQ IN COMMA
%token LPAREN RPAREN
%token TURNSTILE
%token FUN REC ARROW LBRACKET RBRACKET
%token LBRACKET_RBRACKET CONSTRUCT
%token MATCH WITH BAR
%token COLON

%token <Syntax.id> ID
%token <int> INTV

%right CONSTRUCT

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| vl=VarList TURNSTILE e=Expr EVALTO v=Value { EvalExp (vl, e, v) }

// Value

Value :
| i=INTV { IntV i }
| TRUE { BoolV true }
| FALSE { BoolV false }
| v=ProcVExpr { v }
| v=RecProcVExpr { v }
| LBRACKET_RBRACKET { NilV }
// ここをコメント解除する→Valueにリストを許容できる
// なぜかは原因解読中
// | i=INTV CONSTRUCT v2=Value { ConsV (IntV i, v2) }

ProcVExpr :
| LPAREN v=VarList RPAREN LBRACKET FUN x=ID ARROW e=Expr RBRACKET { ProcV (x, e, v) }

RecProcVExpr :
| LPAREN v=VarList RPAREN LBRACKET REC x=ID EQ FUN y=ID ARROW e=Expr RBRACKET { RecProcV (x, y, e, v) }

// Environment

VarList :
| hd=SingleVar COMMA tl=VarList { hd::tl } 
| v=SingleVar { v::[] }
| { [] }

SingleVar :
| x=ID EQ v=Value { (x, v) }

// Expression

Expr :
| e=FunExpr { e }
| e=ConsExpr { e }
| e=LetExpr { e }
| e=LTExpr { e }
| e=IfExpr { e }
| e=MatchExpr { e }

ConsExpr :
| e1=Expr CONSTRUCT e2=Expr { ConsExp (e1, e2) }

FunExpr :
| FUN x=ID ARROW e=Expr { FunExp (x, e) }

IfExpr : 
| IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

MatchExpr :
| MATCH e1=Expr WITH LBRACKET_RBRACKET ARROW e2=Expr BAR x=ID CONSTRUCT y=ID ARROW e3=Expr { MatchExp (e1, e2, x, y, e3) }

LetExpr :
| LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }
| LET REC x=ID EQ FUN y=ID ARROW e1=Expr IN e2=Expr { LetRecExp (x, y, e1, e2) }

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
| LBRACKET_RBRACKET { NilExp }
