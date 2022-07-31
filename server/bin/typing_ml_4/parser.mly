%{
open Syntax
%}

%token IF THEN ELSE TRUE FALSE
%token PLUS MULT MINUS LT
%token LET EQ IN COMMA
%token LPAREN RPAREN
%token TURNSTILE
%token FUN REC ARROW
%token LBRACKET_RBRACKET CONSTRUCT
%token MATCH WITH BAR
%token COLON
%token INT BOOL LIST

%token <Syntax.id> ID
%token <int> INTV

%right CONSTRUCT

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| tl=TyVarList TURNSTILE e=Expr COLON t=Type { TyExp (tl, e, t) }

// Type

// Parserがバグるため、仕方なく、問題ごとに許容するTypeを手書きしている。。。

// バグ↓
// Type : 
// | INT { TyInt }
// | BOOL { TyBool }
// | t=ListType { t }
// | t=FunType{ t }

// FunType :
// | t1=ListType ARROW t2=ListType { TyFun (t1, t2) }

// ListType :
// | INT LIST { TyList TyInt }
// | BOOL LIST { TyList TyBool }

Type :
| INT { TyInt }  // 80, 81, 82, 83, 85, 87, 92, 99, 100, 101, 103
// | BOOL { TyBool }  // 94
// | INT ARROW INT { TyFun (TyInt, TyInt) }  // 84, 95, 96, 97, 98
// | LPAREN INT ARROW INT RPAREN ARROW INT { TyFun (TyFun (TyInt, TyInt), TyInt) }  // 86
// | INT LIST { TyList TyInt }  // 88, 93
// | BOOL LIST { TyList TyBool }  // 89, 105, 106
// | INT ARROW INT ARROW INT { TyFun (TyInt, TyFun (TyInt, TyInt)) }  // 90
// | BOOL ARROW INT ARROW BOOL { TyFun (TyBool, TyFun (TyInt, TyBool)) }  // 91
// | INT LIST ARROW INT { TyFun (TyList TyInt, TyInt) }  // 102
// | INT LIST ARROW INT { TyFun (TyList TyInt, TyFun (TyList TyInt, TyList TyInt)) }  // 104

// Type Environment

TyVarList :
| hd=SingleVar COMMA tl=TyVarList { hd::tl } 
| v=SingleVar { v::[] }
| { [] }

SingleVar :
| x=ID COLON v=Type { (x, v) }

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
