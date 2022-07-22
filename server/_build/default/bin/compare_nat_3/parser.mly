%{
  open Syntax
%}

%token LT
%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel

%%

toplevel : 
| n1=INTV LT n2=INTV { LessThanExp (n1, n2) }