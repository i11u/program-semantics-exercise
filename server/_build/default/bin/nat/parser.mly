%{
  open Syntax
%}

%token PLUS MULT IS

%token <int> INTV

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
| n1=INTV PLUS n2=INTV IS n3=INTV { PlusExp (n1, n2, n3) }
| n1=INTV MULT n2=INTV IS n3=INTV { MultExp (n1, n2, n3) }