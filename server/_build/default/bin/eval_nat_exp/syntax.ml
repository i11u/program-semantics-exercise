type nat = int
type e = Nat of nat | Plus of e * e | Mult of e * e

type judgement = 
| EvalExp of e * nat
| PlusExp of nat * nat * nat
| MultExp of nat * nat * nat

type rule = Econst | Eplus | Etimes | Pzero | Psucc | Tzero | Tsucc