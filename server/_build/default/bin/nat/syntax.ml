type nat = int

type judgement = 
| PlusExp of nat * nat * nat
| MultExp of nat * nat * nat

type rule = Pzero | Psucc | Tzero | Tsucc