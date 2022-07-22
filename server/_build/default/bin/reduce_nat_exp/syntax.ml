type nat = int
type e = Nat of nat | Plus of e * e | Mult of e * e

type judgement = 
| ReduceExp of e * e
| MReduceExp of e * e
| DReduceExp of e * e
| PlusExp of nat * nat * nat
| MultExp of nat * nat * nat

type rule = Rplus | Rtimes | Rplusl | Rplusr | Rtimesl | Rtimesr | DRplus | DRtimes | DRplusl | DRplusr | DRtimesl | DRtimesr | MRzero | MRmulti | MRone | Pzero | Psucc | Tzero | Tsucc