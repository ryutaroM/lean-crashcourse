inductive MyNat where
    | zero
    | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ
#check MyNat.succ MyNat.zero
