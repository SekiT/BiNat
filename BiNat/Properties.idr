module BiNat.Properties

import BiNat

%default total

succDashReversesAcc : (n : BiNat) -> (acc : List Bit) -> succ' n acc = foldl (-:) (succ' n []) acc
succDashReversesAcc J        acc = Refl
succDashReversesAcc (n -: O) acc = Refl
succDashReversesAcc (n -: I) acc =
  rewrite succDashReversesAcc n (O :: acc) in
  rewrite succDashReversesAcc n [O] in Refl

predDashReversesAcc : (n : BiNat) -> (acc : List Bit) -> pred' n acc = foldl (-:) (pred' n []) acc
predDashReversesAcc J              acc = Refl
predDashReversesAcc (n -: I)       acc = Refl
predDashReversesAcc (J -: O)       acc = Refl
predDashReversesAcc (ns -: n -: O) acc =
  rewrite predDashReversesAcc (ns -: n) (I :: acc) in
  rewrite predDashReversesAcc (ns -: n) [I] in Refl

predOfSucc : (n : BiNat) -> pred (succ n) = n
predOfSucc J              = Refl
predOfSucc (n -: O)       = Refl
predOfSucc (J -: I)       = Refl
predOfSucc (ns -: O -: I) = Refl
predOfSucc (ns -: I -: I) =
  rewrite succDashReversesAcc ns [O, O] in
  rewrite predDashReversesAcc (succ' ns [] -: O) [I] in
  rewrite sym $ succDashReversesAcc ns [O] in
  rewrite predOfSucc (ns -: I) in Refl
