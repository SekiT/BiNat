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

succOfPred : (n : BiNat) -> Not (n = J) -> succ (pred n) = n
succOfPred J              notJ = absurd (notJ Refl)
succOfPred (n -: I)       _    = Refl
succOfPred (J -: O)       _    = Refl
succOfPred (ns -: I -: O) _    = Refl
succOfPred (ns -: O -: O) _    =
  rewrite predDashReversesAcc (ns -: O) [I] in
  rewrite succDashReversesAcc (pred' (ns -: O) []) [O] in
  rewrite succOfPred (ns -: O) uninhabited in Refl

succInjective : (m : BiNat) -> (n : BiNat) -> succ m = succ n -> m = n
succInjective m n eq =
  rewrite sym $ predOfSucc m in
  rewrite eq in
  predOfSucc n

plusJIsSucc : (m : BiNat) -> plus m J = succ m
plusJIsSucc J         = Refl
plusJIsSucc (ms -: m) = Refl
