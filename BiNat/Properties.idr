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

nextCarrySymmetric : (a : Bit) -> (b : Bit) -> (c : Bit) -> nextCarry a b c = nextCarry b a c
nextCarrySymmetric O O O = Refl
nextCarrySymmetric O O I = Refl
nextCarrySymmetric O I O = Refl
nextCarrySymmetric O I I = Refl
nextCarrySymmetric I O O = Refl
nextCarrySymmetric I O I = Refl
nextCarrySymmetric I I O = Refl
nextCarrySymmetric I I I = Refl

nextAccSymmetric : (a : Bit) -> (b : Bit) -> (c : Bit) -> nextAcc a b c = nextAcc b a c
nextAccSymmetric O O O = Refl
nextAccSymmetric O O I = Refl
nextAccSymmetric O I O = Refl
nextAccSymmetric O I I = Refl
nextAccSymmetric I O O = Refl
nextAccSymmetric I O I = Refl
nextAccSymmetric I I O = Refl
nextAccSymmetric I I I = Refl

plusDashSymmetric : (m : BiNat) -> (n : BiNat) -> (carry : Bit) -> (acc : List Bit) -> plus' m n carry acc = plus' n m carry acc
plusDashSymmetric J         J         carry acc = Refl
plusDashSymmetric J         (ns -: n) O     acc = Refl
plusDashSymmetric J         (ns -: n) I     acc = Refl
plusDashSymmetric (ms -: m) J         O     acc = Refl
plusDashSymmetric (ms -: m) J         I     acc = Refl
plusDashSymmetric (ms -: m) (ns -: n) carry acc =
  rewrite nextCarrySymmetric n m carry in
  rewrite nextAccSymmetric n m carry in
  plusDashSymmetric ms ns (nextCarry m n carry) (nextAcc m n carry :: acc)

plusSymmetric : (m : BiNat) -> (n : BiNat) -> plus m n = plus n m
plusSymmetric m n = plusDashSymmetric m n O []
