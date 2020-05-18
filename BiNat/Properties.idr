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

plusJIsSucc : (n : BiNat) -> plus n J = succ n
plusJIsSucc J         = Refl
plusJIsSucc (ns -: n) = Refl

jPlusIsSucc : (n : BiNat) -> plus J n = succ n
jPlusIsSucc J         = Refl
jPlusIsSucc (ns -: n) = Refl

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

plusDashSymmetric : (m : BiNat) -> (n : BiNat) -> (carry : Bit) -> (acc : List Bit) ->
  plus' m n carry acc = plus' n m carry acc
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

plusDashReversesAcc : (m : BiNat) -> (n : BiNat) -> (carry : Bit) -> (acc : List Bit) ->
  plus' m n carry acc = foldl (-:) (plus' m n carry []) acc
plusDashReversesAcc J         J         carry acc = Refl
plusDashReversesAcc J         (ns -: n) O     acc = succDashReversesAcc (ns -: n) acc
plusDashReversesAcc J         (ns -: n) I     acc =
  rewrite succDashReversesAcc ns [n] in
  rewrite succDashReversesAcc ns (n :: acc) in Refl
plusDashReversesAcc (ms -: m) J         O     acc = succDashReversesAcc (ms -: m) acc
plusDashReversesAcc (ms -: m) J         I     acc =
  rewrite succDashReversesAcc ms [m] in
  rewrite succDashReversesAcc ms (m :: acc) in Refl
plusDashReversesAcc (ms -: m) (ns -: n) carry acc =
  rewrite plusDashReversesAcc ms ns (nextCarry m n carry) (nextAcc m n carry :: acc) in
  rewrite plusDashReversesAcc ms ns (nextCarry m n carry) [nextAcc m n carry] in Refl

succGoesToCarry : (m : BiNat) -> (n : BiNat) -> (acc : List Bit) -> succ' (plus' m n O []) acc = plus' m n I acc
succGoesToCarry J         J         acc = Refl
succGoesToCarry (ms -: O) J         acc = Refl
succGoesToCarry (ms -: I) J         acc = rewrite succDashReversesAcc ms [O] in rewrite succDashReversesAcc ms (I :: acc) in Refl
succGoesToCarry J         (ns -: O) acc = Refl
succGoesToCarry J         (ns -: I) acc = rewrite succDashReversesAcc ns [O] in rewrite succDashReversesAcc ns (I :: acc) in Refl
succGoesToCarry (ms -: O) (ns -: O) acc = rewrite plusDashReversesAcc ms ns O [O] in rewrite plusDashReversesAcc ms ns O (I :: acc) in Refl
succGoesToCarry (ms -: O) (ns -: I) acc = rewrite plusDashReversesAcc ms ns O [I] in rewrite succGoesToCarry ms ns (O :: acc) in Refl
succGoesToCarry (ms -: I) (ns -: O) acc = rewrite plusDashReversesAcc ms ns O [I] in rewrite succGoesToCarry ms ns (O :: acc) in Refl
succGoesToCarry (ms -: I) (ns -: I) acc = rewrite plusDashReversesAcc ms ns I [O] in rewrite plusDashReversesAcc ms ns I (I :: acc) in Refl

succDashCommutesToPlusDashSnd : (m : BiNat) -> (n : BiNat) -> (acc : List Bit) ->
  succ' (plus m n) acc = plus' m (succ n) O acc
succDashCommutesToPlusDashSnd J         J         acc = Refl
succDashCommutesToPlusDashSnd J         (ns -: O) acc = Refl
succDashCommutesToPlusDashSnd J         (ns -: I) acc =
  rewrite succDashReversesAcc (succ' ns [O]) acc in
  rewrite plusDashReversesAcc J (succ' ns [O]) O acc in
  rewrite jPlusIsSucc (succ' ns [O]) in Refl
succDashCommutesToPlusDashSnd (ms -: O) J         acc =
  rewrite succDashReversesAcc ms (O :: acc) in
  rewrite plusDashReversesAcc ms J O (O :: acc) in
  rewrite plusJIsSucc ms in Refl
succDashCommutesToPlusDashSnd (ms -: I) J         acc =
  rewrite succDashReversesAcc ms [O] in
  rewrite sym $ plusJIsSucc ms in
  rewrite plusDashReversesAcc ms J O (I :: acc) in Refl
succDashCommutesToPlusDashSnd (ms -: O) (ns -: O) acc =
  rewrite plusDashReversesAcc ms ns O [O] in
  rewrite plusDashReversesAcc ms ns O (I :: acc) in Refl
succDashCommutesToPlusDashSnd (ms -: O) (ns -: I) acc =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite succDashCommutesToPlusDashSnd ms ns (O :: acc) in
  rewrite succDashReversesAcc ns [O] in Refl
succDashCommutesToPlusDashSnd (ms -: I) (ns -: O) acc =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite succGoesToCarry ms ns (O :: acc) in Refl
succDashCommutesToPlusDashSnd (ms -: I) (ns -: I) acc =
  rewrite plusDashReversesAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite succDashReversesAcc ns [O] in
  rewrite sym $ succDashCommutesToPlusDashSnd ms ns (I :: acc) in
  rewrite succDashReversesAcc (plus' ms ns O []) (I :: acc) in Refl

succDashCommutesToPlusDashFst : (m : BiNat) -> (n : BiNat) -> (acc : List Bit) ->
  succ' (plus m n) acc = plus' (succ m) n O acc
succDashCommutesToPlusDashFst m n acc =
  rewrite plusSymmetric m n in
  rewrite succDashCommutesToPlusDashSnd n m acc in
  rewrite plusDashSymmetric n (succ m) O acc in Refl

plusAssociative : (l : BiNat) -> (m : BiNat) -> (n : BiNat) -> plus l (plus m n) = plus (plus l m) n
plusAssociative J         J         J         = Refl
plusAssociative J         J         (ns -: O) =
  rewrite succDashReversesAcc ns [O] in
  rewrite plusDashReversesAcc J ns O [O] in
  rewrite jPlusIsSucc ns in Refl
plusAssociative J         J         (ns -: I) =
  rewrite succDashReversesAcc ns [O] in
  rewrite plusDashReversesAcc J ns O [I] in
  rewrite jPlusIsSucc ns in Refl
plusAssociative J         (ms -: O) J         = Refl
plusAssociative J         (ms -: I) J         = plusDashSymmetric J (succ' ms [O]) O []
plusAssociative (ls -: O) J         J         =
  rewrite succDashReversesAcc ls [O] in
  rewrite plusDashReversesAcc ls J O [O] in
  rewrite plusJIsSucc ls in Refl
plusAssociative (ls -: I) J         J         =
  rewrite succDashReversesAcc ls [O] in
  rewrite plusDashReversesAcc ls J O [I] in
  rewrite plusJIsSucc ls in Refl
plusAssociative J         (ms -: O) (ns -: O) =
  rewrite plusDashReversesAcc ms ns O [O] in
  rewrite plusDashReversesAcc ms ns O [I] in Refl
plusAssociative J         (ms -: O) (ns -: I) =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite sym $ succGoesToCarry ms ns [O] in Refl
plusAssociative J         (ms -: I) (ns -: O) =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite succDashReversesAcc (plus' ms ns O []) [O] in
  rewrite sym $ jPlusIsSucc (plus' ms ns O []) in
  rewrite succDashReversesAcc ms [O] in
  rewrite plusDashReversesAcc (succ' ms []) ns O [O] in
  rewrite sym $ jPlusIsSucc ms in
  rewrite plusAssociative J ms ns in Refl
plusAssociative J         (ms -: I) (ns -: I) =
  rewrite plusDashReversesAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite succDashReversesAcc ms [O] in
  rewrite plusDashReversesAcc (succ' ms []) ns O [I] in
  rewrite sym $ jPlusIsSucc ms in
  rewrite sym $ jPlusIsSucc (plus' ms ns O []) in
  rewrite plusAssociative J ms ns in Refl
plusAssociative (ls -: O) J         (ns -: O) = Refl
plusAssociative (ls -: O) J         (ns -: I) =
  rewrite succDashReversesAcc ns [O] in
  rewrite plusDashReversesAcc ls (succ' ns []) O [O] in
  rewrite sym $ plusJIsSucc ns in
  rewrite sym $ succGoesToCarry ls ns [O] in
  rewrite succDashReversesAcc (plus' ls ns O []) [O] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusAssociative ls ns J in Refl
plusAssociative (ls -: I) J         (ns -: O) =
  rewrite sym $ succGoesToCarry ls ns [O] in
  rewrite succDashReversesAcc (plus' ls ns O []) [O] in
  rewrite sym $ jPlusIsSucc (plus' ls ns O []) in
  rewrite succDashReversesAcc ls [O] in
  rewrite plusDashReversesAcc (succ' ls []) ns O [O] in
  rewrite sym $ jPlusIsSucc ls in
  rewrite plusAssociative J ls ns in Refl
plusAssociative (ls -: I) J         (ns -: I) =
  rewrite succDashReversesAcc ns [O] in
  rewrite plusDashReversesAcc ls (succ' ns []) O [I] in
  rewrite sym $ jPlusIsSucc ns in
  rewrite succDashReversesAcc ls [O] in
  rewrite plusDashReversesAcc (succ' ls []) ns O [I] in
  rewrite sym $ plusJIsSucc ls in
  rewrite plusAssociative ls J ns in Refl
plusAssociative (ls -: O) (ns -: O) J         =
  rewrite plusDashReversesAcc ls ns O [O] in
  rewrite plusDashReversesAcc ls ns O [I] in Refl
plusAssociative (ls -: O) (ns -: I) J         =
  rewrite succDashReversesAcc ns [O] in
  rewrite sym $ plusJIsSucc ns in
  rewrite plusDashReversesAcc ls (plus' ns J O []) O [O] in
  rewrite plusDashReversesAcc ls ns O [I] in
  rewrite succDashReversesAcc (plus' ls ns O []) [O] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusAssociative ls ns J in Refl
plusAssociative (ls -: I) (ns -: O) J         =
  rewrite plusDashReversesAcc ls ns I [O] in
  rewrite sym $ succGoesToCarry ls ns [] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusDashReversesAcc ls ns O [I] in
  rewrite succDashReversesAcc (plus' ls ns O []) [O] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in Refl
plusAssociative (ls -: I) (ns -: I) J         =
  rewrite succDashReversesAcc ns [O] in
  rewrite plusDashReversesAcc ls (succ' ns []) O [I] in
  rewrite sym $ plusJIsSucc ns in
  rewrite plusDashReversesAcc ls ns I [O] in
  rewrite sym $ succGoesToCarry ls ns [] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusAssociative ls ns J in Refl
plusAssociative (ls -: O) (ms -: O) (ns -: O) =
  rewrite plusDashReversesAcc ms ns O [O] in
  rewrite plusDashReversesAcc ls (plus' ms ns O []) O [O] in
  rewrite plusDashReversesAcc ls ms O [O] in
  rewrite plusDashReversesAcc (plus' ls ms O []) ns O [O] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: O) (ms -: O) (ns -: I) =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite plusDashReversesAcc ls (plus' ms ns O []) O [I] in
  rewrite plusDashReversesAcc ls ms O [O] in
  rewrite plusDashReversesAcc (plus' ls ms O []) ns O [I] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: O) (ms -: I) (ns -: O) =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite plusDashReversesAcc ls (plus' ms ns O []) O [I] in
  rewrite plusDashReversesAcc ls ms O [I] in
  rewrite plusDashReversesAcc (plus' ls ms O []) ns O [I] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: O) (ms -: I) (ns -: I) =
  rewrite plusDashReversesAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite plusDashReversesAcc ls ms O [I] in
  rewrite sym $ succGoesToCarry (plus' ls ms O []) ns [O] in
  rewrite sym $ plusAssociative ls ms ns in
  rewrite succDashCommutesToPlusDashSnd ls (plus' ms ns O []) [O] in Refl
plusAssociative (ls -: I) (ms -: O) (ns -: O) =
  rewrite plusDashReversesAcc ms ns O [O] in
  rewrite plusDashReversesAcc ls (plus' ms ns O []) O [I] in
  rewrite plusDashReversesAcc ls ms O [I] in
  rewrite plusDashReversesAcc (plus' ls ms O []) ns O [I] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: I) (ms -: O) (ns -: I) =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite sym $ succGoesToCarry ls (plus' ms ns O []) [O] in
  rewrite plusDashReversesAcc ls ms O [I] in
  rewrite sym $ succGoesToCarry (plus' ls ms O []) ns [O] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: I) (ms -: I) (ns -: O) =
  rewrite plusDashReversesAcc ms ns O [I] in
  rewrite sym $ succGoesToCarry ls (plus' ms ns O []) [O] in
  rewrite plusDashReversesAcc ls ms I [O] in
  rewrite sym $ succGoesToCarry ls ms [] in
  rewrite sym $ succDashCommutesToPlusDashFst (plus' ls ms O []) ns [O] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: I) (ms -: I) (ns -: I) =
  rewrite plusDashReversesAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite sym $ succDashCommutesToPlusDashSnd ls (plus' ms ns O []) [I] in
  rewrite plusDashReversesAcc ls ms I [O] in
  rewrite sym $ succGoesToCarry ls ms [] in
  rewrite sym $ succDashCommutesToPlusDashFst (plus' ls ms O []) ns [I] in
  rewrite plusAssociative ls ms ns in Refl

shiftLeftDoubles : (n : BiNat) -> n -: O = plus n n
shiftLeftDoubles J         = Refl
shiftLeftDoubles (ns -: O) =
  rewrite plusDashReversesAcc ns ns O [O] in
  rewrite shiftLeftDoubles ns in Refl
shiftLeftDoubles (ns -: I) =
  rewrite plusDashReversesAcc ns ns I [O] in
  rewrite sym $ succGoesToCarry ns ns [] in
  rewrite sym $ shiftLeftDoubles ns in Refl

composeFunctions : {T : BiNat -> Type} -> ((k : BiNat) -> T k -> T (succ k)) ->
  (m : BiNat) -> (n : BiNat) -> T m -> T (plus m n)
composeFunctions f m J         pm = replace (sym $ plusJIsSucc m) (f m pm)
composeFunctions f m (ns -: O) pm =
  replace {P = \z => T (plus m z)} (sym $ shiftLeftDoubles ns) $
  replace (sym $ plusAssociative m ns ns) $
  composeFunctions f (plus m ns) ns $
  composeFunctions f m ns pm
composeFunctions f m (ns -: I) pm =
  replace {P = \z => T z} (sym $ plusAssociative m J (ns -: O)) $
  replace {P = \z => T (plus (plus m J) z)} (sym $ shiftLeftDoubles ns) $
  replace {P = \z => T z} (sym $ plusAssociative (plus m J) ns ns) $
  composeFunctions f (plus (plus m J) ns) ns $
  composeFunctions f (plus m J) ns $
  replace (sym $ plusJIsSucc m) (f m pm)

induction : (P : BiNat -> Type) -> ((k : BiNat) -> P k -> P (succ k)) -> P J -> (n : BiNat) -> P n
induction prop step pj J         = pj
induction prop step pj (ns -: n) =
  replace (succOfPred (ns -: n) uninhabited) $
  replace (jPlusIsSucc (pred (ns -: n))) $
  composeFunctions step J (pred (ns -: n)) pj

succIsNotJ : (n : BiNat) -> Not (succ n = J)
succIsNotJ J         eq = uninhabited eq
succIsNotJ (ns -: O) eq = uninhabited eq
succIsNotJ (ns -: I) eq = uninhabited $ replace {P = \z => z = J} (succDashReversesAcc ns [O]) eq

predOfDoubled : (n : BiNat) -> Not (n = J) -> pred (n -: O) = pred n -: I
predOfDoubled J notJ = absurd $ notJ Refl
predOfDoubled (ns -: O) _ = predDashReversesAcc (ns -: O) [I]
predOfDoubled (ns -: I) _ = Refl

predCommutesToPlusSnd : (m : BiNat) -> (n : BiNat) -> Not (n = J) ->
  pred (plus m n) = plus m (pred n)
predCommutesToPlusSnd m n notJ =
  induction
    (\k => pred (plus k n) = plus k (pred n))
    (\k, pk =>
      rewrite sym $ jPlusIsSucc k in
      rewrite sym $ plusAssociative J k n in
      rewrite jPlusIsSucc (plus k n) in
      rewrite predOfSucc (plus k n) in
      rewrite plusSymmetric J k in
      rewrite sym $ plusAssociative k J (pred n) in
      rewrite jPlusIsSucc (pred n) in
      rewrite succOfPred n notJ in Refl
    )
    (
      rewrite jPlusIsSucc n in
      rewrite predOfSucc n in
      rewrite jPlusIsSucc (pred n) in
      rewrite succOfPred n notJ in Refl
    )
    m

multDashAddsAccMinusJ : (m : BiNat) -> (n : BiNat) -> (acc : BiNat) ->
  mult' m n acc = pred $ plus (mult' m n J) acc
multDashAddsAccMinusJ J         ns acc = rewrite plusJIsSucc ns in rewrite predOfSucc ns in Refl
multDashAddsAccMinusJ (ms -: O) ns acc = multDashAddsAccMinusJ ms (ns -: O) acc
multDashAddsAccMinusJ (ms -: I) ns acc =
  rewrite multDashAddsAccMinusJ ms (ns -: O) (plus' ns acc O []) in
  rewrite multDashAddsAccMinusJ ms (ns -: O) (plus' ns J O []) in
  rewrite plusAssociative (mult' ms (ns -: O) J) ns J in
  rewrite plusJIsSucc (plus' (mult' ms (ns -: O) J) ns O []) in
  rewrite predOfSucc (plus' (mult' ms (ns -: O) J) ns O []) in
  rewrite plusAssociative (mult' ms (ns -: O) J) ns acc in Refl

multDistributesPlusRight : (l : BiNat) -> (m : BiNat) -> (n : BiNat) ->
  mult l (plus m n) = plus (mult l m) (mult l n)
multDistributesPlusRight J m n =
  rewrite plusJIsSucc (plus' m n O []) in
  rewrite predOfSucc (plus' m n O []) in
  rewrite plusJIsSucc m in
  rewrite predOfSucc m in
  rewrite plusJIsSucc n in
  rewrite predOfSucc n in Refl
multDistributesPlusRight (ls -: O) m n =
  rewrite sym $ plusDashReversesAcc m n O [O] in
  multDistributesPlusRight ls (m -: O) (n -: O)
multDistributesPlusRight (ls -: I) m n =
  rewrite plusJIsSucc (plus' m n O []) in
  rewrite multDashAddsAccMinusJ ls (plus' m n O [] -: O) (succ (plus' m n O [])) in
  rewrite predCommutesToPlusSnd (mult ls (plus m n -: O)) (succ (plus m n)) (succIsNotJ (plus m n)) in
  rewrite predOfSucc (plus m n) in
  rewrite sym $ plusDashReversesAcc m n O [O] in
  rewrite plusJIsSucc m in
  rewrite plusJIsSucc n in
  rewrite multDashAddsAccMinusJ ls (m -: O) (succ m) in
  rewrite multDashAddsAccMinusJ ls (n -: O) (succ n) in
  rewrite predCommutesToPlusSnd (mult ls (m -: O)) (succ m) (succIsNotJ m) in
  rewrite predCommutesToPlusSnd (mult ls (n -: O)) (succ n) (succIsNotJ n) in
  rewrite predOfSucc m in
  rewrite predOfSucc n in
  rewrite sym $ plusAssociative (mult ls (m -: O)) m (plus (mult ls (n -: O)) n) in
  rewrite plusSymmetric m (plus (mult ls (n -: O)) n) in
  rewrite sym $ plusAssociative (mult ls (n -: O)) n m in
  rewrite plusSymmetric n m in
  rewrite plusAssociative (mult ls (m -: O)) (mult ls (n -: O)) (plus' m n O []) in
  rewrite multDistributesPlusRight ls (m -: O) (n -: O) in Refl

multJIsId : (n : BiNat) -> mult n J = n
multJIsId J = Refl
multJIsId (ns -: O) =
  rewrite multDistributesPlusRight ns J J in
  rewrite multJIsId ns in
  rewrite shiftLeftDoubles ns in Refl
multJIsId (ns -: I) =
  rewrite multDashAddsAccMinusJ ns (J -: O) (J -: O) in
  rewrite multDistributesPlusRight ns J J in
  rewrite multJIsId ns in
  rewrite sym $ shiftLeftDoubles ns in
  rewrite plusDashReversesAcc ns J O [O] in
  rewrite plusJIsSucc ns in
  rewrite predOfDoubled (succ ns) (succIsNotJ ns) in
  rewrite predOfSucc ns in Refl

multDistributesPlusLeft : (l : BiNat) -> (m : BiNat) -> (n : BiNat) ->
  mult (plus l m) n = plus (mult l n) (mult m n)
multDistributesPlusLeft l m n =
  induction
    (\k => mult (plus l m) k = plus (mult l k) (mult m k))
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite multDistributesPlusRight (plus' l m O []) k J in
      rewrite pk in
      rewrite multJIsId (plus' l m O []) in
      rewrite multDistributesPlusRight l k J in
      rewrite multDistributesPlusRight m k J in
      rewrite multJIsId l in
      rewrite multJIsId m in
      rewrite sym $ plusAssociative (mult l k) l (plus (mult m k) m) in
      rewrite plusSymmetric l (plus (mult m k) m) in
      rewrite sym $ plusAssociative (mult m k) m l in
      rewrite plusSymmetric m l in
      sym $ plusAssociative (mult l k) (mult m k) (plus l m)
    )
    (rewrite multJIsId (plus l m) in rewrite multJIsId l in rewrite multJIsId m in Refl)
    n
