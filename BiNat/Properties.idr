module BiNat.Properties

import BiNat

%default total

succDashAppendsAcc : (n : BiNat) -> (acc : List Bit) -> succ' n acc = foldl (-:) (succ' n []) acc
succDashAppendsAcc J        acc = Refl
succDashAppendsAcc (n -: O) acc = Refl
succDashAppendsAcc (n -: I) acc =
  rewrite succDashAppendsAcc n (O :: acc) in
  rewrite succDashAppendsAcc n [O] in Refl

predDashAppendsAcc : (n : BiNat) -> (acc : List Bit) -> pred' n acc = foldl (-:) (pred' n []) acc
predDashAppendsAcc J              acc = Refl
predDashAppendsAcc (n -: I)       acc = Refl
predDashAppendsAcc (J -: O)       acc = Refl
predDashAppendsAcc (ns -: n -: O) acc =
  rewrite predDashAppendsAcc (ns -: n) (I :: acc) in
  rewrite predDashAppendsAcc (ns -: n) [I] in Refl

predOfSucc : (n : BiNat) -> pred (succ n) = n
predOfSucc J              = Refl
predOfSucc (n -: O)       = Refl
predOfSucc (J -: I)       = Refl
predOfSucc (ns -: O -: I) = Refl
predOfSucc (ns -: I -: I) =
  rewrite succDashAppendsAcc ns [O, O] in
  rewrite predDashAppendsAcc (succ' ns [] -: O) [I] in
  rewrite sym $ succDashAppendsAcc ns [O] in
  rewrite predOfSucc (ns -: I) in Refl

succOfPred : (n : BiNat) -> Not (n = J) -> succ (pred n) = n
succOfPred J              notJ = absurd (notJ Refl)
succOfPred (n -: I)       _    = Refl
succOfPred (J -: O)       _    = Refl
succOfPred (ns -: I -: O) _    = Refl
succOfPred (ns -: O -: O) _    =
  rewrite predDashAppendsAcc (ns -: O) [I] in
  rewrite succDashAppendsAcc (pred' (ns -: O) []) [O] in
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

plusDashAppendsAcc : (m : BiNat) -> (n : BiNat) -> (carry : Bit) -> (acc : List Bit) ->
  plus' m n carry acc = foldl (-:) (plus' m n carry []) acc
plusDashAppendsAcc J         J         carry acc = Refl
plusDashAppendsAcc J         (ns -: n) O     acc = succDashAppendsAcc (ns -: n) acc
plusDashAppendsAcc J         (ns -: n) I     acc =
  rewrite succDashAppendsAcc ns [n] in
  rewrite succDashAppendsAcc ns (n :: acc) in Refl
plusDashAppendsAcc (ms -: m) J         O     acc = succDashAppendsAcc (ms -: m) acc
plusDashAppendsAcc (ms -: m) J         I     acc =
  rewrite succDashAppendsAcc ms [m] in
  rewrite succDashAppendsAcc ms (m :: acc) in Refl
plusDashAppendsAcc (ms -: m) (ns -: n) carry acc =
  rewrite plusDashAppendsAcc ms ns (nextCarry m n carry) (nextAcc m n carry :: acc) in
  rewrite plusDashAppendsAcc ms ns (nextCarry m n carry) [nextAcc m n carry] in Refl

succGoesToCarry : (m : BiNat) -> (n : BiNat) -> (acc : List Bit) ->
  succ' (plus' m n O []) acc = plus' m n I acc
succGoesToCarry J         J         acc = Refl
succGoesToCarry (ms -: O) J         acc = Refl
succGoesToCarry (ms -: I) J         acc =
  rewrite succDashAppendsAcc ms [O] in
  rewrite succDashAppendsAcc ms (I :: acc) in Refl
succGoesToCarry J         (ns -: O) acc = Refl
succGoesToCarry J         (ns -: I) acc =
  rewrite succDashAppendsAcc ns [O] in
  rewrite succDashAppendsAcc ns (I :: acc) in Refl
succGoesToCarry (ms -: O) (ns -: O) acc =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite plusDashAppendsAcc ms ns O (I :: acc) in Refl
succGoesToCarry (ms -: O) (ns -: I) acc =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite succGoesToCarry ms ns (O :: acc) in Refl
succGoesToCarry (ms -: I) (ns -: O) acc =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite succGoesToCarry ms ns (O :: acc) in Refl
succGoesToCarry (ms -: I) (ns -: I) acc =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite plusDashAppendsAcc ms ns I (I :: acc) in Refl

succDashCommutesToPlusDashSnd : (m : BiNat) -> (n : BiNat) -> (acc : List Bit) ->
  succ' (plus m n) acc = plus' m (succ n) O acc
succDashCommutesToPlusDashSnd J         J         acc = Refl
succDashCommutesToPlusDashSnd J         (ns -: O) acc = Refl
succDashCommutesToPlusDashSnd J         (ns -: I) acc =
  rewrite succDashAppendsAcc (succ' ns [O]) acc in
  rewrite plusDashAppendsAcc J (succ' ns [O]) O acc in
  rewrite jPlusIsSucc (succ' ns [O]) in Refl
succDashCommutesToPlusDashSnd (ms -: O) J         acc =
  rewrite succDashAppendsAcc ms (O :: acc) in
  rewrite plusDashAppendsAcc ms J O (O :: acc) in
  rewrite plusJIsSucc ms in Refl
succDashCommutesToPlusDashSnd (ms -: I) J         acc =
  rewrite succDashAppendsAcc ms [O] in
  rewrite sym $ plusJIsSucc ms in
  rewrite plusDashAppendsAcc ms J O (I :: acc) in Refl
succDashCommutesToPlusDashSnd (ms -: O) (ns -: O) acc =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite plusDashAppendsAcc ms ns O (I :: acc) in Refl
succDashCommutesToPlusDashSnd (ms -: O) (ns -: I) acc =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite succDashCommutesToPlusDashSnd ms ns (O :: acc) in
  rewrite succDashAppendsAcc ns [O] in Refl
succDashCommutesToPlusDashSnd (ms -: I) (ns -: O) acc =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite succGoesToCarry ms ns (O :: acc) in Refl
succDashCommutesToPlusDashSnd (ms -: I) (ns -: I) acc =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite succDashAppendsAcc ns [O] in
  rewrite sym $ succDashCommutesToPlusDashSnd ms ns (I :: acc) in
  rewrite succDashAppendsAcc (plus' ms ns O []) (I :: acc) in Refl

succDashCommutesToPlusDashFst : (m : BiNat) -> (n : BiNat) -> (acc : List Bit) ->
  succ' (plus m n) acc = plus' (succ m) n O acc
succDashCommutesToPlusDashFst m n acc =
  rewrite plusSymmetric m n in
  rewrite succDashCommutesToPlusDashSnd n m acc in
  rewrite plusDashSymmetric n (succ m) O acc in Refl

plusAssociative : (l : BiNat) -> (m : BiNat) -> (n : BiNat) -> plus l (plus m n) = plus (plus l m) n
plusAssociative J         J         J         = Refl
plusAssociative J         J         (ns -: O) =
  rewrite succDashAppendsAcc ns [O] in
  rewrite plusDashAppendsAcc J ns O [O] in
  rewrite jPlusIsSucc ns in Refl
plusAssociative J         J         (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  rewrite plusDashAppendsAcc J ns O [I] in
  rewrite jPlusIsSucc ns in Refl
plusAssociative J         (ms -: O) J         = Refl
plusAssociative J         (ms -: I) J         = plusDashSymmetric J (succ' ms [O]) O []
plusAssociative (ls -: O) J         J         =
  rewrite succDashAppendsAcc ls [O] in
  rewrite plusDashAppendsAcc ls J O [O] in
  rewrite plusJIsSucc ls in Refl
plusAssociative (ls -: I) J         J         =
  rewrite succDashAppendsAcc ls [O] in
  rewrite plusDashAppendsAcc ls J O [I] in
  rewrite plusJIsSucc ls in Refl
plusAssociative J         (ms -: O) (ns -: O) =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite plusDashAppendsAcc ms ns O [I] in Refl
plusAssociative J         (ms -: O) (ns -: I) =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite sym $ succGoesToCarry ms ns [O] in Refl
plusAssociative J         (ms -: I) (ns -: O) =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite succDashAppendsAcc (plus' ms ns O []) [O] in
  rewrite sym $ jPlusIsSucc (plus' ms ns O []) in
  rewrite succDashAppendsAcc ms [O] in
  rewrite plusDashAppendsAcc (succ' ms []) ns O [O] in
  rewrite sym $ jPlusIsSucc ms in
  rewrite plusAssociative J ms ns in Refl
plusAssociative J         (ms -: I) (ns -: I) =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite succDashAppendsAcc ms [O] in
  rewrite plusDashAppendsAcc (succ' ms []) ns O [I] in
  rewrite sym $ jPlusIsSucc ms in
  rewrite sym $ jPlusIsSucc (plus' ms ns O []) in
  rewrite plusAssociative J ms ns in Refl
plusAssociative (ls -: O) J         (ns -: O) = Refl
plusAssociative (ls -: O) J         (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  rewrite plusDashAppendsAcc ls (succ' ns []) O [O] in
  rewrite sym $ plusJIsSucc ns in
  rewrite sym $ succGoesToCarry ls ns [O] in
  rewrite succDashAppendsAcc (plus' ls ns O []) [O] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusAssociative ls ns J in Refl
plusAssociative (ls -: I) J         (ns -: O) =
  rewrite sym $ succGoesToCarry ls ns [O] in
  rewrite succDashAppendsAcc (plus' ls ns O []) [O] in
  rewrite sym $ jPlusIsSucc (plus' ls ns O []) in
  rewrite succDashAppendsAcc ls [O] in
  rewrite plusDashAppendsAcc (succ' ls []) ns O [O] in
  rewrite sym $ jPlusIsSucc ls in
  rewrite plusAssociative J ls ns in Refl
plusAssociative (ls -: I) J         (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  rewrite plusDashAppendsAcc ls (succ' ns []) O [I] in
  rewrite sym $ jPlusIsSucc ns in
  rewrite succDashAppendsAcc ls [O] in
  rewrite plusDashAppendsAcc (succ' ls []) ns O [I] in
  rewrite sym $ plusJIsSucc ls in
  rewrite plusAssociative ls J ns in Refl
plusAssociative (ls -: O) (ns -: O) J         =
  rewrite plusDashAppendsAcc ls ns O [O] in
  rewrite plusDashAppendsAcc ls ns O [I] in Refl
plusAssociative (ls -: O) (ns -: I) J         =
  rewrite succDashAppendsAcc ns [O] in
  rewrite sym $ plusJIsSucc ns in
  rewrite plusDashAppendsAcc ls (plus' ns J O []) O [O] in
  rewrite plusDashAppendsAcc ls ns O [I] in
  rewrite succDashAppendsAcc (plus' ls ns O []) [O] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusAssociative ls ns J in Refl
plusAssociative (ls -: I) (ns -: O) J         =
  rewrite plusDashAppendsAcc ls ns I [O] in
  rewrite sym $ succGoesToCarry ls ns [] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusDashAppendsAcc ls ns O [I] in
  rewrite succDashAppendsAcc (plus' ls ns O []) [O] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in Refl
plusAssociative (ls -: I) (ns -: I) J         =
  rewrite succDashAppendsAcc ns [O] in
  rewrite plusDashAppendsAcc ls (succ' ns []) O [I] in
  rewrite sym $ plusJIsSucc ns in
  rewrite plusDashAppendsAcc ls ns I [O] in
  rewrite sym $ succGoesToCarry ls ns [] in
  rewrite sym $ plusJIsSucc (plus' ls ns O []) in
  rewrite plusAssociative ls ns J in Refl
plusAssociative (ls -: O) (ms -: O) (ns -: O) =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite plusDashAppendsAcc ls (plus' ms ns O []) O [O] in
  rewrite plusDashAppendsAcc ls ms O [O] in
  rewrite plusDashAppendsAcc (plus' ls ms O []) ns O [O] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: O) (ms -: O) (ns -: I) =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite plusDashAppendsAcc ls (plus' ms ns O []) O [I] in
  rewrite plusDashAppendsAcc ls ms O [O] in
  rewrite plusDashAppendsAcc (plus' ls ms O []) ns O [I] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: O) (ms -: I) (ns -: O) =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite plusDashAppendsAcc ls (plus' ms ns O []) O [I] in
  rewrite plusDashAppendsAcc ls ms O [I] in
  rewrite plusDashAppendsAcc (plus' ls ms O []) ns O [I] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: O) (ms -: I) (ns -: I) =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite plusDashAppendsAcc ls ms O [I] in
  rewrite sym $ succGoesToCarry (plus' ls ms O []) ns [O] in
  rewrite sym $ plusAssociative ls ms ns in
  rewrite succDashCommutesToPlusDashSnd ls (plus' ms ns O []) [O] in Refl
plusAssociative (ls -: I) (ms -: O) (ns -: O) =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite plusDashAppendsAcc ls (plus' ms ns O []) O [I] in
  rewrite plusDashAppendsAcc ls ms O [I] in
  rewrite plusDashAppendsAcc (plus' ls ms O []) ns O [I] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: I) (ms -: O) (ns -: I) =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite sym $ succGoesToCarry ls (plus' ms ns O []) [O] in
  rewrite plusDashAppendsAcc ls ms O [I] in
  rewrite sym $ succGoesToCarry (plus' ls ms O []) ns [O] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: I) (ms -: I) (ns -: O) =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite sym $ succGoesToCarry ls (plus' ms ns O []) [O] in
  rewrite plusDashAppendsAcc ls ms I [O] in
  rewrite sym $ succGoesToCarry ls ms [] in
  rewrite sym $ succDashCommutesToPlusDashFst (plus' ls ms O []) ns [O] in
  rewrite plusAssociative ls ms ns in Refl
plusAssociative (ls -: I) (ms -: I) (ns -: I) =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite sym $ succDashCommutesToPlusDashSnd ls (plus' ms ns O []) [I] in
  rewrite plusDashAppendsAcc ls ms I [O] in
  rewrite sym $ succGoesToCarry ls ms [] in
  rewrite sym $ succDashCommutesToPlusDashFst (plus' ls ms O []) ns [I] in
  rewrite plusAssociative ls ms ns in Refl

shiftLeftDoubles : (n : BiNat) -> n -: O = plus n n
shiftLeftDoubles J         = Refl
shiftLeftDoubles (ns -: O) =
  rewrite plusDashAppendsAcc ns ns O [O] in
  rewrite shiftLeftDoubles ns in Refl
shiftLeftDoubles (ns -: I) =
  rewrite plusDashAppendsAcc ns ns I [O] in
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
succIsNotJ (ns -: I) eq = uninhabited $ replace {P = \z => z = J} (succDashAppendsAcc ns [O]) eq

predOfDoubled : (n : BiNat) -> Not (n = J) -> pred (n -: O) = pred n -: I
predOfDoubled J notJ = absurd $ notJ Refl
predOfDoubled (ns -: O) _ = predDashAppendsAcc (ns -: O) [I]
predOfDoubled (ns -: I) _ = Refl

predCommutesToPlusSnd : (m : BiNat) -> (n : BiNat) -> Not (n = J) ->
  pred (plus m n) = plus m (pred n)
predCommutesToPlusSnd J         n notJ =
  rewrite jPlusIsSucc n in
  rewrite predOfSucc n in
  rewrite jPlusIsSucc (pred n) in
  rewrite succOfPred n notJ in Refl
predCommutesToPlusSnd (ms -: m) n notJ =
  rewrite sym $ succOfPred (ms -: m) uninhabited in
  rewrite sym $ jPlusIsSucc (pred (ms -: m)) in
  rewrite sym $ plusAssociative J (pred (ms -: m)) n in
  rewrite jPlusIsSucc (plus (pred (ms -: m)) n) in
  rewrite predOfSucc (plus (pred (ms -: m)) n) in
  rewrite plusSymmetric J (pred (ms -: m)) in
  rewrite sym $ plusAssociative (pred (ms -: m)) J (pred n) in
  rewrite jPlusIsSucc (pred n) in
  rewrite succOfPred n notJ in Refl

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
  rewrite sym $ plusDashAppendsAcc m n O [O] in
  multDistributesPlusRight ls (m -: O) (n -: O)
multDistributesPlusRight (ls -: I) m n =
  rewrite plusJIsSucc (plus' m n O []) in
  rewrite multDashAddsAccMinusJ ls (plus' m n O [] -: O) (succ (plus' m n O [])) in
  rewrite predCommutesToPlusSnd (mult ls (plus m n -: O)) (succ (plus m n)) (succIsNotJ (plus m n)) in
  rewrite predOfSucc (plus m n) in
  rewrite sym $ plusDashAppendsAcc m n O [O] in
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
  rewrite plusDashAppendsAcc ns J O [O] in
  rewrite plusJIsSucc ns in
  rewrite predOfDoubled (succ ns) (succIsNotJ ns) in
  rewrite predOfSucc ns in Refl

jMultIsId : (n : BiNat) -> mult J n = n
jMultIsId J = Refl
jMultIsId (ns -: O) = Refl
jMultIsId (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
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

multSymmetric : (m : BiNat) -> (n : BiNat) -> mult m n = mult n m
multSymmetric m n =
  induction
    (\k => mult k n = mult n k)
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite multDistributesPlusLeft k J n in
      rewrite multDistributesPlusRight n k J in
      rewrite plusJIsSucc n in
      rewrite predOfSucc n in
      rewrite multJIsId n in
      rewrite pk in Refl
    )
    (
      rewrite plusJIsSucc n in
      rewrite predOfSucc n in
      rewrite multJIsId n in Refl
    )
    m

multAssociative : (l : BiNat) -> (m : BiNat) -> (n : BiNat) ->
  mult l (mult m n) = mult (mult l m) n
multAssociative l m n =
  induction
    (\k => mult k (mult m n) = mult (mult k m) n)
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite multDistributesPlusLeft k J (mult m n) in
      rewrite jMultIsId (mult m n) in
      rewrite multDistributesPlusLeft k J m in
      rewrite jMultIsId m in
      rewrite multDistributesPlusLeft (mult k m) m n in
      rewrite pk in Refl
    )
    (
      rewrite jMultIsId (mult m n) in
      rewrite jMultIsId m in Refl
    )
    l

||| Proofs that a BiNat is less than another BiNat.
data LT : BiNat -> BiNat -> Type where
  JLT : (ns : BiNat) -> (n : Bit) -> LT J (ns -: n)
  LTLeading : (ns : BiNat) -> LT (ns -: O) (ns -: I)
  LTAppend : (ms, ns : BiNat) -> LT ms ns -> (m, n : Bit) -> LT (ms -: m) (ns -: n)

Uninhabited (LT n J) where
  uninhabited JLT       impossible
  uninhabited LTLeading impossible
  uninhabited LTAppend  impossible

nIsNotLessThanItself : (n : BiNat) -> Not (LT n n)
nIsNotLessThanItself J         lt = uninhabited {t = LT J J} lt
nIsNotLessThanItself (ns -: n) (JLT ms m) impossible
nIsNotLessThanItself (ns -: n) (LTLeading m) impossible
nIsNotLessThanItself (ns -: n) (LTAppend ns ns lt n n) = nIsNotLessThanItself ns lt

lessThanImpliesNotEqual : (m : BiNat) -> (n : BiNat) -> LT m n -> Not (m = n)
lessThanImpliesNotEqual m n lt eq = nIsNotLessThanItself n $ replace {P = \z => LT z n} eq lt

lessThanImpliesNotGreaterThan : (m : BiNat) -> (n : BiNat) -> LT m n -> Not (LT n m)
lessThanImpliesNotGreaterThan J         (ns -: n) (JLT ns n) lt = uninhabited lt
lessThanImpliesNotGreaterThan (ms -: O) (ms -: I) (LTLeading ms) (LTAppend ms ms lt I O) = nIsNotLessThanItself ms lt
lessThanImpliesNotGreaterThan (ms -: I) (ms -: O) (LTAppend ms ms lt I O) (LTLeading ms) = nIsNotLessThanItself ms lt
lessThanImpliesNotGreaterThan (ms -: m) (ns -: n) (LTAppend ms ns lt1 m n) (LTAppend ns ms lt2 n m) =
  lessThanImpliesNotGreaterThan ms ns lt1 lt2

lessThanTransitive : BiNat.Properties.LT l m -> BiNat.Properties.LT m n -> BiNat.Properties.LT l n
lessThanTransitive (JLT ms O)               (LTLeading ms)           = JLT ms I
lessThanTransitive (JLT ms m)               (LTAppend ms ns lt m n)  = JLT ns n
lessThanTransitive (LTLeading ls)           (LTAppend ls ns lt I n)  = LTAppend ls ns lt O n
lessThanTransitive (LTAppend ls ms lt l O)  (LTLeading ms)           = LTAppend ls ms lt l I
lessThanTransitive (LTAppend ls ms lt1 l m) (LTAppend ms ns lt2 m n) = LTAppend ls ns (lessThanTransitive lt1 lt2) l n

data LTE : BiNat -> BiNat -> Type where
  LTEEqual : (n : BiNat) -> LTE n n
  LTELessThan : (m : BiNat) -> (n : BiNat) -> LT m n -> LTE m n

lessThanEqualTransitive : BiNat.Properties.LTE l m -> BiNat.Properties.LTE m n -> BiNat.Properties.LTE l n
lessThanEqualTransitive (LTEEqual l)          (LTEEqual l)          = LTEEqual l
lessThanEqualTransitive (LTELessThan l m lt1) (LTEEqual m)          = LTELessThan l m lt1
lessThanEqualTransitive (LTEEqual l)          (LTELessThan l n lt2) = LTELessThan l n lt2
lessThanEqualTransitive (LTELessThan l m lt1) (LTELessThan m n lt2) = LTELessThan l n (lessThanTransitive lt1 lt2)

lessThanEqualAntiSymmetric : (m, n : BiNat) -> BiNat.Properties.LTE m n -> BiNat.Properties.LTE n m -> m = n
lessThanEqualAntiSymmetric m m (LTEEqual m)          (LTEEqual m)          = Refl
lessThanEqualAntiSymmetric m m (LTEEqual m)          (LTELessThan m m lt2) = absurd $ nIsNotLessThanItself m lt2
lessThanEqualAntiSymmetric m m (LTELessThan m m lt1) (LTEEqual m)          = absurd $ nIsNotLessThanItself m lt1
lessThanEqualAntiSymmetric m n (LTELessThan m n lt1) (LTELessThan n m lt2) = absurd $ lessThanImpliesNotGreaterThan m n lt1 lt2
