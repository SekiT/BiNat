module BiNat.Properties.Minus

import BiNat
import BiNat.Properties.Plus
import BiNat.Properties.Induction
import BiNat.Properties.LT

%access public export
%default total

minusLast00 : (ms : BiNat) -> (ns : BiNat) -> (tail : List Bit) ->
  minus' (ms -: O) (ns -: O) tail = minus' ms ns (O :: tail)
minusLast00 J         J         tail = Refl
minusLast00 J         (ns -: O) tail = Refl
minusLast00 J         (ns -: I) tail = Refl
minusLast00 (ms -: O) J         tail = Refl
minusLast00 (ms -: I) J         tail = Refl
minusLast00 (ms -: O) (ns -: O) tail = Refl
minusLast00 (ms -: O) (ns -: I) tail = Refl
minusLast00 (ms -: I) (ns -: O) tail = Refl
minusLast00 (ms -: I) (ns -: I) tail = Refl

minusLast10 : (ms : BiNat) -> (ns : BiNat) -> (tail : List Bit) ->
  minus' (ms -: I) (ns -: O) tail = minus' ms ns (I :: tail)
minusLast10 J         J         tail = Refl
minusLast10 J         (ns -: O) tail = Refl
minusLast10 J         (ns -: I) tail = Refl
minusLast10 (ms -: O) J         tail = Refl
minusLast10 (ms -: I) J         tail = Refl
minusLast10 (ms -: O) (ns -: O) tail = Refl
minusLast10 (ms -: O) (ns -: I) tail = Refl
minusLast10 (ms -: I) (ns -: O) tail = Refl
minusLast10 (ms -: I) (ns -: I) tail = Refl

minusLast11 : (ms : BiNat) -> (ns : BiNat) -> (tail : List Bit) ->
  minus' (ms -: I) (ns -: I) tail = minus' ms ns (O :: tail)
minusLast11 J         J         tail = Refl
minusLast11 J         (ns -: O) tail = Refl
minusLast11 J         (ns -: I) tail = Refl
minusLast11 (ms -: O) J         tail = Refl
minusLast11 (ms -: I) J         tail = Refl
minusLast11 (ms -: O) (ns -: O) tail = Refl
minusLast11 (ms -: O) (ns -: I) tail = Refl
minusLast11 (ms -: I) (ns -: O) tail = Refl
minusLast11 (ms -: I) (ns -: I) tail = Refl

minusLast01 : (ms : BiNat) -> (ns : BiNat) -> (tail : List Bit) -> Not (ms = J) ->
  minus' (ms -: O) (ns -: I) tail = minus' (pred ms) ns (I :: tail)
minusLast01 J         ns         tail notJ = absurd (notJ Refl)
minusLast01 (ms -: O) J          tail _    = Refl
minusLast01 (ms -: I) J          tail _    = Refl
minusLast01 (ms -: O) (ns -: O)  tail _    = Refl
minusLast01 (ms -: O) (ns -: I)  tail _    = Refl
minusLast01 (ms -: I) (ns -: O)  tail _    = Refl
minusLast01 (ms -: I) (ns -: I)  tail _    = Refl

minusLast0J : (ms : BiNat) -> (tail : List Bit) -> Not (ms = J) ->
  minus' (ms -: O) J tail = foldl (-:) (pred ms -: I) tail
minusLast0J J         tail notJ = absurd (notJ Refl)
minusLast0J (ms -: O) tail _    = Refl
minusLast0J (ms -: I) tail _    = Refl

minusLast1J : (ms : BiNat) -> (tail : List Bit) -> Not (ms = J) ->
  minus' (ms -: I) J tail = foldl (-:) (ms -: O) tail
minusLast1J J         tail notJ = absurd (notJ Refl)
minusLast1J (ms -: O) tail _    = Refl
minusLast1J (ms -: I) tail _    = Refl

minusJIsPred : (n : BiNat) -> minus n J = pred n
minusJIsPred J              = Refl
minusJIsPred (J -: O)       = Refl
minusJIsPred (ns -: n -: O) = rewrite predDashAppendsAcc (ns -: n) [I] in Refl
minusJIsPred (J -: I)       = Refl
minusJIsPred (ns -: n -: I) = Refl

minusOfItSelf : (n : BiNat) -> (tail : List Bit) -> minus' n n tail = tailToBiNat tail
minusOfItSelf J              tail = Refl
minusOfItSelf (J -: O)       tail = Refl
minusOfItSelf (ns -: O -: O) tail = rewrite minusOfItSelf (ns -: O) (O :: tail) in Refl
minusOfItSelf (ns -: I -: O) tail = rewrite minusOfItSelf (ns -: I) (O :: tail) in Refl
minusOfItSelf (J -: I)       tail = Refl
minusOfItSelf (ns -: O -: I) tail = rewrite minusOfItSelf (ns -: O) (O :: tail) in Refl
minusOfItSelf (ns -: I -: I) tail = rewrite minusOfItSelf (ns -: I) (O :: tail) in Refl

minusDashAppendsTail : (m : BiNat) -> (n : BiNat) -> LT n m -> (tail : List Bit) ->
  minus' m n tail = foldl (-:) (minus' m n []) tail
minusDashAppendsTail J              n              lt tail impossible
minusDashAppendsTail (J -: O)       J              lt tail = Refl
minusDashAppendsTail (ms -: m -: O) J              lt tail = Refl
minusDashAppendsTail (J -: I)       J              lt tail = Refl
minusDashAppendsTail (ms -: m -: I) J              lt tail = Refl
minusDashAppendsTail (ms -: O)      (ns -: O) (LTAppend ns ms lt O O) tail =
  rewrite minusLast00 ms ns tail in
  rewrite minusLast00 ms ns [] in
  rewrite minusDashAppendsTail ms ns lt (O :: tail) in
  rewrite minusDashAppendsTail ms ns lt [O] in Refl
minusDashAppendsTail (J -: O)       (ns -: I)      (LTAppend ns J lt I O) tail impossible
minusDashAppendsTail (ms -: m -: O) (J -: I)       (LTAppend J (ms -: m) lt I O) tail =
  case decomposeLTE $ lessThanImpliesLTEPred J (ms -: m) lt of
    Left eq   =>
      rewrite sym $ eq in Refl
    Right lt2 =>
      rewrite minusDashAppendsTail (pred (ms -: m)) J lt2 (I :: tail) in
      rewrite minusDashAppendsTail (pred (ms -: m)) J lt2 [I] in Refl
minusDashAppendsTail (ms -: m -: O) (ns -: n -: I) (LTAppend (ns -: n) (ms -: m) lt I O) tail =
  case decomposeLTE $ lessThanImpliesLTEPred (ns -: n) (ms -: m) lt of
    Left eq   =>
      rewrite sym $ eq in
      rewrite minusOfItSelf (ns -: n) (I :: tail) in
      rewrite minusOfItSelf (ns -: n) [I] in Refl
    Right lt2 =>
      rewrite minusDashAppendsTail (pred (ms -: m)) (ns -: n) lt2 (I :: tail) in
      rewrite minusDashAppendsTail (pred (ms -: m)) (ns -: n) lt2 [I] in Refl
minusDashAppendsTail (ms -: I)      (ms -: O)      (LTLeading ms) tail =
  rewrite minusLast10 ms ms tail in
  rewrite minusLast10 ms ms [] in
  case ms of
    J          => Refl
    (ms2 -: m) =>
      rewrite minusOfItSelf (ms2 -: m) (I :: tail) in
      rewrite minusOfItSelf (ms2 -: m) [I] in Refl
minusDashAppendsTail (ms -: m -: I) (ns -: O)      (LTAppend ns (ms -: m) lt O I) tail =
  rewrite minusDashAppendsTail (ms -: m) ns lt (I :: tail) in
  rewrite minusDashAppendsTail (ms -: m) ns lt [I] in Refl
minusDashAppendsTail (J -: I)       (ns -: I)      (LTAppend ns J lt I I) tail impossible
minusDashAppendsTail (ms -: m -: I) (ns -: I)      (LTAppend ns (ms -: m) lt I I) tail =
  rewrite minusDashAppendsTail (ms -: m) ns lt (O :: tail) in
  rewrite minusDashAppendsTail (ms -: m) ns lt [O] in Refl

plusNMinusN : (m : BiNat) -> (n : BiNat) -> minus (plus m n) n = m
plusNMinusN J              J              = Refl
plusNMinusN J              (J -: O)       = Refl
plusNMinusN J              (ns -: O -: O) = minusOfItSelf (ns -: O) [I]
plusNMinusN J              (ns -: I -: O) = minusOfItSelf (ns -: I) [I]
plusNMinusN J              (J -: I)       = Refl
plusNMinusN J              (ns -: O -: I) = minusOfItSelf (ns -: O) [I]
plusNMinusN J              (ns -: I -: I) =
  rewrite succDashAppendsAcc ns [O, O] in
  rewrite predOfDoubled (succ ns) (succIsNotJ ns) in
  rewrite predOfSucc ns in
  rewrite minusOfItSelf (ns -: I) [I] in Refl
plusNMinusN (J -: O)       J              = Refl
plusNMinusN (ms -: O -: O) J              = Refl
plusNMinusN (ms -: I -: O) J              = Refl
plusNMinusN (J -: I)       J              = Refl
plusNMinusN (ms -: O -: I) J              = Refl
plusNMinusN (ms -: I -: I) J              =
  rewrite succDashAppendsAcc ms [O, O] in
  rewrite predOfDoubled (succ ms) (succIsNotJ ms) in
  rewrite predOfSucc ms in Refl
plusNMinusN (ms -: O)      (ns -: O)      =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite minusLast00 (plus ms ns) ns [] in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [O] in
  rewrite plusNMinusN ms ns in Refl
plusNMinusN (ms -: O)      (ns -: I)      =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite minusLast11 (plus ms ns) ns [] in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [O] in
  rewrite plusNMinusN ms ns in Refl
plusNMinusN (ms -: I)      (ns -: O)      =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite minusLast10 (plus ms ns) ns [] in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [I] in
  rewrite plusNMinusN ms ns in Refl
plusNMinusN (ms -: I)      (ns -: I)      =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite minusLast01 (succ (plus ms ns)) ns [] (succIsNotJ (plus ms ns)) in
  rewrite predOfSucc (plus ms ns) in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [I] in
  rewrite plusNMinusN ms ns in Refl

minusNPlusN : (m : BiNat) -> (n : BiNat) -> LT n m -> plus (minus m n) n = m
minusNPlusN m n =
  induction
    (\k => LT n k -> plus (minus k n) n = k)
    (\k, pk, lt =>
      case decomposeLTE $ lessThanImpliesLTEPred n (succ k) lt of
        Left eq =>
          rewrite eq in
          rewrite predOfSucc k in
          rewrite sym $ jPlusIsSucc k in
          rewrite plusNMinusN J k in Refl
        Right lt2 =>
          let pk' = pk (replace {P = \z => LT n z} (predOfSucc k) lt2) in
          replace {P = \z => plus (minus (succ z) n) n = succ k} pk' $
          rewrite sym $ jPlusIsSucc (plus (minus k n) n) in
          rewrite plusAssociative J (minus k n) n in
          rewrite plusNMinusN (plus J (minus k n)) n in
          rewrite sym $ plusAssociative J (minus k n) n in
          rewrite pk' in jPlusIsSucc k
    )
    (\lt => absurd (uninhabited lt))
    m

succIntoMinus : (m, n : BiNat) -> LT n m -> succ (minus m n) = minus (succ m) n
succIntoMinus m n lt =
  induction
    (\k => LT n k -> succ (minus k n) = minus (succ k) n)
    (\k, pk, ltSucc =>
      case decomposeLTE $ lessThanImpliesLTEPred n (succ k) ltSucc of
        Left eq =>
          rewrite eq in
          rewrite predOfSucc k in
          rewrite sym $ jPlusIsSucc k in
          rewrite plusNMinusN J k in
          rewrite sym $ jPlusIsSucc (plus J k) in
          rewrite plusAssociative J J k in
          rewrite plusNMinusN (J -: O) k in Refl
        Right lt =>
          rewrite sym $ minusNPlusN (succ k) n ltSucc in
          rewrite sym $ jPlusIsSucc (plus (minus (succ k) n) n) in
          rewrite plusAssociative J (minus (succ k) n) n in
          rewrite plusNMinusN (plus J (minus (succ k) n)) n in
          rewrite jPlusIsSucc (minus (succ k) n) in
          rewrite plusNMinusN (minus (succ k) n) n in Refl
    )
    (absurd . uninhabited)
    m lt
