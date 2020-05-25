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

minusOfItSelf : (ns : BiNat) -> (n : Bit) -> (tail : List Bit) ->
  minus' (ns -: n) (ns -: n) tail = tailToBiNat tail
minusOfItSelf J         O tail = Refl
minusOfItSelf (ns -: O) O tail = rewrite minusOfItSelf ns O (O :: tail) in Refl
minusOfItSelf (ns -: I) O tail = rewrite minusOfItSelf ns I (O :: tail) in Refl
minusOfItSelf J         I tail = Refl
minusOfItSelf (ns -: O) I tail = rewrite minusOfItSelf ns O (O :: tail) in Refl
minusOfItSelf (ns -: I) I tail = rewrite minusOfItSelf ns I (O :: tail) in Refl

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
      rewrite minusOfItSelf ns n (I :: tail) in
      rewrite minusOfItSelf ns n [I] in Refl
    Right lt2 =>
      rewrite minusDashAppendsTail (pred (ms -: m)) (ns -: n) lt2 (I :: tail) in
      rewrite minusDashAppendsTail (pred (ms -: m)) (ns -: n) lt2 [I] in Refl
minusDashAppendsTail (ms -: I)      (ms -: O)      (LTLeading ms) tail =
  rewrite minusLast10 ms ms tail in
  rewrite minusLast10 ms ms [] in
  case ms of
    J          => Refl
    (ms2 -: m) =>
      rewrite minusOfItSelf ms2 m (I :: tail) in
      rewrite minusOfItSelf ms2 m [I] in Refl
minusDashAppendsTail (ms -: m -: I) (ns -: O)      (LTAppend ns (ms -: m) lt O I) tail =
  rewrite minusDashAppendsTail (ms -: m) ns lt (I :: tail) in
  rewrite minusDashAppendsTail (ms -: m) ns lt [I] in Refl
minusDashAppendsTail (J -: I)       (ns -: I)      (LTAppend ns J lt I I) tail impossible
minusDashAppendsTail (ms -: m -: I) (ns -: I)      (LTAppend ns (ms -: m) lt I I) tail =
  rewrite minusDashAppendsTail (ms -: m) ns lt (O :: tail) in
  rewrite minusDashAppendsTail (ms -: m) ns lt [O] in Refl

minusOfPlus : (m : BiNat) -> (n : BiNat) -> minus (plus m n) n = m
minusOfPlus J              J              = Refl
minusOfPlus J              (J -: O)       = Refl
minusOfPlus J              (ns -: O -: O) = minusOfItSelf ns O [I]
minusOfPlus J              (ns -: I -: O) = minusOfItSelf ns I [I]
minusOfPlus J              (J -: I)       = Refl
minusOfPlus J              (ns -: O -: I) = minusOfItSelf ns O [I]
minusOfPlus J              (ns -: I -: I) =
  rewrite succDashAppendsAcc ns [O, O] in
  rewrite predOfDoubled (succ ns) (succIsNotJ ns) in
  rewrite predOfSucc ns in
  rewrite minusOfItSelf ns I [I] in Refl
minusOfPlus (J -: O)       J              = Refl
minusOfPlus (ms -: O -: O) J              = Refl
minusOfPlus (ms -: I -: O) J              = Refl
minusOfPlus (J -: I)       J              = Refl
minusOfPlus (ms -: O -: I) J              = Refl
minusOfPlus (ms -: I -: I) J              =
  rewrite succDashAppendsAcc ms [O, O] in
  rewrite predOfDoubled (succ ms) (succIsNotJ ms) in
  rewrite predOfSucc ms in Refl
minusOfPlus (ms -: O)      (ns -: O)      =
  rewrite plusDashAppendsAcc ms ns O [O] in
  rewrite minusLast00 (plus ms ns) ns [] in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [O] in
  rewrite minusOfPlus ms ns in Refl
minusOfPlus (ms -: O)      (ns -: I)      =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite minusLast11 (plus ms ns) ns [] in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [O] in
  rewrite minusOfPlus ms ns in Refl
minusOfPlus (ms -: I)      (ns -: O)      =
  rewrite plusDashAppendsAcc ms ns O [I] in
  rewrite minusLast10 (plus ms ns) ns [] in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [I] in
  rewrite minusOfPlus ms ns in Refl
minusOfPlus (ms -: I)      (ns -: I)      =
  rewrite plusDashAppendsAcc ms ns I [O] in
  rewrite sym $ succGoesToCarry ms ns [] in
  rewrite minusLast01 (succ (plus ms ns)) ns [] (succIsNotJ (plus ms ns)) in
  rewrite predOfSucc (plus ms ns) in
  rewrite minusDashAppendsTail (plus ms ns) ns (lessThanPlus ns ms) [I] in
  rewrite minusOfPlus ms ns in Refl

plusOfMinus : (m : BiNat) -> (n : BiNat) -> LT n m -> plus (minus m n) n = m
plusOfMinus m n =
  induction
    (\k => LT n k -> plus (minus k n) n = k)
    (\k, pk, lt =>
      case decomposeLTE $ lessThanImpliesLTEPred n (succ k) lt of
        Left eq =>
          rewrite eq in
          rewrite predOfSucc k in
          rewrite sym $ jPlusIsSucc k in
          rewrite minusOfPlus J k in Refl
        Right lt2 =>
          let pk' = pk (replace {P = \z => LT n z} (predOfSucc k) lt2) in
          replace {P = \z => plus (minus (succ z) n) n = succ k} pk' $
          rewrite sym $ jPlusIsSucc (plus (minus k n) n) in
          rewrite plusAssociative J (minus k n) n in
          rewrite minusOfPlus (plus J (minus k n)) n in
          rewrite sym $ plusAssociative J (minus k n) n in
          rewrite pk' in jPlusIsSucc k
    )
    (\lt => absurd (uninhabited lt))
    m
