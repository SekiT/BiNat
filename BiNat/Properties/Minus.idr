module BiNat.Properties.Minus

import BiNat
import BiNat.Properties.Plus
import BiNat.Properties.Induction
import BiNat.Properties.LT

%access public export
%default total

minusLast00 : (ms, ns : BiNat) -> (tail : List Bit) ->
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

minusLast10 : (ms, ns : BiNat) -> (tail : List Bit) ->
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

minusLast11 : (ms, ns : BiNat) -> (tail : List Bit) ->
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

minusLast01 : (ms, ns : BiNat) -> (tail : List Bit) -> Not (ms = J) ->
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

jMinusIsJ : (n : BiNat) -> minus J n = J
jMinusIsJ J         = Refl
jMinusIsJ (ns -: n) = Refl

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

minusDashAppendsTail : (m, n : BiNat) -> GT m n -> (tail : List Bit) ->
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
  case lessThanImpliesLTEPred J (ms -: m) lt of
    LTEEqual _ _ eq =>
      rewrite sym $ eq in Refl
    LTELessThan _ _ lt2 =>
      rewrite minusDashAppendsTail (pred (ms -: m)) J lt2 (I :: tail) in
      rewrite minusDashAppendsTail (pred (ms -: m)) J lt2 [I] in Refl
minusDashAppendsTail (ms -: m -: O) (ns -: n -: I) (LTAppend (ns -: n) (ms -: m) lt I O) tail =
  case lessThanImpliesLTEPred (ns -: n) (ms -: m) lt of
    LTEEqual _ _ eq =>
      rewrite sym $ eq in
      rewrite minusOfItSelf (ns -: n) (I :: tail) in
      rewrite minusOfItSelf (ns -: n) [I] in Refl
    LTELessThan _ _ lt2 =>
      rewrite minusDashAppendsTail (pred (ms -: m)) (ns -: n) lt2 (I :: tail) in
      rewrite minusDashAppendsTail (pred (ms -: m)) (ns -: n) lt2 [I] in Refl
minusDashAppendsTail (ms -: I)      (ns -: O)      (LTLeading ns ms eq) tail =
  rewrite eq in
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

plusNMinusN : (m, n : BiNat) -> minus (plus m n) n = m
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

minusNPlusN : (m, n : BiNat) -> GT m n -> plus (minus m n) n = m
minusNPlusN m n =
  induction
    (\k => LT n k -> plus (minus k n) n = k)
    (\k, pk, lt =>
      case lessThanImpliesLTEPred n (succ k) lt of
        LTEEqual _ _ eq =>
          rewrite eq in
          rewrite predOfSucc k in
          rewrite sym $ jPlusIsSucc k in
          rewrite plusNMinusN J k in Refl
        LTELessThan _ _ lt2 =>
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

succIntoMinus : (m, n : BiNat) -> GT m n -> succ (minus m n) = minus (succ m) n
succIntoMinus m n lt =
  induction
    (\k => LT n k -> succ (minus k n) = minus (succ k) n)
    (\k, pk, ltSucc =>
      case lessThanImpliesLTEPred n (succ k) ltSucc of
        LTEEqual _ _ eq =>
          rewrite eq in
          rewrite predOfSucc k in
          rewrite sym $ jPlusIsSucc k in
          rewrite plusNMinusN J k in
          rewrite sym $ jPlusIsSucc (plus J k) in
          rewrite plusAssociative J J k in
          rewrite plusNMinusN (J -: O) k in Refl
        LTELessThan _ _ lt =>
          rewrite sym $ minusNPlusN (succ k) n ltSucc in
          rewrite sym $ jPlusIsSucc (plus (minus (succ k) n) n) in
          rewrite plusAssociative J (minus (succ k) n) n in
          rewrite plusNMinusN (plus J (minus (succ k) n)) n in
          rewrite jPlusIsSucc (minus (succ k) n) in
          rewrite plusNMinusN (minus (succ k) n) n in Refl
    )
    (absurd . uninhabited)
    m lt

succNMinusNIsJ : (n : BiNat) -> minus (succ n) n = J
succNMinusNIsJ J         = Refl
succNMinusNIsJ (ns -: O) = rewrite minusLast10 ns ns [] in minusOfItSelf ns [I]
succNMinusNIsJ (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  rewrite minusLast01 (succ ns) ns [] (succIsNotJ ns) in
  rewrite predOfSucc ns in
  minusOfItSelf ns [I]

nMinusPredNIsJ : (n : BiNat) -> minus n (pred n) = J
nMinusPredNIsJ J              = Refl
nMinusPredNIsJ (J -: O)       = Refl
nMinusPredNIsJ (ns -: n -: O) = rewrite predDashAppendsAcc (ns -: n) [I] in minusOfItSelf (pred (ns -: n)) [I]
nMinusPredNIsJ (ns -: I)      = rewrite minusLast10 ns ns [] in minusOfItSelf ns [I]

minusIntoPlusLeft : (l, m, n : BiNat) -> GT l n -> minus (plus l m) n = plus (minus l n) m
minusIntoPlusLeft l m n lt =
  induction
    (\k => minus (plus l k) n = plus (minus l n) k)
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite plusAssociative l k J in
      rewrite plusJIsSucc (plus l k) in
      let nLtLPlusK = lessThanTransitive lt (replace (plusSymmetric k l) (lessThanPlus l k)) in
      rewrite sym $ succIntoMinus (plus l k) n nLtLPlusK in
      rewrite pk in
      rewrite sym $ plusJIsSucc (plus (minus l n) k5) in
      rewrite sym $ plusAssociative (minus l n) k J in Refl
    )
    (
      rewrite plusJIsSucc l in
      rewrite plusJIsSucc (minus l n) in
      sym $ succIntoMinus l n lt
    )
    m

minusIntoPlusRight : (l, m, n : BiNat) -> GT m n -> minus (plus l m) n = plus l (minus m n)
minusIntoPlusRight l m n lt =
  rewrite plusSymmetric l m in
  rewrite minusIntoPlusLeft m l n lt in
  plusSymmetric (minus m n) l

minusGreater : (m, n : BiNat) -> LT m n -> (tail : List Bit) -> minus' m n tail = J
minusGreater m              J         lt tail impossible
minusGreater J              (ns -: n) lt tail = Refl
minusGreater (ms -: O)      (ns -: O) (LTAppend ms ns lt O O) tail =
  rewrite minusLast00 ms ns tail in minusGreater ms ns lt (O :: tail)
minusGreater (ms -: I)      (ns -: O) (LTAppend ms ns lt I O) tail =
  rewrite minusLast10 ms ns tail in minusGreater ms ns lt (I :: tail)
minusGreater (ms -: I)      (ns -: I) (LTAppend ms ns lt I I) tail =
  rewrite minusLast11 ms ns tail in minusGreater ms ns lt (O :: tail)
minusGreater (J -: O)       (ns -: I) lt tail = Refl
minusGreater (ms -: m -: O) (ns -: I) (LTAppend (ms -: m) ns lt O I) tail =
  let lt2 = lessThanTransitive (predIsLessThan (ms -: m) (JLT ms m)) lt in
  minusGreater (pred (ms -: m)) ns lt2 (I :: tail)
minusGreater (ms -: m -: O) (ns -: I) (LTLeading (ms -: m) ns eq) tail =
  let lt = replace {P = \z => LT (pred (ms -: m)) z} eq (predIsLessThan (ms -: m) (JLT ms m)) in
  minusGreater (pred (ms -: m)) ns lt (I :: tail)

minusOfSuccs : (m, n : BiNat) -> minus m n = minus (succ m) (succ n)
minusOfSuccs J              J         = Refl
minusOfSuccs J              (ns -: O) = Refl
minusOfSuccs J              (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  rewrite minusGreater J (succ ns) (succGreaterThanJ ns) [O] in Refl
minusOfSuccs (J -: O)       J         = Refl
minusOfSuccs (ms -: m -: O) J         =
  rewrite minusDashAppendsTail (ms -: m) J (JLT ms m) [I] in
  rewrite minusJIsPred (ms -: m) in Refl
minusOfSuccs (J -: I)       J         = Refl
minusOfSuccs (ms -: m -: I) J         =
  rewrite succDashAppendsAcc (ms -: m) [O] in
  rewrite minusLast00 (succ (ms -: m)) J [] in
  rewrite minusDashAppendsTail (succ (ms -: m)) J (succGreaterThanJ (ms -: m)) [O] in
  rewrite minusJIsPred (succ (ms -: m)) in
  rewrite predOfSucc (ms -: m) in Refl
minusOfSuccs (ms -: O)      (ns -: O) = rewrite minusLast11 ms ns [] in minusLast00 ms ns []
minusOfSuccs (J -: O)       (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  sym $ minusGreater J (succ ns) (succGreaterThanJ ns) [I]
minusOfSuccs (ms -: m -: O) (ns -: I) =
  rewrite succDashAppendsAcc ns [O] in
  case lessThanOrGTE ns (pred (ms -: m)) of
    Left nLTpredm =>
      let succnLTm = replace {P = \z => LT (succ ns) z} (succOfPred (ms -: m) uninhabited) $
                     succKeepsLessThan ns (pred (ms -: m)) nLTpredm in
      rewrite minusDashAppendsTail (pred (ms -: m)) ns nLTpredm [I] in
      rewrite minusDashAppendsTail (ms -: m) (succ ns) succnLTm [I] in
      rewrite minusOfSuccs (pred (ms -: m)) ns in
      rewrite succOfPred (ms -: m) uninhabited in Refl
    Right (LTEEqual (pred (ms -: m)) ns eq) =>
      rewrite sym $ succOfPred (ms -: m) uninhabited in
      rewrite eq in
      rewrite predOfSucc ns in
      rewrite minusOfItSelf ns [I] in
      rewrite minusOfItSelf (succ ns) [I] in Refl
    Right (LTELessThan (pred (ms -: m)) ns predmLTn) =>
      let mLTsuccn = replace {P = \z => LT z (succ ns)} (succOfPred (ms -: m) uninhabited) $
                     succKeepsLessThan (pred (ms -: m)) ns predmLTn in
      rewrite minusGreater (pred (ms -: m)) ns predmLTn [I] in
      rewrite minusGreater (ms -: m) (succ ns) mLTsuccn [I] in Refl
minusOfSuccs (ms -: I)      (ns -: O) =
  rewrite minusLast10 ms ns [] in
  rewrite succDashAppendsAcc ms [O] in
  rewrite minusLast01 (succ ms) ns [] (succIsNotJ ms) in
  rewrite predOfSucc ms in Refl
minusOfSuccs (ms -: I)      (ns -: I) =
  rewrite minusLast11 ms ns [] in
  rewrite succDashAppendsAcc ms [O] in
  rewrite succDashAppendsAcc ns [O] in
  rewrite minusLast00 (succ ms) (succ ns) [] in
  case lessThanOrGTE ns ms of
    Left gt =>
      rewrite minusDashAppendsTail ms ns gt [O] in
      rewrite minusDashAppendsTail (succ ms) (succ ns) (succKeepsLessThan ns ms gt) [O] in
      rewrite minusOfSuccs ms ns in Refl
    Right (LTEEqual ms ns eq) =>
      rewrite eq in
      rewrite minusOfItSelf ns [O] in
      rewrite minusOfItSelf (succ ns) [O] in Refl
    Right (LTELessThan ms ns lt) =>
      rewrite minusGreater ms ns lt [O] in
      rewrite minusGreater (succ ms) (succ ns) (succKeepsLessThan ms ns lt) [O] in Refl

predIntoMinus' : (m, n : BiNat) -> GT m n -> pred (minus m n) = minus (pred m) n
predIntoMinus' m n gt = induction
  (\k => GT k n -> pred (minus k n) = minus (pred k) n)
  (\k, pk, nLTsucck =>
    case lessThanImpliesLTEPred n (succ k) nLTsucck of
      LTEEqual n (pred $ succ k) eq =>
        rewrite eq in
        rewrite predOfSucc k in
        rewrite succNMinusNIsJ k in
        rewrite minusOfItSelf k [] in Refl
      LTELessThan n (pred $ succ k) lt =>
        let nLTk = replace (predOfSucc k) lt in
        rewrite sym $ succIntoMinus k n nLTk in
        rewrite predOfSucc (minus k n) in
        rewrite predOfSucc k in Refl
  )
  (\gt => absurd $ uninhabited gt)
  m gt

predIntoMinus : (m, n : BiNat) -> pred (minus m n) = minus (pred m) n
predIntoMinus m n =
  case lessThanOrGTE n m of
    Left gt =>
      predIntoMinus' m n gt
    Right (LTEEqual m n eq) =>
      rewrite eq in
      rewrite minusOfItSelf n [] in
      case predLessThanEqual n of
        LTEEqual (pred n) n eq2 =>
          rewrite eq2 in
          sym $ minusOfItSelf n []
        LTELessThan (pred n) n lt =>
          rewrite minusGreater (pred n) n lt [] in Refl
    Right (LTELessThan m n lt) =>
      rewrite minusGreater m n lt [] in
      let predmLTn = transLTEandLT (predLessThanEqual m) lt in
      rewrite minusGreater (pred m) n predmLTn [] in Refl

predIntoMinusSucc : (m, n : BiNat) -> pred (minus m n) = minus m (succ n)
predIntoMinusSucc J         n = rewrite jMinusIsJ n in rewrite jMinusIsJ (succ n) in Refl
predIntoMinusSucc (ms -: m) n =
  rewrite predIntoMinus (ms -: m) n in
  rewrite minusOfSuccs (pred (ms -: m)) n in
  rewrite succOfPred (ms -: m) uninhabited in Refl
