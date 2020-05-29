module BiNat.Properties.Mult

import BiNat
import BiNat.Properties.Plus
import BiNat.Properties.Induction
import BiNat.Properties.LT

%access public export
%default total

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

appendOIsTwice : (n : BiNat) -> n -: O = mult n (J -: O)
appendOIsTwice n =
  induction
    (\k => k -: O = mult k (J -: O))
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite multDistributesPlusLeft k J (J -: O) in
      rewrite sym pk in
      sym $ plusDashAppendsAcc k J O [O]
    )
    Refl
    n

appendIIsTwicePlusJ : (n : BiNat) -> n -: I = plus (mult n (J -: O)) J
appendIIsTwicePlusJ n = rewrite sym $ appendOIsTwice n in Refl

multNKeepsLT : (l, m : BiNat) -> LT l m -> (n : BiNat) -> LT (mult l n) (mult m n)
multNKeepsLT l m lt n =
  induction
    (\k => LT (mult l k) (mult m k))
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite multDistributesPlusRight l k J in
      rewrite multDistributesPlusRight m k J in
      rewrite multJIsId l in
      rewrite multJIsId m in
      lessThanTransitive
        (plusNKeepsLessThan (mult l k) (mult m k) pk l)
        (
          rewrite plusSymmetric (mult m k) l in
          rewrite plusSymmetric (mult m k) m in
          plusNKeepsLessThan l m lt (mult m k)
        )
    )
    (rewrite multJIsId l in rewrite multJIsId m in lt)
    n
