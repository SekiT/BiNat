module BiNat.Properties.LT

import BiNat
import BiNat.Properties.Plus
import BiNat.Properties.Induction

%access public export
%default total

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

lessThanTransitive : BiNat.Properties.LT.LT l m -> LT m n -> LT l n
lessThanTransitive (JLT ms O)               (LTLeading ms)           = JLT ms I
lessThanTransitive (JLT ms m)               (LTAppend ms ns lt m n)  = JLT ns n
lessThanTransitive (LTLeading ls)           (LTAppend ls ns lt I n)  = LTAppend ls ns lt O n
lessThanTransitive (LTAppend ls ms lt l O)  (LTLeading ms)           = LTAppend ls ms lt l I
lessThanTransitive (LTAppend ls ms lt1 l m) (LTAppend ms ns lt2 m n) = LTAppend ls ns (lessThanTransitive lt1 lt2) l n

data LTE : BiNat -> BiNat -> Type where
  LTEEqual : (n : BiNat) -> LTE n n
  LTELessThan : (m : BiNat) -> (n : BiNat) -> LT m n -> LTE m n

lessThanEqualTransitive : BiNat.Properties.LT.LTE l m -> LTE m n -> LTE l n
lessThanEqualTransitive (LTEEqual l)          (LTEEqual l)          = LTEEqual l
lessThanEqualTransitive (LTELessThan l m lt1) (LTEEqual m)          = LTELessThan l m lt1
lessThanEqualTransitive (LTEEqual l)          (LTELessThan l n lt2) = LTELessThan l n lt2
lessThanEqualTransitive (LTELessThan l m lt1) (LTELessThan m n lt2) = LTELessThan l n (lessThanTransitive lt1 lt2)

lessThanEqualAntiSymmetric : (m, n : BiNat) -> LTE m n -> LTE n m -> m = n
lessThanEqualAntiSymmetric m m (LTEEqual m)          (LTEEqual m)          = Refl
lessThanEqualAntiSymmetric m m (LTEEqual m)          (LTELessThan m m lt2) = absurd $ nIsNotLessThanItself m lt2
lessThanEqualAntiSymmetric m m (LTELessThan m m lt1) (LTEEqual m)          = absurd $ nIsNotLessThanItself m lt1
lessThanEqualAntiSymmetric m n (LTELessThan m n lt1) (LTELessThan n m lt2) = absurd $ lessThanImpliesNotGreaterThan m n lt1 lt2

decomposeLTE : BiNat.Properties.LT.LTE m n -> Either (m = n) (LT m n)
decomposeLTE (LTEEqual m)         = Left Refl
decomposeLTE (LTELessThan m n lt) = Right lt

lessThanOrGTE : (m, n : BiNat) -> Either (LT m n) (LTE n m)
lessThanOrGTE J         J         = Right $ LTEEqual J
lessThanOrGTE J         (ns -: n) = Left $ JLT ns n
lessThanOrGTE (ms -: m) J         = Right $ LTELessThan J (ms -: m) (JLT ms m)
lessThanOrGTE (ms -: O) (ns -: O) =
  case lessThanOrGTE ms ns of
    Left lt   => Left (LTAppend ms ns lt O O)
    Right gte => case decomposeLTE gte of
      Left eq  => Right $ rewrite sym eq in LTEEqual (ns -: O)
      Right gt => Right $ LTELessThan (ns -: O) (ms -: O) (LTAppend ns ms gt O O)
lessThanOrGTE (ms -: O) (ns -: I) =
  case lessThanOrGTE ms ns of
    Left lt   => Left (LTAppend ms ns lt O I)
    Right gte => case decomposeLTE gte of
      Left eq  => Left $ rewrite eq in LTLeading ms
      Right gt => Right $ LTELessThan (ns -: I) (ms -: O) (LTAppend ns ms gt I O)
lessThanOrGTE (ms -: I) (ns -: O) =
  case lessThanOrGTE ms ns of
    Left lt   => Left (LTAppend ms ns lt I O)
    Right gte => case decomposeLTE gte of
      Left eq  => Right $ LTELessThan (ns -: O) (ms -: I) (rewrite sym eq in LTLeading ns)
      Right gt => Right $ LTELessThan (ns -: O) (ms -: I) (LTAppend ns ms gt O I)
lessThanOrGTE (ms -: I) (ns -: I) =
  case lessThanOrGTE ms ns of
    Left lt   => Left (LTAppend ms ns lt I I)
    Right gte => case decomposeLTE gte of
      Left eq  => Right $ rewrite sym eq in LTEEqual (ns -: I)
      Right gt => Right $ LTELessThan (ns -: I) (ms -: I) (LTAppend ns ms gt I I)

lessThanAppended : (n : BiNat) -> (b : Bit) -> LT n (n -: b)
lessThanAppended J         b = JLT J b
lessThanAppended (ns -: n) b = LTAppend ns (ns -: n) (lessThanAppended ns n) n b

lessThanSucc : (n : BiNat) -> LT n (succ n)
lessThanSucc J         = JLT J O
lessThanSucc (ns -: O) = LTLeading ns
lessThanSucc (ns -: I) =
  replace {P = \z => LT (ns -: I) z} (sym $ succDashAppendsAcc ns [O]) $
  LTAppend ns (succ ns) (lessThanSucc ns) I O

predIsLessThan : (n : BiNat) -> LT J n -> LT (pred n) n
predIsLessThan J _ impossible
predIsLessThan (J -: O)       _ = JLT J O
predIsLessThan (ns -: O -: O) _ =
  replace {P = \z => LT z (ns -: O -: O)} (sym $ predDashAppendsAcc (ns -: O) [I]) $
  LTAppend (pred (ns -: O)) (ns -: O) (predIsLessThan (ns -: O) (JLT ns O)) I O
predIsLessThan (ns -: I -: O) _ = LTAppend (ns -: O) (ns -: I) (LTLeading ns) I O
predIsLessThan (ns -: I)      _ = LTLeading ns

lessThanImpliesLTEPred : (m : BiNat) -> (n : BiNat) -> LT m n -> LTE m (pred n)
lessThanImpliesLTEPred m J lt impossible
lessThanImpliesLTEPred J (J -: O)       _ = LTEEqual J
lessThanImpliesLTEPred J (ns -: O -: O) _ =
  replace {P = \z => LTE J z} (sym $ predDashAppendsAcc (ns -: O) [I]) $
  LTELessThan J (pred (ns -: O) -: I) (JLT (pred (ns -: O)) I)
lessThanImpliesLTEPred J (ns -: I -: O) _ = LTELessThan J (ns -: O -: I) (JLT (ns -: O) I)
lessThanImpliesLTEPred J (ns -: I)      _ = LTELessThan J (ns -: O) (JLT ns O)
lessThanImpliesLTEPred (ms -: O) (ns -: O) (LTAppend ms ns lt O O) =
  case ns of
    J          => absurd (uninhabited lt)
    (ns2 -: n) =>
      replace {P = \z => LTE (ms -: O) z} (sym $ predDashAppendsAcc (ns2 -: n) [I]) $
      case decomposeLTE $ lessThanImpliesLTEPred ms (ns2 -: n) lt of
        Left eq =>
          replace {P = \z => LTE (ms -: O) (z -: I)} eq (LTELessThan (ms -: O) (ms -: I) (LTLeading ms))
        Right lt2 =>
          LTELessThan (ms -: O) (pred (ns2 -: n) -: I) (LTAppend ms (pred (ns2 -: n)) lt2 O I)
lessThanImpliesLTEPred (ms -: O) (ms -: I) (LTLeading ms) = LTEEqual (ms -: O)
lessThanImpliesLTEPred (ms -: O) (ns -: I) (LTAppend ms ns lt O I) =
  LTELessThan (ms -: O) (ns -: O) (LTAppend ms ns lt O O)
lessThanImpliesLTEPred (ms -: I) (J -: O) (LTAppend ms J lt I O) impossible
lessThanImpliesLTEPred (ms -: I) (ns -: n -: O) (LTAppend ms (ns -: n) lt I O) =
  replace {P = \z => LTE (ms -: I) z} (sym $ predDashAppendsAcc (ns -: n) [I]) $
  case decomposeLTE $ lessThanImpliesLTEPred ms (ns -: n) lt of
    Left eq   =>
      replace {P = \z => LTE (ms -: I) (z -: I)} eq (LTEEqual (ms -: I))
    Right lt2 =>
      LTELessThan (ms -: I) (pred (ns -: n) -: I) (LTAppend ms (pred (ns -: n)) lt2 I I)
lessThanImpliesLTEPred (ms -: I) (ns -: I) (LTAppend ms ns lt I I) =
  LTELessThan (ms -: I) (ns -: O) (LTAppend ms ns lt I O)

lessThanImpliesSuccLTE : (m : BiNat) -> (n : BiNat) -> LT m n -> LTE (succ m) n
lessThanImpliesSuccLTE m         J lt impossible
lessThanImpliesSuccLTE J         (J -: O)       (JLT J O) = LTEEqual (J -: O)
lessThanImpliesSuccLTE J         (J -: I)       (JLT J I) =
  LTELessThan (J -: O) (J -: I) (LTLeading J)
lessThanImpliesSuccLTE J         (ns -: n -: O) lt        =
  LTELessThan (J -: O) (ns -: n -: O) (LTAppend J (ns -: n) (JLT ns n) O O)
lessThanImpliesSuccLTE J         (ns -: n -: I) lt        =
  LTELessThan (J -: O) (ns -: n -: I) (LTAppend J (ns -: n) (JLT ns n) O I)
lessThanImpliesSuccLTE (ms -: O) (ns -: O)      (LTAppend ms ns lt O O) =
  LTELessThan (ms -: I) (ns -: O) (LTAppend ms ns lt I O)
lessThanImpliesSuccLTE (ms -: O) (ms -: I)      (LTLeading ms) = LTEEqual (ms -: I)
lessThanImpliesSuccLTE (ms -: O) (ns -: I)      (LTAppend ms ns lt O I) =
  LTELessThan (ms -: I) (ns -: I) (LTAppend ms ns lt I I)
lessThanImpliesSuccLTE (ms -: I) (ns -: O)      (LTAppend ms ns lt I O) =
  rewrite succDashAppendsAcc ms [O] in
  case decomposeLTE $ lessThanImpliesSuccLTE ms ns lt of
    Left eq =>
      rewrite eq in LTEEqual (ns -: O)
    Right lt2 =>
      LTELessThan (succ ms -: O) (ns -: O) (LTAppend (succ ms) ns lt2 O O)
lessThanImpliesSuccLTE (ms -: I) (ns -: I)      (LTAppend ms ns lt I I) =
  rewrite succDashAppendsAcc ms [O] in
  case decomposeLTE $ lessThanImpliesSuccLTE ms ns lt of
    Left eq =>
      rewrite eq in LTELessThan (ns -: O) (ns -: I) (LTLeading ns)
    Right lt2 =>
      LTELessThan (succ ms -: O) (ns -: I) (LTAppend (succ ms) ns lt2 O I)

succKeepsLessThan : (m : BiNat) -> (n : BiNat) -> LT m n -> LT (succ m) (succ n)
succKeepsLessThan m         J              lt impossible
succKeepsLessThan J         (J -: O)       lt = LTLeading J
succKeepsLessThan J         (ns -: n -: O) lt = LTAppend J (ns -: n) (JLT ns n) O I
succKeepsLessThan J         (J -: I)       lt = LTAppend J (J -: O) (JLT J O) O O
succKeepsLessThan J         (ns -: n -: I) lt =
  rewrite succDashAppendsAcc (ns -: n) [O] in
  LTAppend J (succ (ns -: n)) (lessThanTransitive (JLT ns n) (lessThanSucc (ns -: n))) O O
succKeepsLessThan (ms -: O) (ns -: O)      (LTAppend ms ns lt O O) = LTAppend ms ns lt I I
succKeepsLessThan (ms -: O) (ms -: I)      (LTLeading ms) =
  rewrite succDashAppendsAcc ms [O] in
  LTAppend ms (succ ms) (lessThanSucc ms) I O
succKeepsLessThan (ms -: O) (ns -: I)      (LTAppend ms ns lt O I) =
  rewrite succDashAppendsAcc ns [O] in
  LTAppend ms (succ ns) (lessThanTransitive lt (lessThanSucc ns)) I O
succKeepsLessThan (ms -: I) (ns -: O)      (LTAppend ms ns lt I O) =
  rewrite succDashAppendsAcc ms [O] in
  case decomposeLTE $ lessThanImpliesSuccLTE ms ns lt of
    Left eq   => rewrite eq in LTLeading ns
    Right lt2 => LTAppend (succ ms) ns lt2 O I
succKeepsLessThan (ms -: I) (ns -: I)      (LTAppend ms ns lt I I) =
  rewrite succDashAppendsAcc ms [O] in
  rewrite succDashAppendsAcc ns [O] in
  LTAppend (succ ms) (succ ns) (succKeepsLessThan ms ns lt) O O

succsRecoversLessThan : (m : BiNat) -> (n : BiNat) -> LT (succ m) (succ n) -> LT m n
succsRecoversLessThan m n lt =
  case
    decomposeLTE $
    replace {P = \z => LTE (succ m) z} (predOfSucc n) $
    lessThanImpliesLTEPred (succ m) (succ n) lt
  of
    Left eq =>
      rewrite sym eq in lessThanSucc m
    Right lt2 =>
      lessThanTransitive (lessThanSucc m) lt2

lessThanImpliesLTEOfPreds : (m : BiNat) -> (n : BiNat) -> LT m n -> LTE (pred m) (pred n)
lessThanImpliesLTEOfPreds J         (J -: O)       lt = LTEEqual J
lessThanImpliesLTEOfPreds J         (ns -: n -: O) lt =
  rewrite predDashAppendsAcc (ns -: n) [I] in
  LTELessThan J (pred (ns -: n) -: I) (JLT (pred (ns -: n)) I)
lessThanImpliesLTEOfPreds J         (ns -: I)      lt = LTELessThan J (ns -: O) (JLT ns O)
lessThanImpliesLTEOfPreds (ms -: m) ns             lt =
  lessThanEqualTransitive
    (LTELessThan (pred (ms -: m)) (ms -: m) (predIsLessThan (ms -: m) (JLT ms m)))
    (lessThanImpliesLTEPred (ms -: m) ns lt)

predRecoversLT : (m : BiNat) -> (n : BiNat) -> LT (pred m) (pred n) -> LT m n
predRecoversLT m         J         lt impossible
predRecoversLT J         (ns -: n) lt = JLT ns n
predRecoversLT (ms -: m) (ns -: n) lt =
  rewrite sym $ succOfPred (ms -: m) uninhabited in
  rewrite sym $ succOfPred (ns -: n) uninhabited in
  succKeepsLessThan (pred (ms -: m)) (pred (ns -: n)) lt

lessThanPlus : (m : BiNat) -> (n : BiNat) -> LT m (plus n m)
lessThanPlus m n =
  induction
    (\k => LT m (plus k m))
    (\k, pk =>
      replace {P = \z => LT m (plus z m)} (jPlusIsSucc k) $
      replace {P = \z => LT m z} (plusAssociative J k m) $
      replace {P = \z => LT m z} (sym $ jPlusIsSucc (plus k m)) $
      lessThanTransitive pk (lessThanSucc (plus k m))
    )
    (replace (sym $ jPlusIsSucc m) (lessThanSucc m))
    n

completeInduction :
  (P : BiNat -> Type) ->
  ((k : BiNat) -> ((m : BiNat) -> LT m k -> P m) -> P k) ->
  (n : BiNat) -> P n
completeInduction prop trans n =
  trans n $ induction
    (\k => (m : BiNat) -> LT m k -> prop m)
    (\k, pk, m, lt =>
      case decomposeLTE $ lessThanImpliesLTEPred m (succ k) lt of
        Left eq =>
          rewrite eq in rewrite predOfSucc k in trans k pk
        Right lt2 =>
          pk m (replace (predOfSucc k) lt2)
    )
    (\m, lt => absurd (uninhabited lt))
    n
