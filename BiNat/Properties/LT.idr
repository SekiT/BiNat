module BiNat.Properties.LT

import BiNat
import BiNat.Properties.Plus
import BiNat.Properties.Induction

%access public export
%default total

nIsNotLessThanItself : (n : BiNat) -> Not (LT n n)
nIsNotLessThanItself J         lt = uninhabited {t = LT J J} lt
nIsNotLessThanItself (ns -: n) (JLT ms m) impossible
nIsNotLessThanItself (ns -: n) (LTLeading _ _ _) impossible
nIsNotLessThanItself (ns -: n) (LTAppend ns ns lt n n) = nIsNotLessThanItself ns lt

lessThanImpliesNotEqual : (m, n : BiNat) -> LT m n -> Not (m = n)
lessThanImpliesNotEqual m n lt eq = nIsNotLessThanItself n $ replace {P = \z => LT z n} eq lt

greaterThanImpliesNotEqual : (m, n : BiNat) -> GT m n -> Not (m = n)
greaterThanImpliesNotEqual m n gt = (lessThanImpliesNotEqual n m gt) . sym

lessThanImpliesNotGreaterThan : (m, n : BiNat) -> LT m n -> Not (GT m n)
lessThanImpliesNotGreaterThan J         (ns -: n) (JLT ns n) lt = uninhabited lt
lessThanImpliesNotGreaterThan (ms -: O) (ns -: I) (LTLeading ms ns eq) (LTAppend ns ms lt I O) =
  nIsNotLessThanItself ns (replace eq lt)
lessThanImpliesNotGreaterThan (ms -: I) (ns -: O) (LTAppend ms ns lt I O) (LTLeading ns ms eq) =
  nIsNotLessThanItself ms (replace {P = \z => LT ms z} eq lt)
lessThanImpliesNotGreaterThan (ms -: m) (ns -: n) (LTAppend ms ns lt1 m n) (LTAppend ns ms lt2 n m) =
  lessThanImpliesNotGreaterThan ms ns lt1 lt2

lessThanTransitive : BiNat.LT l m -> LT m n -> LT l n
lessThanTransitive (JLT ms O)               (LTLeading ms ns eq)     = JLT ns I
lessThanTransitive (JLT ms m)               (LTAppend ms ns lt m n)  = JLT ns n
lessThanTransitive (LTLeading ls ms eq)     (LTAppend ms ns lt I n)  =
  LTAppend ls ns (replace {P = \z => BiNat.LT z ns} (sym eq) lt) O n
lessThanTransitive (LTAppend ls ms lt l O)  (LTLeading ms ns eq)     =
  LTAppend ls ns (replace {P = \z => BiNat.LT ls z} eq lt) l I
lessThanTransitive (LTAppend ls ms lt1 l m) (LTAppend ms ns lt2 m n) =
  LTAppend ls ns (lessThanTransitive lt1 lt2) l n

lessThanEqualTransitive : BiNat.LTE l m -> LTE m n -> LTE l n
lessThanEqualTransitive (LTEEqual l m eq1)    (LTEEqual m n eq2)    =
  LTEEqual l n (replace {P = \z => z = n} (sym eq1) eq2)
lessThanEqualTransitive (LTELessThan l m lt1) (LTEEqual m n eq2)    =
  LTELessThan l n (replace {P = \z => LT l z} eq2 lt1)
lessThanEqualTransitive (LTEEqual l m eq1)    (LTELessThan m n lt2) =
  LTELessThan l n (replace {P = \z => LT z n} (sym eq1) lt2)
lessThanEqualTransitive (LTELessThan l m lt1) (LTELessThan m n lt2) =
  LTELessThan l n (lessThanTransitive lt1 lt2)

lessThanEqualAntiSymmetric : (m, n : BiNat) -> LTE m n -> GTE m n -> m = n
lessThanEqualAntiSymmetric m n (LTEEqual m n eq1)    (LTEEqual n m eq2)    = eq1
lessThanEqualAntiSymmetric m n (LTEEqual m n eq1)    (LTELessThan n m lt2) =
  absurd $ nIsNotLessThanItself n (replace {P = \z => LT n z} eq1 lt2)
lessThanEqualAntiSymmetric m n (LTELessThan m n lt1) (LTEEqual n m eq2)    =
  absurd $ nIsNotLessThanItself m (replace {P = \z => LT m z} eq2 lt1)
lessThanEqualAntiSymmetric m n (LTELessThan m n lt1) (LTELessThan n m lt2) =
  absurd $ lessThanImpliesNotGreaterThan m n lt1 lt2

transLTandLTE : BiNat.LT l m -> LTE m n -> LT l n
transLTandLTE lt1 (LTEEqual m n eq)     = rewrite sym eq in lt1
transLTandLTE lt1 (LTELessThan m n lt2) = lessThanTransitive lt1 lt2

transLTEandLT : BiNat.LTE l m -> LT m n -> LT l n
transLTEandLT (LTEEqual l m eq)     lt2 = rewrite eq in lt2
transLTEandLT (LTELessThan l m lt1) lt2 = lessThanTransitive lt1 lt2

lessThanOrGTE : (m, n : BiNat) -> Either (LT m n) (GTE m n)
lessThanOrGTE J         J         = Right $ LTEEqual J J Refl
lessThanOrGTE J         (ns -: n) = Left $ JLT ns n
lessThanOrGTE (ms -: m) J         = Right $ LTELessThan J (ms -: m) (JLT ms m)
lessThanOrGTE (ms -: O) (ns -: O) =
  case lessThanOrGTE ms ns of
    Left lt                      => Left (LTAppend ms ns lt O O)
    Right (LTEEqual ns ms eq)    => Right $ rewrite sym eq in LTEEqual (ns -: O) (ns -: O) Refl
    Right (LTELessThan ns ms gt) => Right $ LTELessThan (ns -: O) (ms -: O) (LTAppend ns ms gt O O)
lessThanOrGTE (ms -: O) (ns -: I) =
  case lessThanOrGTE ms ns of
    Left lt                      => Left (LTAppend ms ns lt O I)
    Right (LTEEqual ns ms eq)    => Left $ rewrite eq in LTLeading ms ms Refl
    Right (LTELessThan ns ms gt) => Right $ LTELessThan (ns -: I) (ms -: O) (LTAppend ns ms gt I O)
lessThanOrGTE (ms -: I) (ns -: O) =
  case lessThanOrGTE ms ns of
    Left lt                      => Left (LTAppend ms ns lt I O)
    Right (LTEEqual ns ms eq)    => Right $ LTELessThan (ns -: O) (ms -: I) (rewrite sym eq in LTLeading ns ns Refl)
    Right (LTELessThan ns ms gt) => Right $ LTELessThan (ns -: O) (ms -: I) (LTAppend ns ms gt O I)
lessThanOrGTE (ms -: I) (ns -: I) =
  case lessThanOrGTE ms ns of
    Left lt                      => Left (LTAppend ms ns lt I I)
    Right (LTEEqual ns ms eq)    => Right $ rewrite sym eq in LTEEqual (ns -: I) (ns -: I) Refl
    Right (LTELessThan ns ms gt) => Right $ LTELessThan (ns -: I) (ms -: I) (LTAppend ns ms gt I I)

lessThanAppended : (n : BiNat) -> (b : Bit) -> LT n (n -: b)
lessThanAppended J         b = JLT J b
lessThanAppended (ns -: n) b = LTAppend ns (ns -: n) (lessThanAppended ns n) n b

succGreaterThanJ : (n : BiNat) -> GT (succ n) J
succGreaterThanJ J         = JLT J O
succGreaterThanJ (ns -: O) = JLT ns I
succGreaterThanJ (ns -: I) = rewrite succDashAppendsAcc ns [O] in JLT (succ ns) O

lessThanSucc : (n : BiNat) -> LT n (succ n)
lessThanSucc J         = JLT J O
lessThanSucc (ns -: O) = LTLeading ns ns Refl
lessThanSucc (ns -: I) =
  replace {P = \z => LT (ns -: I) z} (sym $ succDashAppendsAcc ns [O]) $
  LTAppend ns (succ ns) (lessThanSucc ns) I O

predIsLessThan : (n : BiNat) -> LT J n -> LT (pred n) n
predIsLessThan J _ impossible
predIsLessThan (J -: O)       _ = JLT J O
predIsLessThan (ns -: O -: O) _ =
  replace {P = \z => LT z (ns -: O -: O)} (sym $ predDashAppendsAcc (ns -: O) [I]) $
  LTAppend (pred (ns -: O)) (ns -: O) (predIsLessThan (ns -: O) (JLT ns O)) I O
predIsLessThan (ns -: I -: O) _ = LTAppend (ns -: O) (ns -: I) (LTLeading ns ns Refl) I O
predIsLessThan (ns -: I)      _ = LTLeading ns ns Refl

predLessThanEqual : (n : BiNat) -> LTE (pred n) n
predLessThanEqual J              = LTEEqual J J Refl
predLessThanEqual (J -: O)       = LTELessThan J (J -: O) (JLT J O)
predLessThanEqual (ns -: n -: O) =
  rewrite predDashAppendsAcc (ns -: n) [I] in
  let lt = predIsLessThan (ns -: n) (JLT ns n) in
  LTELessThan (pred (ns -: n) -: I) (ns -: n -: O) (LTAppend (pred (ns -: n)) (ns -: n) lt I O)
predLessThanEqual (ns -: I)      = LTELessThan (ns -: O) (ns -: I) (LTLeading ns ns Refl)

lessThanImpliesLTEPred : (m, n : BiNat) -> LT m n -> LTE m (pred n)
lessThanImpliesLTEPred m J lt impossible
lessThanImpliesLTEPred J (J -: O)       _ = LTEEqual J J Refl
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
      case lessThanImpliesLTEPred ms (ns2 -: n) lt of
        LTEEqual _ _ eq =>
          replace {P = \z => LTE (ms -: O) (z -: I)} eq (LTELessThan (ms -: O) (ms -: I) (LTLeading ms ms Refl))
        LTELessThan _ _ lt2 =>
          LTELessThan (ms -: O) (pred (ns2 -: n) -: I) (LTAppend ms (pred (ns2 -: n)) lt2 O I)
lessThanImpliesLTEPred (ms -: O) (ns -: I) (LTLeading ms ns eq) =
  LTEEqual (ms -: O) (ns -: O) (rewrite eq in Refl)
lessThanImpliesLTEPred (ms -: O) (ns -: I) (LTAppend ms ns lt O I) =
  LTELessThan (ms -: O) (ns -: O) (LTAppend ms ns lt O O)
lessThanImpliesLTEPred (ms -: I) (J -: O) (LTAppend ms J lt I O) impossible
lessThanImpliesLTEPred (ms -: I) (ns -: n -: O) (LTAppend ms (ns -: n) lt I O) =
  replace {P = \z => LTE (ms -: I) z} (sym $ predDashAppendsAcc (ns -: n) [I]) $
  case lessThanImpliesLTEPred ms (ns -: n) lt of
    LTEEqual _ _ eq =>
      replace {P = \z => LTE (ms -: I) (z -: I)} eq (LTEEqual (ms -: I) (ms -: I) Refl)
    LTELessThan _ _ lt2 =>
      LTELessThan (ms -: I) (pred (ns -: n) -: I) (LTAppend ms (pred (ns -: n)) lt2 I I)
lessThanImpliesLTEPred (ms -: I) (ns -: I) (LTAppend ms ns lt I I) =
  LTELessThan (ms -: I) (ns -: O) (LTAppend ms ns lt I O)

lessThanImpliesSuccLTE : (m, n : BiNat) -> LT m n -> LTE (succ m) n
lessThanImpliesSuccLTE m         J lt impossible
lessThanImpliesSuccLTE J         (J -: O)       (JLT J O) = LTEEqual (J -: O) (J -: O) Refl
lessThanImpliesSuccLTE J         (J -: I)       (JLT J I) =
  LTELessThan (J -: O) (J -: I) (LTLeading J J Refl)
lessThanImpliesSuccLTE J         (ns -: n -: O) lt        =
  LTELessThan (J -: O) (ns -: n -: O) (LTAppend J (ns -: n) (JLT ns n) O O)
lessThanImpliesSuccLTE J         (ns -: n -: I) lt        =
  LTELessThan (J -: O) (ns -: n -: I) (LTAppend J (ns -: n) (JLT ns n) O I)
lessThanImpliesSuccLTE (ms -: O) (ns -: O)      (LTAppend ms ns lt O O) =
  LTELessThan (ms -: I) (ns -: O) (LTAppend ms ns lt I O)
lessThanImpliesSuccLTE (ms -: O) (ns -: I)      (LTLeading ms ns eq) =
  LTEEqual (ms -: I) (ns -: I) (rewrite eq in Refl)
lessThanImpliesSuccLTE (ms -: O) (ns -: I)      (LTAppend ms ns lt O I) =
  LTELessThan (ms -: I) (ns -: I) (LTAppend ms ns lt I I)
lessThanImpliesSuccLTE (ms -: I) (ns -: O)      (LTAppend ms ns lt I O) =
  rewrite succDashAppendsAcc ms [O] in
  case lessThanImpliesSuccLTE ms ns lt of
    LTEEqual _ _ eq =>
      rewrite eq in LTEEqual (ns -: O) (ns -: O) Refl
    LTELessThan _ _ lt2 =>
      LTELessThan (succ ms -: O) (ns -: O) (LTAppend (succ ms) ns lt2 O O)
lessThanImpliesSuccLTE (ms -: I) (ns -: I)      (LTAppend ms ns lt I I) =
  rewrite succDashAppendsAcc ms [O] in
  case lessThanImpliesSuccLTE ms ns lt of
    LTEEqual _ _ eq =>
      rewrite eq in LTELessThan (ns -: O) (ns -: I) (LTLeading ns ns Refl)
    LTELessThan _ _ lt2 =>
      LTELessThan (succ ms -: O) (ns -: I) (LTAppend (succ ms) ns lt2 O I)

succKeepsLessThan : (m, n : BiNat) -> LT m n -> LT (succ m) (succ n)
succKeepsLessThan m         J              lt impossible
succKeepsLessThan J         (J -: O)       lt = LTLeading J J Refl
succKeepsLessThan J         (ns -: n -: O) lt = LTAppend J (ns -: n) (JLT ns n) O I
succKeepsLessThan J         (J -: I)       lt = LTAppend J (J -: O) (JLT J O) O O
succKeepsLessThan J         (ns -: n -: I) lt =
  rewrite succDashAppendsAcc (ns -: n) [O] in
  LTAppend J (succ (ns -: n)) (lessThanTransitive (JLT ns n) (lessThanSucc (ns -: n))) O O
succKeepsLessThan (ms -: O) (ns -: O)      (LTAppend ms ns lt O O) = LTAppend ms ns lt I I
succKeepsLessThan (ms -: O) (ns -: I)      (LTLeading ms ns eq) =
  rewrite sym eq in
  rewrite succDashAppendsAcc ms [O] in
  LTAppend ms (succ ms) (lessThanSucc ms) I O
succKeepsLessThan (ms -: O) (ns -: I)      (LTAppend ms ns lt O I) =
  rewrite succDashAppendsAcc ns [O] in
  LTAppend ms (succ ns) (lessThanTransitive lt (lessThanSucc ns)) I O
succKeepsLessThan (ms -: I) (ns -: O)      (LTAppend ms ns lt I O) =
  rewrite succDashAppendsAcc ms [O] in
  case lessThanImpliesSuccLTE ms ns lt of
    LTEEqual _ _ eq     => rewrite eq in LTLeading ns ns Refl
    LTELessThan _ _ lt2 => LTAppend (succ ms) ns lt2 O I
succKeepsLessThan (ms -: I) (ns -: I)      (LTAppend ms ns lt I I) =
  rewrite succDashAppendsAcc ms [O] in
  rewrite succDashAppendsAcc ns [O] in
  LTAppend (succ ms) (succ ns) (succKeepsLessThan ms ns lt) O O

plusNKeepsLessThan : (l, m : BiNat) -> LT l m -> (n : BiNat) -> LT (plus l n) (plus m n)
plusNKeepsLessThan l m lt n =
  induction
    (\k => LT (plus l k) (plus m k))
    (\k, pk =>
      rewrite sym $ plusJIsSucc k in
      rewrite plusAssociative l k J in
      rewrite plusAssociative m k J in
      rewrite plusJIsSucc (plus l k) in
      rewrite plusJIsSucc (plus m k) in
      succKeepsLessThan (plus l k) (plus m k) pk
    )
    (rewrite plusJIsSucc l in rewrite plusJIsSucc m in succKeepsLessThan l m lt)
    n

succsRecoversLessThan : (m, n : BiNat) -> LT (succ m) (succ n) -> LT m n
succsRecoversLessThan m n lt =
  case
    replace {P = \z => LTE (succ m) z} (predOfSucc n) $
    lessThanImpliesLTEPred (succ m) (succ n) lt
  of
    LTEEqual _ _ eq =>
      rewrite sym eq in lessThanSucc m
    LTELessThan _ _ lt2 =>
      lessThanTransitive (lessThanSucc m) lt2

lessThanImpliesLTEOfPreds : (m, n : BiNat) -> LT m n -> LTE (pred m) (pred n)
lessThanImpliesLTEOfPreds J         (J -: O)       lt = LTEEqual J J Refl
lessThanImpliesLTEOfPreds J         (ns -: n -: O) lt =
  rewrite predDashAppendsAcc (ns -: n) [I] in
  LTELessThan J (pred (ns -: n) -: I) (JLT (pred (ns -: n)) I)
lessThanImpliesLTEOfPreds J         (ns -: I)      lt = LTELessThan J (ns -: O) (JLT ns O)
lessThanImpliesLTEOfPreds (ms -: m) ns             lt =
  lessThanEqualTransitive
    (LTELessThan (pred (ms -: m)) (ms -: m) (predIsLessThan (ms -: m) (JLT ms m)))
    (lessThanImpliesLTEPred (ms -: m) ns lt)

predKeepsLessThan : (m, n : BiNat) -> LT J m -> LT m n -> LT (pred m) (pred n)
predKeepsLessThan m n jltm lt =
  case lessThanImpliesLTEOfPreds m n lt of
    LTEEqual (pred m) (pred n) eq =>
      let nIsNotJ = greaterThanImpliesNotEqual n J (lessThanTransitive jltm lt) in
      let mIsNotJ = greaterThanImpliesNotEqual m J jltm in
      let mEQn = replace {P = \z => m = z} (succOfPred n nIsNotJ) $
                 replace {P = \z => z = succ (pred n)} (succOfPred m mIsNotJ) $
                 replace {P = \z => succ (pred m) = succ z} eq Refl in
      absurd $ lessThanImpliesNotEqual m n lt mEQn
    LTELessThan (pred m) (pred n) lt =>
      lt

predRecoversLT : (m, n : BiNat) -> LT (pred m) (pred n) -> LT m n
predRecoversLT m         J         lt impossible
predRecoversLT J         (ns -: n) lt = JLT ns n
predRecoversLT (ms -: m) (ns -: n) lt =
  rewrite sym $ succOfPred (ms -: m) uninhabited in
  rewrite sym $ succOfPred (ns -: n) uninhabited in
  succKeepsLessThan (pred (ms -: m)) (pred (ns -: n)) lt

lessThanPlus : (m, n : BiNat) -> LT m (plus n m)
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
      case lessThanImpliesLTEPred m (succ k) lt of
        LTEEqual _ _ eq =>
          rewrite eq in rewrite predOfSucc k in trans k pk
        LTELessThan _ _ lt2 =>
          pk m (replace (predOfSucc k) lt2)
    )
    (\m, lt => absurd (uninhabited lt))
    n

compareSelf : (m, n : BiNat) -> m = n -> (last : Ordering) -> compare' m n last = last
compareSelf m J         eq last = rewrite eq in Refl
compareSelf m (ns -: O) eq last = rewrite eq in compareSelf ns ns Refl last
compareSelf m (ns -: I) eq last = rewrite eq in compareSelf ns ns Refl last

compareLT : (m, n : BiNat) -> LT m n -> (last : Ordering) -> compare' m n last = LT
compareLT m         J         _                       _    impossible
compareLT J         (ns -: n) _                       _    = Refl
compareLT (ms -: O) (ns -: O) (LTAppend ms ns lt O O) last = compareLT ms ns lt last
compareLT (ms -: O) (ns -: I) (LTAppend ms ns lt O I) last = compareLT ms ns lt LT
compareLT (ms -: O) (ns -: I) (LTLeading ms ns eq)    last = rewrite eq in compareSelf ns ns Refl LT
compareLT (ms -: I) (ns -: O) (LTAppend ms ns lt I O) last = compareLT ms ns lt GT
compareLT (ms -: I) (ns -: I) (LTAppend ms ns lt I I) last = compareLT ms ns lt last

compareGT : (m, n : BiNat) -> GT m n -> (last : Ordering) -> compare' m n last = GT
compareGT J         n         _                       _    impossible
compareGT (ms -: m) J         _                       _    = Refl
compareGT (ms -: O) (ns -: O) (LTAppend ns ms gt O O) last = compareGT ms ns gt last
compareGT (ms -: O) (ns -: I) (LTAppend ns ms gt I O) last = compareGT ms ns gt LT
compareGT (ms -: I) (ns -: O) (LTAppend ns ms gt O I) last = compareGT ms ns gt GT
compareGT (ms -: I) (ns -: O) (LTLeading ns ms eq)    last = rewrite eq in compareSelf ms ms Refl GT
compareGT (ms -: I) (ns -: I) (LTAppend ns ms gt I I) last = compareGT ms ns gt last

-- These should be in Prelude.Interfaces
Uninhabited (EQ = LT) where
  uninhabited Refl impossible
Uninhabited (EQ = GT) where
  uninhabited Refl impossible
Uninhabited (LT = EQ) where
  uninhabited Refl impossible
Uninhabited (Prelude.Interfaces.LT = GT) where
  uninhabited Refl impossible
Uninhabited (GT = EQ) where
  uninhabited Refl impossible
Uninhabited (Prelude.Interfaces.GT = LT) where
  uninhabited Refl impossible

compareRecoversEQ : (m, n : BiNat) -> compare m n = EQ -> m = n
compareRecoversEQ m n eq =
  case lessThanOrGTE m n of
    Left lt                    => absurd $ uninhabited $ trans (sym eq) (compareLT m n lt EQ)
    Right (LTEEqual n m eq2)   => sym eq2
    Right (LTELessThan n m gt) => absurd $ uninhabited $ trans (sym eq) (compareGT m n gt EQ)

compareRecoversLT : (m, n : BiNat) -> compare m n = LT -> LT m n
compareRecoversLT m n eq =
  case lessThanOrGTE m n of
    Left lt                    => lt
    Right (LTEEqual n m eq2)   => absurd $ uninhabited $ trans (sym eq) (compareSelf m n (sym eq2) EQ)
    Right (LTELessThan n m gt) => absurd $ uninhabited $ trans (sym eq) (compareGT m n gt EQ)

compareRecoversGT : (m, n : BiNat) -> compare m n = GT -> GT m n
compareRecoversGT m n eq =
  case lessThanOrGTE n m of
    Left gt                    => gt
    Right (LTEEqual m n eq2)   => absurd $ uninhabited $ trans (sym eq) (compareSelf m n eq2 EQ)
    Right (LTELessThan m n lt) => absurd $ uninhabited $ trans (sym eq) (compareLT m n lt EQ)
