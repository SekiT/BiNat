module BiNat.Properties.Induction

import BiNat
import BiNat.Properties.Plus

%access public export
%default total

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
