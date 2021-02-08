module BiNat.Views

import BiNat
import BiNat.Properties.Plus

%default total

||| View for BiNat which represents whether the number is J or succ of something
public export
data SuccView : BiNat -> Type where
  IsJ    : SuccView J
  IsSucc : SuccView (succ n)

||| Determines whether the BiNat is J or succ of something.
export
succView : (n : BiNat) -> SuccView n
succView J = IsJ
succView (x -: I) = IsSucc {n = x -: O}
succView (x -: O) with (succView x)
  succView (J      -: O) | IsJ    = IsSucc {n = J}
  succView (succ n -: O) | IsSucc =
    rewrite sym $ plusJIsSucc n in
    rewrite sym $ plusDashAppendsAcc n J O [O] in
    rewrite plusAssociative (n -: O) J J in
    IsSucc {n = n -: I}
