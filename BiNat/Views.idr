module BiNat.Views

import BiNat
import BiNat.Properties.Plus

%default total

||| View for BiNat, of the form `IsJ` or `IsSucc n`
data SuccView : BiNat -> Type where
  IsJ    : SuccView J
  IsSucc : (n : BiNat) -> SuccView (succ n)

||| Determines whether the `BiNat` is `J` or succ of something.
succView : (n : BiNat) -> SuccView n
succView J = IsJ
succView (x -: I) = IsSucc (x -: O)
succView (x -: O) with (succView x)
  succView (J      -: O) | IsJ        = IsSucc J
  succView (succ n -: O) | (IsSucc n) =
    rewrite shiftLeftDoubles (succ n) in
    rewrite sym $ plusJIsSucc n in
    rewrite sym $ plusAssociative n J (n + J) in
    rewrite plusSymmetric J (n + J) in
    rewrite sym $ plusAssociative n J J in
    rewrite plusAssociative n n (J -: O) in
    rewrite plusAssociative (n + n) J J in
    rewrite plusJIsSucc (n + n + J) in
    IsSucc (n + n + J)
