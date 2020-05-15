||| Binary representation of natural numbers.
module BiNat

%access public export

data Bit : Type where
  O : Bit
  I : Bit

infixl 7 -:

data BiNat : Type where
  ||| Leading one bit
  J : BiNat
  ||| Appends a bit to a BiNat.
  ||| `J -: O -: I -: I` corresponds to `1011`.
  (-:) : BiNat -> Bit -> BiNat

Uninhabited (J = n -: b) where
  uninhabited Refl impossible
Uninhabited (n -: b = J) where
  uninhabited Refl impossible
Uninhabited (m -: O = n -: I) where
  uninhabited Refl impossible
Uninhabited (m -: I = n -: O) where
  uninhabited Refl impossible
