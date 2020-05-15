||| Binary representation of natural numbers.
module BiNat

%access export

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
