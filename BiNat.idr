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

fromInteger : Integer -> BiNat
fromInteger i = if i <= 1 then J else fromInteger' i [] where
  fromInteger' : Integer -> List Bit -> BiNat
  fromInteger' 1 acc = foldl (-:) J acc
  fromInteger' i acc =
    fromInteger'
      (assert_smaller i (assert_total (div i 2)))
      ((if assert_total (mod i 2) == 0 then O else I) :: acc)
