||| Binary representation of natural numbers.
module BiNat

%access public export
%default total

data Bit = O | I

infixl 7 -:

data BiNat : Type where
  ||| Leading one bit
  J : BiNat

  ||| Append a bit to a BiNat.
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

succ' : BiNat -> List Bit -> BiNat
succ' J        acc = foldl (-:) (J -: O) acc
succ' (n -: O) acc = foldl (-:) (n -: I) acc
succ' (n -: I) acc = succ' n (O :: acc)

||| The successor of a natural number.
succ : BiNat -> BiNat
succ n = succ' n []

pred' : BiNat -> List Bit -> BiNat
pred' J              acc = foldl (-:) J acc
pred' (n -: I)       acc = foldl (-:) (n -: O) acc
pred' (J -: O)       acc = foldl (-:) J acc
pred' (ns -: n -: O) acc = pred' (ns -: n) (I :: acc)

||| The predecessor of a natural number, but `pred J` is `J`.
pred : BiNat -> BiNat
pred n = pred' n []

nextCarry : Bit -> Bit -> Bit -> Bit
nextCarry I I I = I
nextCarry I I O = I
nextCarry I O I = I
nextCarry O I I = I
nextCarry _ _ _ = O

nextAcc : Bit -> Bit -> Bit -> Bit
nextAcc O O O = O
nextAcc O I I = O
nextAcc I O I = O
nextAcc I I O = O
nextAcc _ _ _ = I

plus' : BiNat -> BiNat -> Bit -> List Bit -> BiNat
plus' J         J         c acc = foldl (-:) (J -: c) acc
plus' J         ns        O acc = succ' ns acc
plus' J         (ns -: n) I acc = succ' ns (n :: acc)
plus' ms        J         O acc = succ' ms acc
plus' (ms -: m) J         I acc = succ' ms (m :: acc)
plus' (ms -: m) (ns -: n) c acc = plus' ms ns (nextCarry m n c) (nextAcc m n c :: acc)

||| Add two natural numbers.
plus : BiNat -> BiNat -> BiNat
plus m n = plus' m n O []

mult' : BiNat -> BiNat -> BiNat -> BiNat
mult' J         added acc = pred (plus added acc)
mult' (ms -: O) added acc = mult' ms (added -: O) acc
mult' (ms -: I) added acc = mult' ms (added -: O) (plus added acc)

||| Multiply natural numbers.
mult : BiNat -> BiNat -> BiNat
mult m n = mult' m n J

||| Convert an Integer to a BiNat, mapping non-positive numbers to J.
fromInteger : Integer -> BiNat
fromInteger i = if i <= 1 then J else fromInteger' i [] where
  fromInteger' : Integer -> List Bit -> BiNat
  fromInteger' 1 acc = foldl (-:) J acc
  fromInteger' i acc =
    fromInteger'
      (assert_smaller i (assert_total (div i 2)))
      ((if assert_total (mod i 2) == 0 then O else I) :: acc)

||| Convert a BiNat to an Integer.
toInteger : BiNat -> Integer
toInteger n = toInteger' n 1 0 where
  toInteger' : BiNat -> Integer -> Integer -> Integer
  toInteger' J         added acc = added + acc
  toInteger' (ns -: O) added acc = toInteger' ns (added * 2) acc
  toInteger' (ns -: I) added acc = toInteger' ns (added * 2) (acc + added)

tailToBiNat : List Bit -> BiNat
tailToBiNat []          = J
tailToBiNat (O :: tail) = tailToBiNat tail
tailToBiNat (I :: tail) = foldl (-:) J tail

minus' : BiNat -> BiNat -> List Bit -> BiNat
minus' J          J         tail = tailToBiNat tail
minus' J          ns        tail = J
minus' (J -: O)   J         tail = foldl (-:) J tail
minus' (ms -: O)  J         tail = foldl (-:) (pred ms -: I) tail
minus' (ms -: I)  J         tail = foldl (-:) (ms -: O) tail
minus' (ms -: O)  (ns -: O) tail = minus' ms ns (O :: tail)
minus' (J -: O)   (ns -: I) tail = J
minus' (ms -: O)  (ns -: I) tail = minus' (pred ms) ns (I :: tail)
minus' (ms -: I)  (ns -: O) tail = minus' ms ns (I :: tail)
minus' (ms -: I)  (ns -: I) tail = minus' ms ns (O :: tail)

||| Subtract natural numbers. If the second number is larger than or equal to the first, return J.
minus : BiNat -> BiNat -> BiNat
minus m n = minus' m n []

Eq BiNat where
  J         == J         = True
  (ns -: O) == (ms -: O) = ns == ms
  (ns -: I) == (ms -: I) = ns == ms
  _         == _         = False

||| Proofs that a BiNat is strictly less than another BiNat.
data LT : BiNat -> BiNat -> Type where
  JLT : (ns : BiNat) -> (n : Bit) -> LT J (ns -: n)
  LTLeading : (ms, ns : BiNat) -> ms = ns -> LT (ms -: O) (ns -: I)
  LTAppend : (ms, ns : BiNat) -> LT ms ns -> (m, n : Bit) -> LT (ms -: m) (ns -: n)

||| Strict greater than
GT : BiNat -> BiNat -> Type
GT m n = LT n m

Uninhabited (LT n J) where
  uninhabited JLT       impossible
  uninhabited LTLeading impossible
  uninhabited LTAppend  impossible

||| Less than or equal to
data LTE : BiNat -> BiNat -> Type where
  LTEEqual : (m, n : BiNat) -> m = n -> LTE m n
  LTELessThan : (m, n : BiNat) -> LT m n -> LTE m n

||| Greater than or equal to
GTE : BiNat -> BiNat -> Type
GTE m n = LTE n m

compare' : BiNat -> BiNat -> Ordering -> Ordering
compare' J         J         last = last
compare' J         (ns -: n) last = LT
compare' (ms -: m) J         last = GT
compare' (ms -: O) (ns -: O) last = compare' ms ns last
compare' (ms -: O) (ns -: I) last = compare' ms ns LT
compare' (ms -: I) (ns -: O) last = compare' ms ns GT
compare' (ms -: I) (ns -: I) last = compare' ms ns last

Ord BiNat where
  compare m n = compare' m n EQ

Num BiNat where
  (+) = plus
  (*) = mult
  fromInteger = BiNat.fromInteger
