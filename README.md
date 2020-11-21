# BiNat

My exercise in [Idris](https://www.idris-lang.org/), reimplementing natural number with O(log n).

## Motivation

- My practicing in Idris and proofs
- `Nat` has very slow performance (try `fromIntegerNat 100 * 100`)
- With `Int` or something primitive, we can't write proof by induction

## Features

`BiNat` defines a natural number as a finite sequence of bits. By this, we have following features:

- `0` is not a natural number
  - Because every sequence should start with 1
- Costs O(log n) for defining a natural number n
- Induction through function `BiNat.Properties.Induction.induction`
  - Note that n is not structurally smaller than n + 1
  - There is also complete induction `BiNat.Properties.LT.completeInduction`

## Examples

### Factorial function using `BiNat.Properties.Induction.induction`

```idr
import BiNat
import BiNat.Properties.Induction

fact : BiNat -> BiNat
fact = induction
  (\k => BiNat)                  -- All intermediate values are of type BiNat
  (\k, factk => (k + 1) * factk) -- Define fact (k + 1) using k and fact k
  J                              -- RHS of fact J = J
```

### Fibonacci function using `BiNat.Properties.Induction.induction`

```idr
import BiNat
import BiNat.Properties.Induction

fib : BiNat -> BiNat
fib n = fst $ induction                     -- Taking first element of the pair (fib n, fib (n + 1))
  (\k => (BiNat, BiNat))                    -- Each accumulator is (fib k, fib (k + 1))
  (\k, (fib0, fib1) => (fib1, fib0 + fib1))
  (J, J)                                    -- (fib 1, fib 2) = (1, 1)
  n
```

## Development

We use [asdf](https://github.com/asdf-vm/asdf) to manage language versions.

Install [asdf-idris](https://github.com/vic/asdf-idris) plugin (beware that [issue](https://github.com/vic/asdf-idris/issues/1)!) and then `asdf install`.
