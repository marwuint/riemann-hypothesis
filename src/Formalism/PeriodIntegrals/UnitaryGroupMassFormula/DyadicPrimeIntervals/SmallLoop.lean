import Mathlib

namespace PI.PrimesDyadicRS.K

def pr (Q m : Nat) : Nat :=
  if m ≤ 362 then (if Nat.gcd m (Nat.factorial (m - 1)) = 1 then 1 else 0)
  else (if Nat.gcd m Q = 1 then 1 else 0)

end PI.PrimesDyadicRS.K
