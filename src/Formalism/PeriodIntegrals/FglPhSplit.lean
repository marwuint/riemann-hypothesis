import Mathlib

noncomputable section

namespace PI.FglPhSplit

open Classical

def expMv {K : Type*} [Field K] {σ : Type*} (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : K)

def hP {K : Type*} [Field K] {ι : Type*} [Fintype ι] (x y : ι → K × K) : K × K :=
  ∑ k, x k * (y k).swap

structure Dat (K : Type*) [Field K] where
  l : PowerSeries K
  ex : PowerSeries K
  ph : PowerSeries K

namespace Dat

variable {K : Type*} [Field K] (g : Dat K) {σ : Type*}

def lg (a : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ K) : MvPowerSeries σ K := g.pt (g.lg a + g.lg b)

def lin {ι : Type*} [Fintype ι] (c : ι → K) (a : ι → MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

end Dat

end PI.FglPhSplit

end
