import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

def LS (g r n : ℕ) : Finset ℕ := n.primeFactors.filter (fun ℓ => ℓ ∉ BB r g)

def WA (g e j ℓ : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  (nthRoots ((g ^ j - 1) * Lp g e ℓ) (1 : Fbar g)).toFinset.filter
    (fun w => (minpoly (ZMod g) w).natDegree = e)

def YB (g e' : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  ((X ^ (g ^ e') - X : (Fbar g)[X]).roots.toFinset).filter
    (fun y => (minpoly (ZMod g) y).natDegree = e')

def XB (g e ℓ : ℕ) [Fact g.Prime] (y : Fbar g) : Finset (Fbar g) :=
  (nthRoots (Lp g e ℓ) ((primeToPart ℓ y) ^ Lp g e ℓ)).toFinset.filter
    (fun x => (minpoly (ZMod g) x).natDegree = e)

def SB (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
    g ^ e' * Lp g e ℓ * g ^ (r - e - e')

def PA (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 2 r, ∃ j ∈ Finset.Icc 1 (e / 2),
    ∃ ℓ ∈ LS g r (g ^ e - 1), ∃ w ∈ WA g e j ℓ, minpoly (ZMod g) w ∣ f

def PB (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 1 r, ∃ e' ∈ Finset.Icc 1 (min e (r - e)),
    ∃ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∃ y ∈ YB g e', ∃ x ∈ XB g e ℓ y,
      minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f

end PI.SqfRootsInj.W
