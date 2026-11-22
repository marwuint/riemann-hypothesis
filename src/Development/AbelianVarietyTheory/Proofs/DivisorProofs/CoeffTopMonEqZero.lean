import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.SecJet

section Alg

variable (R : Type) [CommRing R]

def sqIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) R) ^ 2)

abbrev EpsAlg (k : ℕ) : Type := MvPolynomial (Fin k) R ⧸ sqIdeal R k

def topMon (k : ℕ) : Fin k →₀ ℕ := ∑ a, Finsupp.single a 1

theorem coeff_topMon_eq_zero {k : ℕ} {p : MvPolynomial (Fin k) R} (hp : p ∈ sqIdeal R k) :
    MvPolynomial.coeff (topMon k) p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h a
  simp [topMon, Finsupp.finsetSum_apply, Finsupp.single_apply] at this

def topCoeff (k : ℕ) : EpsAlg R k →ₗ[R] R :=
  (Submodule.liftQ ((sqIdeal R k).restrictScalars R) (MvPolynomial.lcoeff R (topMon k))
    (fun _ hp => LinearMap.mem_ker.2 (coeff_topMon_eq_zero R hp))) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (sqIdeal R k)).symm.toLinearMap

def eps {k : ℕ} (a : Fin k) : EpsAlg R k := Ideal.Quotient.mk _ (MvPolynomial.X a)

theorem eps_mul_self {k : ℕ} (a : Fin k) : eps R a * eps R a = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨a, rfl⟩

end Alg

end GlobalTheory.SecJet

namespace GlobalTheory.SecJet

section Geo

variable (R : Type) [CommRing R]

abbrev epsT (k : ℕ) : Over (Sp R) := Over.mk (spMap (algebraMap R (EpsAlg R k)))

theorem spMap_comp_eq {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    spMap (f : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def epsScaleA (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  { epsScaleR c with commutes' := fun r => by simp [epsScaleR] }

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (spMap_comp_eq R (epsScaleA R c))

variable {R}

def tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) : epsR R ⟶ G :=
  (List.ofFn fun i => epsScale R (c i) ≫ v i).prod

theorem isLieComb_tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) :
    IsLieComb c v (tanComb c v) :=
  ⟨_, fun _ => rfl, rfl⟩

end Geo

def filt {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (i : ℕ) : Submodule K V :=
  Nat.rec ⊤ (fun k F => F ⊓ LinearMap.ker (j k)) i

theorem filt_succ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (i : ℕ) :
    filt j (i + 1) = filt j i ⊓ LinearMap.ker (j i) := rfl

end GlobalTheory.SecJet
