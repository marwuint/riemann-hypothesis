import Mathlib
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.BaseInst
import Formalism.LocalToGlobal.Columns.AtTOwedS
import Formalism.LocalToGlobal.Columns.RamifiedOperatorsNonvacuous

open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host

section Pos

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def GSD.pairEmb (σ : K →+* ℂ) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

theorem GSD.pairAt_eq_pairEmb (v : InfinitePlace K) (x y : S.V) : S.pairAt v x y = S.pairEmb v.embedding x y := rfl

theorem GSD.map_pair (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) :
    σ (S.pair x y) = S.pairEmb σ x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, map_mul, hσ, GSD.pairEmb, GSD.gramV, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def GSD.ipEmb (h : S.Ok) (σ : K →+* ℂ) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairEmb σ (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

theorem GSD.ipAt_eq_ipEmb (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = S.ipEmb h v.embedding φ ψ := rfl

theorem GSD.map_ip (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (φ ψ : S.D → S.V) :
    σ (S.ip h φ ψ) = S.ipEmb h σ φ ψ := by
  let _ : Fintype S.Cl := h.fintypeCl
  unfold GSD.ip GSD.ipOf GSD.ipEmb CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  congr 1
  exact S.map_pair σ hσ _ _

end Pos

section GaussInst

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def gaussianPrimesLarge : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![29, 37]
  piG := ![gz ι LL hE 5 2, gz ι LL hE 6 1]
  Word := Unit
  T := fun _ => 763521676554817
  piT := fun _ => gz ι LL hE 1 27631896

end GaussInst

def ndN : ℕ := 4 * 51613301813429074383

theorem ndN_pos : 0 < ndN := by
  unfold ndN
  norm_num

theorem gaussianRationals_le_cyclotomic_four_mul (M : ℕ) : KQ 1 ≤ cycQ (4 * M) := by
  unfold KQ sqQ cycQ
  apply IntermediateField.adjoin.mono
  intro z hz
  have h : z ^ 2 = -1 := by
    have h1 : z ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb) := hz
    rw [h1]; simp
  show z ^ (4 * M) = 1
  rw [show 4 * M = 2 * (2 * M) by ring, pow_mul, h, pow_mul]
  simp

theorem gaussianRationals_le_cyclotomic_level : KQ 1 ≤ cycQ ndN := by
  exact gaussianRationals_le_cyclotomic_four_mul 51613301813429074383

instance fin_cycNd : FiniteDimensional ℚ (cycQ ndN) := fin_adjoin (finite_pow_eq ndN ndN_pos 1)

instance normal_cycNd : Normal ℚ (cycQ ndN) := normal_adjoin fun s x hx => by
  show (s x) ^ ndN = 1
  rw [← map_pow, show x ^ ndN = 1 from hx, map_one]

def ndIota : Qb →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

def ndX : Fields := gaussFields ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

def ndPr : Primes ndX := gaussianPrimesLarge ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

theorem ndPr_alt (u : ndPr.Word) : ndPr.T u = 763521676554817 := rfl

end Formalism.L2.Col
