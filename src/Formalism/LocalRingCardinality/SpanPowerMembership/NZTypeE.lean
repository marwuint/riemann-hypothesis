module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain

theorem monicOf_injective {K : Type} [Field K] {N : ℕ} : Function.Injective (monicOf (K := K) (N := N)) := by
  intro a b h
  funext i
  have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
  simpa [monicOf, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Fin.val_inj,
    (Fin.is_lt i).ne] using h2

variable {R : Ranks} {H : Host R}

theorem neZero_g (k : Fin 2) : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩

theorem fact_g (k : Fin 2) : Fact (H.g k).Prime := ⟨H.g_prime k⟩

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {what₂ : Rows.Data R} (N : NData R H what₂)

abbrev Ix : Type := Σ k : Fin 2, N.PlG k

def GoodT (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (fun v j => (N.chiT k v j)⁻¹)

variable {K : Type} [Field K]

def e0F (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k)))) :
    MonoidAlgebra K (G0g N) :=
  eSum (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (monicOf a))
    (fun a => GoodT N fun k v => monicOf (a ⟨k, v⟩))

variable (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
  (hidem : ∀ k f, es k f * es k f = es k f) (hcen : ∀ k f a, es k f * a = a * es k f)
  (horth : ∀ k f f', f ≠ f' → es k f * es k f' = 0)

include hcen in
theorem seriesIdempotent_central (a : MonoidAlgebra K (G0g N)) : e0F N es * a = a * e0F N es := by
  unfold e0F
  apply eSum_central
  intro i x b
  exact hcen i.1 (monicOf x) b

include hidem horth in
theorem seriesIdempotent_idem : e0F N es * e0F N es = e0F N es := by
  unfold e0F
  apply eSum_idem
  · exact fun i x => hidem i.1 (monicOf x)
  · exact fun i x y hxy => horth i.1 _ _ (fun h => hxy (monicOf_injective h))


variable {N}

theorem e0_eq {A : NAut N} (X : NTypes A) : X.e0 = e0F N X.eSer := by
  apply MonoidAlgebra.ext
  ext g
  rw [e0F, eSum_coeff]
  simp only [Formalism.BasicNotions.NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  rfl

theorem idempotent_mem_center {A : NAut N} (X : NTypes A) :
    X.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  rw [e0_eq X, Subalgebra.mem_center_iff]
  exact fun b => (seriesIdempotent_central N X.eSer X.eSer_central b).symm

theorem idempotent_sum {A : NAut N} (X : NTypes A) : X.e0 * X.e0 = X.e0 := by
  rw [e0_eq X]
  exact seriesIdempotent_idem N X.eSer X.eSer_idem X.eSer_orth

end Formalism.BasicNotions.Examples₂.NZ
