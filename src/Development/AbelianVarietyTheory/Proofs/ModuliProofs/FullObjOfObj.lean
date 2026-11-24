module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ.rt_coe (S A : ℕ) : ((RZ.rt H S A : RZ H S A) : ℂ) = H.rt0 := by
  have h2 : ((2 : RZ H S A) : ℂ) = 2 := map_ofNat (RZ H S A).subtype 2
  unfold RZ.rt
  push_cast
  rw [h2]
  ring

theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (KA l))
    (o : Obj D l (baseKA l) s) (β : RZ H n l.A →+* KA l) (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) :
    FullObj D (s ≫ spMap β) o.t o.etaA := by
  unfold IsInc at hβ
  have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := by
    apply Subtype.ext
    show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0
    rw [← RZ.rt_coe (H := H) n l.A]
    exact hβ (RZ.rt H n l.A)
  have hze : β (RZ.ze H n l.A) = (baseKA l).ζ := Subtype.ext (hβ (RZ.ze H n l.A))
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩
  intro k _ _ _ x β' hx
  obtain ⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by
    refine ⟨(Spec.preimage (x ≫ s)).hom, ?_⟩
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : β' = g0.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β)) := by
      unfold spMap at hx hg0
      rw [← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hb
  obtain ⟨hdet, I, hI1, hI2, -⟩ := o.geom k x g0 hg0
  refine ⟨?_, I, ?_, hI2⟩
  · rwa [RingHom.comp_apply, hρ]
  · rwa [RingHom.comp_apply, hze]

end GlobalTheory.Models
