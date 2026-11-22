import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HartogsUnit

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def toFrac (p : Ideal A) [p.IsPrime] : Localization.AtPrime p →+* FractionRing A :=
  IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
    (g := algebraMap A (FractionRing A))
    (fun s => IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors s.2)))

theorem toFrac_comp (p : Ideal A) [p.IsPrime] :
    (toFrac p).comp (algebraMap A (Localization.AtPrime p)) = algebraMap A (FractionRing A) :=
  IsLocalization.lift_comp _

theorem toFrac_mem (p : Ideal A) [p.IsPrime] (w : Localization.AtPrime p) :
    ∃ s, s ∉ p ∧ s • toFrac p w ∈ (algebraMap A (FractionRing A)).range := by
  obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
  refine ⟨s, s.2, m, ?_⟩
  have h := congrArg (toFrac p) e
  simp only [map_mul] at h
  rw [← RingHom.comp_apply (toFrac p), ← RingHom.comp_apply (toFrac p), toFrac_comp] at h
  rw [Algebra.smul_def, mul_comm, h]

end GlobalTheory.HartogsUnit
