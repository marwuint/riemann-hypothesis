import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts SameModel modVec resImage ResField)

theorem coe_subringCongr {R : Type*} [Ring R] {s t : Subring R} (h : s = t) (x : s) :
    ((RingEquiv.subringCongr h x : t) : R) = x :=
  rfl

theorem coe_subringCongr_symm {R : Type*} [Ring R] {s t : Subring R} (h : s = t) (x : t) :
    (((RingEquiv.subringCongr h).symm x : s) : R) = x :=
  rfl

section Transport

variable {S : Type*} [CommRing S] {L L' : Type*} [Field L] [Field L'] [Algebra S L] [Algebra S L']

theorem chartRingOver_comp {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k) :
    chartRingOver S (fun q => φ (v q)) c = (chartRingOver S v c).map (φ : L →ₐ[S] L') := by
  unfold chartRingOver
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  congr 1
  ext u
  simp [map_div₀]

noncomputable def chartEquiv {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k) :
    chartRingOver S v c ≃ₐ[S] chartRingOver S (fun q => φ (v q)) c :=
  (φ.subalgebraMap (chartRingOver S v c)).trans (Subalgebra.equivOfEq _ _ (chartRingOver_comp φ v c).symm)

theorem chartEquiv_coe {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k)
    (a : chartRingOver S v c) : (chartEquiv φ v c a : L') = φ a :=
  rfl

end Transport

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
