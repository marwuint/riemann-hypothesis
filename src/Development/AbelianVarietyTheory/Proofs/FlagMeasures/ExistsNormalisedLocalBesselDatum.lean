import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem exists_isStdOf (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hk : 1 ≤ k) (hsec : IsSection k r L.z L.z' μsec) :
    ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨χ, hχs, hχsupp, hχint⟩ := P.character_exists_alt
  have h1 := _root_.GlobalTheory.ThA.hcType_rep k r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  have h1' := _root_.GlobalTheory.ThA.hcType_rep k r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hW := _root_.GlobalTheory.ThA.haarW_twoSided_of_left k r L.z L.μW L.hz.1 L.hz.2 L.hμW.1 L.hμW.2
  have hW' := _root_.GlobalTheory.ThA.haarW_twoSided_of_left k r L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2
  have hN := P.Dx2.MN.haar (k := k) r
  exact ⟨⟨L.z, L.z', L.π, L.π', μG, L.μW, D.muN k r, L.μW', μsec, χ, hk, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
    h1.2.1, h1'.2.1, h1.2.2.2.1, h1'.2.2.2.1, h1.2.2.1, h1'.2.2.1, hμG, hW, hN, hW', hsec, hχs, hχsupp, hχint⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ThA
