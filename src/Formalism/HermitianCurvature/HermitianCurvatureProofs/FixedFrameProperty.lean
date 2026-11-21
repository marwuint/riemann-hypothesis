import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

theorem fixed_frame_property : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]

end Formalism.FourierDecayAlt.P
