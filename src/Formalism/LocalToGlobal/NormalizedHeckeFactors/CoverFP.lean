import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverF

open Formalism.BasicNotions

namespace Formalism.L2

theorem linkEtaTw_of_plain {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hP : HeckeStdPlain)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := h
  refine locsCoverTwF_of Fm ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hex⟩ := hx x hx' i
  exact ⟨M, T, heckeStd_of_plain T hP HT hex (genOutBad_of T)⟩

end Formalism.L2
