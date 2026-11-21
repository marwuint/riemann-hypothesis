import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApprox

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.StrongApproxSUProof

theorem strongApproxSU : StrongApproxSU := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg
  have h3 := _root_.GlobalTheory.SUAssemble.assemble _root_.GlobalTheory.PlaneSU.plane_closure _root_.GlobalTheory.PlaceIso.exists_isotropic_places F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces F E σ hcm M J hJ g hg)
  rintro x ⟨T₁, T₂, η, hη, hx⟩
  refine closure_minimal ?_ isClosed_closure (_root_.GlobalTheory.SUWeakApprox.weak_approx_SU F E σ hcm M J hJ T₁ T₂ η hη x hx)
  rintro y ⟨γ, hγ, hy⟩
  exact h3 T₁ T₂ η hη γ hγ y hy

end GlobalTheory.StrongApproxSUProof
