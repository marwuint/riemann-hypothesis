import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionCuspidalOfRapidDecayHolomorphicType

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem holForm_zCusp_of_mem_mult : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, HolForm θ M w J χ (T v) ∧ ZCusp V (T v) := by
  intro hP D θ V S M w v hθ hM hw hv J χ T hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  have hd := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ (h.aut v) (h.cusp v)
  have hh := _root_.GlobalTheory.MultHol.holAd_of_isMultMap D θ V S M w v hθ hM hw hv J χ T h
  exact ⟨⟨(h.aut v).toIsAutFun, hd.bounded, h.lev v, hh⟩,
    _root_.GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay D θ V S M w hθ hM _ (h.aut v).toIsAutFun hh hd⟩

end GlobalTheory.HolDict
