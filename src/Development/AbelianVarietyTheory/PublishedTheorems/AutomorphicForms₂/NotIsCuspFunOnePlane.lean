import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay.Model

variable {D : D7}

theorem isCuspFun_zero (V : HSp D) : IsCuspFun V fun _ => 0 := fun _ _ _ _ _ _ _ _ => by simp

def line (D : D7) : HSp D := Examples₂.posSpace Examples₂.star_isIntegral 1

theorem isClosed_NI (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) :
    IsClosed (NI V C : Set (GA D V)) := by
  obtain ⟨L, hL, -⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm V C hC.2.1 hC.2.2
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : T2Space (AF D.host.F ⊗[D.host.F] D.host.E) :=
    .of_injective_continuous (f := (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun.toLinearMap)
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  rw [GlobalTheory.AutFunCompare.NI_eq]
  have hcl : IsClosed {g : GA D V |
      ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) * (C * L).map (inclR (F := D.host.F) (AF D.host.F)) = 0 ∧
      (1 - (C * L).map (inclR (F := D.host.F) (AF D.host.F))) * ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) *
        (1 - GlobalTheory.AutFunCompare.adj D.sp.cm V ((C * L).map (inclR (F := D.host.F) (AF D.host.F)))) = 0} :=
    (isClosed_eq ((hm.sub continuous_const).matrix_mul continuous_const) continuous_const).inter
    (isClosed_eq ((continuous_const.matrix_mul (hm.sub continuous_const)).matrix_mul continuous_const) continuous_const)
  convert hcl using 1
  exact Set.ext fun g => GlobalTheory.AutFunCompare.mem_unipRad_idem D.sp.cm V C L hL g

end GlobalTheory.CuspDecay.Model

end
