import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneAddSubOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitDetRoot

theorem infPart_sigR_one (D : D7) (x : AE D) (hx : infPart D x = 1) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = 1 := by
  have h := GlobalTheory.DetRootCong.map_sigR (F := D.host.F) (E := D.host.E)
    (AlgHom.fst D.host.F (InfiniteAdeleRing D.host.F) (Af D.host.F)) D.sp.cm.sig x
  refine h.trans ?_
  exact (congrArg _ hx).trans (map_one _)

end GlobalTheory.UnitDetRoot
