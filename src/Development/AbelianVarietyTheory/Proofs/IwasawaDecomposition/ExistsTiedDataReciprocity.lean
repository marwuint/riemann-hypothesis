import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtraTiedCol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsTwTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem ColW.cf_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    Fr.at (w.st Z) f = TC.cf w.I w.l Z := by
  have h := w.C_eq
  have : Fr.at (w.st Z) w.I.C = TC.cf w.I w.l Z := rfl
  rw [← this, h]

end GlobalTheory.Mem.Top.Bl
