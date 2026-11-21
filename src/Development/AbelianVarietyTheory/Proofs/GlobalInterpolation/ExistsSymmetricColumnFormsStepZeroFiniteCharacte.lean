import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsTiedSymChiZeroFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimitiveRootsCoeffFieldTrueColumns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem colsTiedSym_chiFin0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ C : ColsTiedSym (I.rec7 l Z), ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u) := by
  intro B X I hI hP l Z
  obtain ⟨C, -, -⟩ := _root_.GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hI hP l Z
  refine ⟨C, fun u => ?_⟩
  exact GlobalTheory.formsTiedSym_chi_zero_finite (I.rec7 l Z) u _ _ (C.forms u)
    (fun i => _root_.GlobalTheory.trueCols_exists_primitiveRoots I hI l Z i)

end GlobalTheory.Mem.Col2.TC
