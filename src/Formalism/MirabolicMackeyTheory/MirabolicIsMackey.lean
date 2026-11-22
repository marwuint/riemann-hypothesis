import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.MirabolicMackeyTheory.StatementL
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnLocal
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms

namespace Formalism.EigenvalueLevelCeiling

theorem idxMono : IdxMono := index_monotone
theorem idxScaleIn : IdxScaleIn := index_scale_inclusion
theorem idxCutLe : IdxCutLe := index_truncation_le
theorem idxTransport : IdxTransport := index_transport
theorem latInter : LatInter := lattice_intersection
theorem threeForms : ThreeForms := three_forms
theorem idxPsiGood : IdxPsiGood := idxPsiGood_of idxMono idxScaleIn idxCutLe latInter
theorem lemmaGG : LemmaGG := good_index_GG
theorem mirabolicIsMackey : MirabolicIsMackey := mirabolic_is_mackey
theorem onLocal : OnLocal := onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG
theorem ramBasic : RamBasic := ramified_basic_bound
end Formalism.EigenvalueLevelCeiling
