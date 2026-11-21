import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlusRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev NormDatum (B : WeightFamilies.Prov D) := GlobalTheory.RunIn.SecNorm B

namespace NormDatum
variable (n : NormDatum B)

abbrev B' : WeightFamilies.Prov D := GlobalTheory.RunIn.SecNorm.base n

abbrev X' (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D n.B' P j := xplusN n.N n.h0 n.h1 n.h2 n.h3 n.h4 X E hM

end NormDatum

end GlobalTheory.PlusRec
