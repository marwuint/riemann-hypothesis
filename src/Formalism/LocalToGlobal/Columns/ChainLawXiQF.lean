import Formalism.LocalToGlobal.Columns.UnfoldingPhiCompLeftUnipotentSource
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.CompSymmComp
import Formalism.LocalToGlobal.Columns.CqCard

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_chrOk_holds (hc : cst.Ok) {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hd : TwDegOne X w.1) (hi : i + 2 ≤ R.m)
    (hD : i + 1 ≤ cst.D w) {hal : AutY X R i} {h : AutY X R (i + 1)} (hba : TwBdd (Pr := Pr) i w.1 hal)
    (hbb : TwBdd (Pr := Pr) (i + 1) w.1 h) (hint : prCat (Pr := Pr) cst.sharp (i + 1) w.1 h ≤ GLint X.E (R.N (i + 1)) w.1)
    (hne : FiniteSumNonzeroLargeDepth Ch sel mu cst i w hal h) : TwChrOk Ch sel mu cst (i + 1) w h :=
  clXQ_chrOk_of cq_covT hc hw hd hi hD hba hbb hint hne

end Formalism.L2.Col
