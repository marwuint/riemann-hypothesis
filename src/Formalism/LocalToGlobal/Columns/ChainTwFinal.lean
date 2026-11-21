import Formalism.LocalToGlobal.Columns.ExistsNeZeroOfFirstUnfoldingNeZero
import Formalism.LocalToGlobal.Columns.ChainLawXiQF

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwFinal

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem characterNonvanishing_holds {G : ChGlob X R.m} {m2 : ℕ} (hm : R.m = m2 + 2) (hc : (twCst Ch sel mu G).Ok) :
    TwChrNFQ Ch sel mu (twCst Ch sel mu G) m2 := by
  intro i hi P hP hd hal h hba _ hbb _ hint hne
  exact clXQ_chrOk_holds hc hP hd (by omega) (by rw [twCst_D_Q hP]; omega) hba hbb hint hne

end TwFinal

end Formalism.L2.Col
