import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem RealSide.space_eq {D : D7} (X : RealSide D) (j : Fin D.R.m) :
    X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
  X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀

end GlobalTheory.TwInputs

end
