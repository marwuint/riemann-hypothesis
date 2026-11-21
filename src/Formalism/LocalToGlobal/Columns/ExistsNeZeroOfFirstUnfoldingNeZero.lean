import Formalism.LocalToGlobal.Columns.ChainTwAux
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwE1JMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

def twOmS (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu c i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu c i P (LinearEquiv.det g : X.Eˣ))⁻¹ *
    c.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * ((R.N (i + 1) + cOf R (i + 1) : ℕ) : ℤ)) *
    c.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det g : X.Eˣ) * ((R.N i + cOf R i : ℕ) : ℤ))

theorem twOmPhi_eq (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu c i P hal g x = twOmS (Ch := Ch) c i P hal g * PhiAt Ch mu c.sharp i P.1 (g.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) :=
  rfl

end TwE1JMain

end Formalism.L2.Col
