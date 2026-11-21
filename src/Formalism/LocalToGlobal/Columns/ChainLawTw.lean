import Formalism.LocalToGlobal.Columns.ChainLawXi
import Formalism.LocalToGlobal.Columns.ChainLawPhi
import Formalism.LocalToGlobal.Columns.ChainLawPhiPf
import Formalism.LocalToGlobal.Columns.XiFirstLawAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.CompSymmComp
import Formalism.LocalToGlobal.Columns.ChainTwMain
import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.WithTopLevGTop

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TopG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clW_lamGBS_lamJsym {K : Type} [Field K] (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {n k₀ r t j rS : ℕ} (hr : r = k₀ + 2 * rS + 1) (ht : 0 < t) (hn : r + j * t ≤ n) (h : r ≤ n) (hkr : k₀ < r)
    (M : ↥(HJsym (𝓞 E ⧸ P.asIdeal) n k₀ r t j rS h)) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P)
    (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = M.1.1.mulVec (redV P x)) :
    LocE.lamGBS q ψ₀ χ k₀ r t j n 0 κ.toLinearMap = ((lamJsym ψ₀ χ n k₀ r t j rS h M : Kˣ) : K) := by
  subst hr
  apply σ₀.injective
  rw [ctl_lamGBS_lamJ (RingEquiv.refl _) σ₀ ψ₀ χ hkr hn hκ hred, ctl_lamJsym_lamJ σ₀ ψ₀ χ ht hn h M]

end TopG

end Formalism.L2.Col
