import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConstantCoeffFormalSum
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.SclY

noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem k1gen_of_orth {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) {be : MvPowerSeries (Fin 2) (K0 l)} (hB : BeProp l be)
    {g2 g3 ε s2 : MaximalUnramifiedExtension l} (hC : CurveAt l be g2 g3 ε s2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]} (hO : OrthInt l g2 g3 s2 ε Th) :
    @ExtensionGeneratorCondition l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be Th := by
  obtain ⟨hg2, hg3, hε, hθ, hN, hbe0, F, hF, hTie⟩ := hC
  obtain ⟨r, Θ, σ, f, f', hσ, hP, rfl, hI⟩ := hO
  have hInt := hyperbolic_of_orthogonal l h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hσ F hF (hN σ hσ) ι (Fin r) f f' hP be hbe0 hTie Θ hI
  exact @first_kernel_of_sum l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be _ hB (sum_beta_even l (by omega) ι be hB) hInt

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem curveDict_data (hCD : CurveDict) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime]
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g) (hA : Formalism.MainNotions.GL3Theta.At D cc δ g) (h5 : 5 ≤ p)
    (hIn : Formalism.MainNotions.GL3Theta.InertK D p) (hM : Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C) :
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension p, CurveAt p (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : D7, DictInt D' g.lam g.abelian₂ (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε := by
  obtain ⟨g2, g3, ε, s2, h⟩ := hCD D cc δ p g hLT hA h5 hIn hM
  exact ⟨g2, g3, ε, s2, by tauto⟩

theorem thOrth_sclY {p : ℕ} [Fact p.Prime] {N N' r : ℕ} (D : D7) (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    thOrth D lam 1 b (sclY c G) = thOrth D lam c b G := by
  have ha : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      (MvPowerSeries.C c * MvPowerSeries.X k : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have hb : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      ∑ i, MvPowerSeries.C ((1 : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold thOrth sclY
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hb, map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C,
    MvPowerSeries.subst_X hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, one_mul]

end Glob

end Formalism.L2.KerInert.Rep
