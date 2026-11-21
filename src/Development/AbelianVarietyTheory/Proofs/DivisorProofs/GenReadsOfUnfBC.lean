import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem genReads_of_unfBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r g : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((U (σ'.comp (incF c c' hle))).X k).Λ)
    (idx : Fin g ≃ ((U (σ'.comp (incF c c' hle))).X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : ((U (σ'.comp (incF c c' hle))).X k).dom) (ϑ : (Fin g → ℂ) → ℂ)
    (h : GenReads (unfBC hle U σ') k bas idx e x ϑ) : GenReads (U (σ'.comp (incF c c' hle))) k bas idx e x ϑ := by
  obtain ⟨B, hB⟩ := h
  letI : Algebra c.F ℂ := (σ'.comp (incF c c' hle)).toAlgebra
  letI : Algebra c'.F ℂ := σ'.toAlgebra
  exact ⟨⟨B.ex, B.ex_add, B.ex_onto, B.ex_ker, B.ex_lin, B.hol, B.der, B.fr, B.fr_hol, B.fr_ne, B.fr_g, B.fr_0, B.χ,
    B.χ_norm, B.fr_per⟩, hB⟩

theorem CcIs.unfBC {D : D7} (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ)
    (dict : GA D W → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D W → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ)
    (h : CcIs θ V W hr (U (σ'.comp (incF c c' hle))) dict mu x₀ om f₀ cc) :
    CcIs θ V W hr (Formalism.L2.Pj.unfBC hle U σ') dict mu x₀ om f₀ cc := by
  refine ⟨h.1, fun a γ hA hx' g bas idx e hs hi ϑ hϑ w hw => ?_⟩
  have hrel : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  have hi' : IdxIs c (σ'.comp (incF c c' hle)) ((U (σ'.comp (incF c c' hle))).X (dict a).1) idx e := by
    unfold IdxIs at hi ⊢
    rw [hrel] at hi
    exact hi
  exact h.2 a γ hA hx' g bas idx e hs hi' ϑ (genReads_of_unfBC hle U σ' _ bas idx e ⟨_, hx'⟩ ϑ hϑ) w hw

end GlobalTheory.AdTh
