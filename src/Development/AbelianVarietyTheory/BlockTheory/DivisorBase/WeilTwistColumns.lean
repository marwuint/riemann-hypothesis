import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTwistColumns

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end Period

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Theta

section Const

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def colAt {V W : HSp D} (hr : W.rank = r) {Ψ : Finset (D.host.E →+* ℂ)}
    (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (w : WO V W) (b : Fin V.rank) : Ψ → Fin r → ℂ :=
  fun τ a => th τ (infPart D (w (Fin.cast hr.symm a) b))

def cXi {n : ℕ} (d : DeltaDat Xo c n) {W : HSp D}
    (U₂ : Unf d.Xo₂ d.c₂ (σ.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D W → Σ k, Frame (U₂.X k).Ψ r)
    (h : GA D W) : ℂ :=
  rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2

end Const

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def WeilTwist : Prop :=
  R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (t : T0) (h : GA D (Vc D i)) (g : GA D (Wc D i)) (y x : (AE D)ˣ),
    IsDetRoot (Vc D i) h y → IsDetRoot (Wc D i) g x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      R.ωP i t (h, g) f = (((R.xi t x * (R.xi t y)⁻¹ : Circle)) : ℂ) • R.ωP i A.μ0 (h, g) f

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  (U : Unf Xo c σ D.R.r) (dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) {g : ℕ}
  (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
  (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
  (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  (dδ : T0 → DeltaDat Xo c (Vc D i).rank)
  (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r)
  (dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.WeilTwistColumns
