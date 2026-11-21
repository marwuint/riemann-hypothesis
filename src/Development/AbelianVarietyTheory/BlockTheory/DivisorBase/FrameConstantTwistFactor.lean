import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameConstantVectors

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.FD (Frame)

section Cover

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c' : Coeff l} {n r : ℕ}

def cXi (W : HSp D) (σ' : c'.F →+* ℂ) (d : DeltaDat Xo c' n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ'.comp (d.eF.symm : d.c₂.F →+* c'.F)) r)
    (dict₂ : GA D W → Σ k, Frame (U₂.X k).Ψ r) (g : GA D W) : ℂ :=
  rdU U₂ d.cδ (dict₂ g).1 (dict₂ g).2

end Cover

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def WeilTwist (t : T0) : Prop :=
  ∀ (h : GA D (Vc D i)) (g : GA D (Wc D i)) (y x : (AE D)ˣ), IsDetRoot (Vc D i) h y → IsDetRoot (Wc D i) g x →
    ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      R.ωP i t (h, g) f = (((R.xi t x * (R.xi t y)⁻¹ : Circle) : ℂ)) • R.ωP i A.μ0 (h, g) f

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.FrameConstantVectors

end
