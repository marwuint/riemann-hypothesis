import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OAf (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def finR (V : HSp D) {r : ℕ} (hr : V.rank = r) : GA D V →* GL (Fin r) (EAf D) :=
  (Units.map (Matrix.reindexRingEquiv (EAf D) (finCongr hr)).toRingHom.toMonoidHom).comp (finE V)

def IsLatBasis (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) : Prop :=
  ∀ z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E, z ∈ latHat V ↔
    ∀ i, (Units.val (β⁻¹ : GL (Fin r) (EAf D))).mulVec
      (fun a => swapAE D (z (Fin.cast hr.symm a))) i ∈ OAf D

def IsLift (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (g : Formalism.L2.DIV.G0 Pg r) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ ∃ h : finR V hr κ ∈ Formalism.L2.DIV.St β, ∀ w : ↥Pg, Formalism.L2.DIV.redAt β w.1 ⟨finR V hr κ, h⟩ = g w

def chiDetG0 {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (Pg : Finset (Formalism.L2.DIV.Pl E)) (r : ℕ)
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ) : Formalism.L2.DIV.G0 Pg r →* Kˣ :=
  ∏ w : ↥Pg, (χ w).comp (Matrix.GeneralLinearGroup.det.comp
    (Pi.evalMonoidHom (fun w : ↥Pg => GL (Fin r) (Formalism.L2.DIV.kP w.1)) w))

def readAd (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c : (T.U j σ).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R j) (h : GA D (T.V j σ)) : ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (c (T.dict j σ h).1 * T.mu j σ h *
    rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2)

def levOf {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {G : Type} (γ : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La) (g : G) :
    (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La) :=
  (γ g, LinearMap.id)

def geoAct (T : Core D) (j : ℕ) {G : Type} [Group G] (γ : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) (g : G) :
    T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (levOf γ) g

def IntegralAt (T : Core D) (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (f : T.R j) : Prop :=
  ∀ y : T.PtM j la, T.nrmM j la y f ≤ 1

structure LevelActionLaws (T : CoreJ D) (j : ℕ) (β : GL (Fin D.R.r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* (T.Q.c.F)ˣ)
    (γ : Formalism.L2.DIV.G0 Pg D.R.r → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) : Prop where

  act : ActLev (Xo := T.Q.Xo j) T.Q.c (levOf γ)

  cusp : ∀ a n, Dom a n → ∀ g, ∀ f ∈ T.toCore.cuspA j a n, geoAct T.toCore j γ g f ∈ T.toCore.cuspA j a n

  lift : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) g, ∃ κ, IsLift (T.V j σ) hr β Pg g κ

  read : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) (n : ℕ), Even n →
    ∃ c : (T.U j σ).Comp → ℂ, CUnit c ∧ ∀ a, Dom a n → ∀ g κ, IsLift (T.V j σ) hr β Pg g κ →
      ∀ f ∈ T.toCore.cuspA j a n, ∀ h : GA D (T.V j σ),
        readAd T.toCore j σ c a (geoAct T.toCore j γ g f) h =
          σ ((chiDetG0 Pg D.R.r χ g : (T.Q.c.F)ˣ) : T.Q.c.F) * readAd T.toCore j σ c a f (h * κ)

  integral : ∀ a n, Dom a n → ∀ g, ∀ f ∈ T.toCore.cuspA j a n, ∀ la,
    IntegralAt T.toCore j la f → IntegralAt T.toCore j la (geoAct T.toCore j γ g f)

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
