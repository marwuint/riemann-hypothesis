import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idealLatHat (V : HSp D) (I : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ b ∈ I, ∃ z ∈ latGHat V 1, w = halfVec V b z}

def IsLift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (g : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) (k : GA D V) : Prop :=
  k ∈ GfC V ∧ gLat V k = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
    ∀ a b : Dw.La, (Submodule.Quotient.mk b : LaMod Dw l) = g (Submodule.Quotient.mk a) →
      (finHom V k).1.mulVec (finVec V (ι a)) - finVec V (ι b) ∈ idealLatHat V l.Mb

abbrev LevGrp (T : CoreJ D) (j : ℕ) : Type :=
  LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def iotaAt (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (hr : (T.V j σ).rank = D.R.r) :
    (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

def IsChiDet (T : CoreJ D) (j : ℕ) {V : HSp D} (ℓ : LevGrp T j → GA D V) (chi : LevGrp T j →* T.Q.c.Fˣ) : Prop :=
  ∀ g x, FinUnit x → IsDetRoot V (ℓ g) x →
    T.σ₀ ((chi g : T.Q.c.Fˣ) : T.Q.c.F) * ((T.chiW j T.σ₀ x : Circle) : ℂ) = 1

end GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
