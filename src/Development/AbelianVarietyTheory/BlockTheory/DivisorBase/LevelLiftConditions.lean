import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l

def levDet (Dw : Datum H) (l : Level H) : LevGrp Dw l →* (𝓞 E ⧸ l.Mb)ˣ where
  toFun γ := LinearEquiv.det
    (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ l.Mb) Ideal.Quotient.mk_surjective)
  map_one' := by
    rw [← map_one (LinearEquiv.det (R := 𝓞 E ⧸ l.Mb) (M := LaMod Dw l))]
    rfl
  map_mul' γ δ := by
    rw [← map_mul]
    rfl

end Level

variable {D : D7}

def idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ b ∈ I, ∃ y ∈ intAE D, z = ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * y}

def CongMod (I : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) (u : 𝓞 D.host.E) : Prop :=
  finPart D (x : AE D) - (1 : Af D.host.F) ⊗ₜ (u : D.host.E) ∈ idealHat D I

def IsInvTame {K : Type} [Field K] (σ : K →+* ℂ) (Mb Mc : Ideal (𝓞 D.host.E)) (μ : (AE D)ˣ →* Circle)
    (χ : (𝓞 D.host.E ⧸ Mb)ˣ →* Kˣ) : Prop :=
  ∀ x : (AE D)ˣ, FinUnit x → ∀ (u : 𝓞 D.host.E) (ub : (𝓞 D.host.E ⧸ Mb)ˣ),
    (ub : 𝓞 D.host.E ⧸ Mb) = Ideal.Quotient.mk Mb u → CongMod Mb x u → CongMod Mc x 1 →
      σ ((χ ub : Kˣ) : K) * ((μ x : Circle) : ℂ) = 1

def IsLevLift {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
    ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a) →
      ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = (l.M : ℕ) • w

end GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions
