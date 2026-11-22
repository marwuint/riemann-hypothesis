import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace

noncomputable section

namespace GlobalTheory.TripleGal

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf)

def rk1 {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) : Γ →* GL (Fin 1) K :=
  (Units.map (Matrix.scalar (Fin 1) : K →+* Matrix (Fin 1) (Fin 1) K).toMonoidHom).comp χ

def CharAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
      IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧ IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype)) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)}

end GlobalTheory.TripleGal

end
