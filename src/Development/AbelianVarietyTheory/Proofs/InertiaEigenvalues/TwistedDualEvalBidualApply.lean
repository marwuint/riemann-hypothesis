import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DualSide

section Dual

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]

theorem finite_TDual [Finite R] [Finite M] : Finite (TDual R M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := TDual R M))

def evalBidual : M →ₗ[R] TDual R (TDual R M) := evalPair

@[simp] theorem twistedDual_evalBidual_apply (m : M) (φ : TDual R M) :
    (evalBidual m : TDual R (TDual R M)) φ = φ m := rfl

variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]

theorem contAction_twDual [TopologicalSpace Γ] [ContinuousInv Γ] [Finite M] {χ : Γ →* Rˣ}
    {rho : Representation R Γ M} (hχ : ContAction (charRep χ)) (h : ContAction rho) :
    ContAction (twDual χ rho) := by
  have h1 : Continuous fun (p : Γ × TDual R M) (m : M) => twDual χ rho p.1 p.2 m :=
    continuous_pi fun m => hχ.comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun q : TDual R M × M => q.1 q.2)).comp
        (continuous_snd.prodMk (h.comp (continuous_fst.inv.prodMk continuous_const)))))
  exact (IsLocallyConstant.desc _ (fun (φ : TDual R M) (m : M) => φ m)
    ((IsLocallyConstant.iff_continuous _).2 h1) DFunLike.coe_injective).continuous

variable {D : Type*} [Group D] [TopologicalSpace D]

end Dual

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
  {Av : S → ValuationSubring Ω}
  {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
  {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M]
  {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}

omit [TopologicalSpace M] [DiscreteTopology M] in
theorem finite_TDual_pow : Finite (TDual (ZMod (l ^ r)) M) :=
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  finite_TDual

end Global

end GlobalTheory.DualSide
