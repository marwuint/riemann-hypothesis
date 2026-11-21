import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

omit [NumberField F] in

def WitAQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

theorem guard_of (H : PlainRec) [IsCMField F] [IsAlgClosure F Ω] {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub F n} (hreg : (CG.mk π).IsRegAlg) (ha : AttC ι r π) (hW : WitA ι r) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRecT h rc) {σ : SmIrr (GL (Fin n) (w.adicCompletion F))}
    (hσ : π.IsLocComp w σ) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ UpperTheory.GalStar.Tor (rc (algNorm σ)) ∧ (rc (algNorm σ)).mono0 := by
  obtain ⟨t, ht⟩ := hW.2 π hreg ha
  refine H F Ω A w h rc hrc n π t (ht w ?_) σ hσ
  by_cases e : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
  · exact Or.inr ((hw.resolve_left fun k => k e).elim (hW.1 w e) id)
  · exact Or.inl e

def ThruAway : Prop := PlainRec → Thru false
def AIsoTwOf : Prop := FlagLaws → WinTw → AIsoTw
end UpperTheory.V.Z.Win
