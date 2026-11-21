import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrOfConjRes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceNormVEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RoadU

open UpperTheory.V.Af in

theorem frobEig_of_dec {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π : CuspSub E a) (Q : GlobalTheory.RealGal.QCM E Ω) (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l))
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hdec : ∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.K).range)
    (hsph : ∀ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w → (CG.mk P).HasSat w' B → SphAt .unr P ι r w' B)
    (hP : IsLift π P) (hB : (CG.mk π).HasSat w B) (hiso : RepIso r (ρ.comp (Bc.res E Ω ↥Q.K)))
    (hunr : ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1) :
    FrobEig ι ρ w (algSat a (normV w) B) := by
  intro A hA
  refine ⟨hunr A hA, fun σ hσ => ?_⟩
  obtain ⟨w', hw', hA', hq⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA (hdec A hA)
  obtain ⟨τ, rfl⟩ := hdec A hA hσ.1
  have hτ : IsFrob (F := ↥Q.K) A (normV w') τ := by
    rw [hq]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 ↥Q.K) ∉ w'.asIdeal := by
    intro h
    apply hl
    rw [← hw']
    change ((l : ℕ) : 𝓞 E) ∈ Ideal.comap (algebraMap (𝓞 E) (𝓞 ↥Q.K)) w'.asIdeal
    simpa using h
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hw', hq]) (by rw [hw']; exact hB)
    simpa using this
  have key := ((hsph w' hw' hB' hl') A hA').2 τ hτ
  obtain ⟨g, hg⟩ := hiso
  have e : ρ (Bc.res E Ω ↥Q.K τ)⁻¹ = g * r τ⁻¹ * g⁻¹ := by
    rw [← map_inv]
    exact hg τ⁻¹
  rw [e, ← hq, ← key, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

end GlobalTheory.RoadU
end
