import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

namespace GlobalTheory.Published

def LanglandsSumMultiplicityOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (𝔪 𝔫 : Multiset (Segment k)) (r t : ℕ) (π₁ : IrrRep (GL (Fin r) k)) (π₂ : IrrRep (GL (Fin t) k)),
    IsL 𝔪 π₁.ρ → IsL 𝔫 π₂.ρ →
      (∃ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
        ∀ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  {𝔪 𝔫 : Multiset (Segment k)} {r t : ℕ} {π₁ : IrrRep (GL (Fin r) k)} {π₂ : IrrRep (GL (Fin t) k)}

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}

theorem IsRec.segment (H : IsRec h rc) {Δ : Segment (w.adicCompletion E)} {x : IrrGL (w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) : rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  exact (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)

theorem IsRec.langlandsQuotient (H : IsRec h rc) {𝔪 : Multiset (Segment (w.adicCompletion E))} {s N : ℕ}
    {δ : Fin s → IrrGL (w.adicCompletion E)} (hδ : LFactors 𝔪 δ) (hd : ∑ i, (δ i).1 = N)
    {π : IrrRep (GL (Fin N) (w.adicCompletion E))} (hπ : IsCosocle π.ρ (prodIrr δ hd)) :
    rc (cls π) = sumList (List.ofFn fun i => rc (δ i)) := by
  have h1 : IsL 𝔪 (cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  simp only [fun i => H.segment (hΔ i)]
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.langlands (List.ofFn Δ) (cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl

theorem IsRec.prod (H : IsRec h rc) {r t : ℕ} (σ : IrrRep (GL (Fin r) (w.adicCompletion E)))
    (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E)))
    (φ : π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) : rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) :=
  let ⟨_, _, _, _, H⟩ := H; H.prod r t σ τ π ⟨φ⟩

end GlobalTheory.LocLanglands

end
