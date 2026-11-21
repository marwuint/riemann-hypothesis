import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_smul' (c : ℂ) (f : UA E a →₀ ℂ) (φ : UA E a → ℂ) : opOf (RU E a) (c • f) φ = c • opOf (RU E a) f φ := by
  have e : ∀ f : UA E a →₀ ℂ, opOf (RU E a) f φ = Finsupp.linearCombination ℂ (fun g => RU E a g φ) f := fun f =>
    (Finsupp.linearCombination_apply ℂ f).symm
  rw [e, e, map_smul]

theorem core (hT : ToPolyX) (hC : Combine) (hR : Restrict) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (hK : K ≤ finU E a) (lam : (E →+* ℂ) → DomWeight a)
    (S : Type) [Fintype S] (Gn : S → Submodule ℂ (UA E a → ℂ) → Prop) (P : Submodule ℂ (UA E a → ℂ) → Prop)
    (hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w, Gn w U) (hP : Dense ι (Wt.ofFam lam) K P)
    (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) (hact : ActsBy K t η)
    (f : S → (UA E a →₀ ℂ)) (e : S → Submodule ℂ (UA E a → ℂ) → ℂ)
    (hf : ∀ w U, IsAutRepU U → (∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) (f w) φ = e w U • φ) ∧
        ((∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) → (e w U ≠ 0 ↔ Gn w U)))
    (hF : FramedX ι (Wt.ofFam lam) (Sum.elim t f)) (U : Submodule ℂ (UA E a → ℂ)) (hU : OfType lam K U) :
    PolyApprox (fun j => ι.symm (η U j))
      {θ | ∃ U', OfType lam K U' ∧ P U' ∧ (∀ w, Gn w U') ∧ θ = fun j => ι.symm (η U' j)} := by
  classical
  let η' : Submodule ℂ (UA E a → ℂ) → J ⊕ S → ℂ := fun U => Sum.elim (η U) fun w => e w U
  have hact' : ActsBy K (Sum.elim t f) η' := by
    intro U hU φ hφ hfix j
    cases j with
    | inl j => exact hact U hU φ hφ hfix j
    | inr w => exact (hf w U hU).1 φ hφ hfix
  let Q : MvPolynomial (J ⊕ S) ℤ := ∏ w : S, MvPolynomial.X (Sum.inr w)
  have hQ : ∀ U', OfType lam K U' → (MvPolynomial.aeval (fun j => ι.symm (η' U' j)) Q ≠ 0 ↔ ∀ w, Gn w U') := by
    intro U' hU'
    simp only [Q, map_prod, MvPolynomial.aeval_X, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff]
    refine forall_congr' fun w => ?_
    rw [← (hf w U' hU'.aut).2 hU'.fix]
    exact map_ne_zero_iff _ ι.symm.injective
  have h1 := hT E l ι a w₀ K hK lam _ hG _ _ η' hF hact' U hU
  have h2 := hC (Qbar l) _ _ _ {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η' U' j)} Q h1 (by
    rintro _ ⟨U', hU', hg, rfl⟩
    exact ⟨(hQ U' hU').2 hg, hT E l ι a w₀ K hK lam _ hP _ _ η' hF hact' U' hU'⟩)
  refine (hR (Qbar l) J _ Sum.inl _ _ h2).mono ?_
  rintro _ ⟨_, ⟨⟨U', hU', hp, rfl⟩, hq⟩, rfl⟩
  exact ⟨U', hU', hp, (hQ U' hU').1 hq, rfl⟩

theorem part_mono (W : Wt E a) (C : Subgroup (UA E a)) {P Q : Submodule ℂ (UA E a → ℂ) → Prop} (h : ∀ U, P U → Q U) :
    part W C P ≤ part W C Q :=
  iSup₂_le fun π hπ => le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : Q π.V) => π.finPart W ⊓ fixedBy W C) π (h _ hπ) le_rfl

end UpperTheory.Gal.Gen

end
