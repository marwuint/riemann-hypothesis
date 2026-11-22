import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.TwoSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem range_le_comap (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (g : GL (Fin N) k) :
    LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (π g) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨σ g w, Representation.IntertwiningMap.isIntertwining _ _ f g w⟩

def quotRep (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) : Representation ℂ (GL (Fin N) k) (V ⧸ LinearMap.range f.toLinearMap) where
  toFun g := (LinearMap.range f.toLinearMap).mapQ _ (π g) (range_le_comap π σ f g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

@[simp] theorem quotRep_mk (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (g : GL (Fin N) k) (v : V) :
    quotRep π σ f g ((LinearMap.range f.toLinearMap).mkQ v) = (LinearMap.range f.toLinearMap).mkQ (π g v) := rfl

theorem mkQ_mem_twKer (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (U : Subgroup (GL (Fin N) k)) (θ : U →* ℂˣ) {v : V} (hv : v ∈ twKer π U θ) :
    (LinearMap.range f.toLinearMap).mkQ v ∈ twKer (quotRep π σ f) U θ := by
  have hle : twKer π U θ ≤ (twKer (quotRep π σ f) U θ).comap (LinearMap.range f.toLinearMap).mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, (LinearMap.range f.toLinearMap).mkQ u, ?_⟩
    simp only [LinearMap.map_sub, LinearMap.map_smul]
    rfl
  exact hle hv

theorem isSmooth_of_injective (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π) : IsSmooth σ := by
  intro w
  have : {g : GL (Fin N) k | σ g w = w} = {g | π g (f w) = f w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← Representation.IntertwiningMap.isIntertwining _ _ f g w, hf.eq_iff]
  rw [this]
  exact hπ _

theorem not_isGeneric_quotRep {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1) (hσ : IsGeneric σ) :
    ¬ IsGeneric (quotRep π σ f) := by
  rw [isGeneric_iff_isGenericFor hψ h1] at hσ ⊢
  have hσs := isSmooth_of_injective π σ f hf hπ
  unfold IsGenericFor at hσ ⊢
  rw [not_nontrivial_iff_subsingleton]

  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet σ (unipB k (Fin N)) (whitChar ψ N))
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hw : w ∉ twKer σ (unipB k (Fin N)) (whitChar ψ N) := fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)
  have hfw : f w ∉ twKer π (unipB k (Fin N)) (whitChar ψ N) := fun h =>
    hw (GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N σ π hσs hπ f.toLinearMap hf
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v) w h)
  obtain ⟨e, he⟩ := rank_le_one_iff.1 hr
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  obtain ⟨a, ha⟩ := he (Submodule.Quotient.mk (f w))
  obtain ⟨b, hb⟩ := he (Submodule.Quotient.mk v)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfw ((Submodule.Quotient.mk_eq_zero _).1 (by rw [← ha, zero_smul]))
  have hk : v - (b / a) • f w ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← ha, ← hb, smul_smul,
      div_mul_cancel₀ _ ha0, sub_self]
  have h2 := mkQ_mem_twKer π σ f _ _ hk
  have h3 : (LinearMap.range f.toLinearMap).mkQ (f w) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [map_sub, map_smul, h3, smul_zero, sub_zero] at h2
  exact h2

end GlobalTheory.CompanionTheory.BZSeg.TwoSeg

namespace GlobalTheory.CompanionTheory.BZSeg

end GlobalTheory.CompanionTheory.BZSeg
