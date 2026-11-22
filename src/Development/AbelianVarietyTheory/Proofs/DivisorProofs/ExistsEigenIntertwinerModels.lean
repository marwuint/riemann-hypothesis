import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestriction

noncomputable section

namespace GlobalTheory.ThK.ModelPol

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (finPr φ) := rfl

theorem finPr_mem {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : finPr φ ∈ SB _ :=
  ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩

theorem exists_finPr_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : ∃ y, finPr φ y ≠ 0 := by
  have key : ∀ v : Pl F, ∃ p : κ → Fv F v, φ v p ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  refine ⟨fun i => ⟨fun v => p v i, ?_⟩, ?_⟩
  · filter_upwards [hstd] with v hv using hp' v hv i
  · exact finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => hp v

def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain MeasureTheory Filter Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.ThK.ModelPol.pureA_pt {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    _root_.GlobalTheory.WeilM.pureA F f g (_root_.GlobalTheory.ThK.ModelPol.pt x y) = f x * g y := by
  unfold _root_.GlobalTheory.WeilM.pureA _root_.GlobalTheory.ThK.ModelPol.pt
  simp

open scoped Classical in

theorem proj_adm {κ : Type} [Fintype κ] (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) :
    (LinearMap.proj (pt x y) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g y • (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  rw [LinearMap.proj_apply, pureA_pt]
  simp [mul_comm]

section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem pol_map (M M' : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D D' : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (hD' : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M'.heisLine ψ u) f f₁ ↔ f₁ = D' u f)
    (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) (hb : Function.Bijective ei)
    (hi : ∀ u, At (evI F) u → ∀ f, ei (D u f) = D' u (ei f)) : (M.Pol ψ τ).map ei = M'.Pol ψ τ := by
  have hG : ∀ f, M.IsGauss ψ τ f ↔ M'.IsGauss ψ τ (ei f) := fun f => by
    refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun h g g' hg hg' => ?_, fun h g g' hg hg' => ?_⟩
    · rw [(hD' u hu _ _).1 hg, (hD' u' hu' _ _).1 hg', ← hi u hu, ← hi u' hu',
        h _ _ ((hD u hu _ _).2 rfl) ((hD u' hu' _ _).2 rfl), map_smul]
    · apply hb.1
      rw [(hD u hu _ _).1 hg, (hD u' hu' _ _).1 hg', map_smul, hi u hu, hi u' hu']
      exact h _ _ ((hD' u hu _ _).2 rfl) ((hD' u' hu' _ _).2 rfl)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine sInf_le ⟨fun f hf => ?_, fun u hu f hf f₁ h₁ => ?_⟩
    · exact Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).1 hf)
    · refine Submodule.mem_sInf.2 fun N hN => hN.2 u hu (ei f) (Submodule.mem_sInf.1 hf N hN) _ ?_
      rw [hD' u hu, (hD u hu _ _).1 h₁, hi u hu]
  · refine sInf_le ⟨fun g hg => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ := hb.2 g
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).2 hg))
    · rintro u hu _ ⟨f, hf, rfl⟩ g₁ h₁
      rw [(hD' u hu _ _).1 h₁, ← hi u hu]
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN =>
        hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ ((hD u hu _ _).2 rfl))

end

theorem exists_chr (B : Base F E) (hB : B.IsGood σ) (m : ℕ) :
    ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m := by
  obtain ⟨χ, hχ, hr⟩ := _root_.GlobalTheory.CMHeckeEta.exists_hecke_resEtaPow_one F E σ B hB
  refine ⟨χ ^ m, ⟨hχ.1.pow m, fun x => ?_⟩, fun a => ?_⟩
  · rw [MonoidHom.pow_apply, hχ.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hr a]
    split_ifs <;> simp

end GlobalTheory.ThK.ModelPol

end
