import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseReal
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseArch
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataRestrictionUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalIsomorphismScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}

theorem polMatch_iso {R R₃ : RealMaps F a a'} {Rf Rf₃ : FinMaps F a a'} {ψ₀ : R.Pi ≃ₗ[ℂ] R₃.Pi} {l₀ : ℂ}
    {ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v} {l : Pl F → ℂ} (hl1 : ∀ v ∉ X.T, l v = 1)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ₀ (R.p f)) (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l₀ • ψ₀ (R.p' f))
    (hRf : ∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ v (Rf.p v φ))
    (hRf' : ∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l v • ψ v (Rf.p' v φ))
    {Φ Φ'} (hM : PolMatch B G X R Rf Φ Φ') : PolMatch B G X R₃ Rf₃ ((l₀ * ∏ v ∈ X.T, l v) • Φ) Φ' := by
  set Λ : ℂ := l₀ * ∏ v ∈ X.T, l v with hΛdef
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', heq⟩ := hM
  have hΛT : l₀ * ∏ v ∈ T, l v = Λ := by
    rw [hΛdef, Finset.prod_subset hT (fun v _ hv => hl1 v hv)]
  refine ⟨T, hT, m, m', fun i => Λ • f i, φ, f', φ', fun i => ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩, hf', ?_, hΦ', ?_⟩
  · rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  · let L := TensorProduct.map ψ₀.toLinearMap (PiTensorProduct.map fun v : T => (ψ v).toLinearMap)
    have h1 := congrArg L heq
    simp only [map_sum, L, TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearEquiv.coe_coe] at h1
    have lhs : ∀ i, R₃.p (Λ • f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p v (φ i v)) =
        Λ • (ψ₀ (R.p (f i)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p v (φ i v))) := by
      intro i
      have e : (fun v : T => Rf₃.p v (φ i v)) = fun v : T => ψ v (Rf.p v (φ i v)) :=
        funext fun v => hRf v _ ((hf i).2.1 v)
      rw [e, map_smul, hR _ (hf i).1, ← TensorProduct.smul_tmul']
    have rhs : ∀ j, R₃.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p' v (φ' j v)) =
        Λ • (ψ₀ (R.p' (f' j)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p' v (φ' j v))) := by
      intro j
      have e : (fun v : T => Rf₃.p' v (φ' j v)) = fun v : T => l v • ψ v (Rf.p' v (φ' j v)) :=
        funext fun v => hRf' v _ ((hf' j).2.1 v)
      rw [e, MultilinearMap.map_smul_univ, hR' _ (hf' j).1, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
        Finset.prod_coe_sort, hΛT]
    simp only [lhs, rhs, ← Finset.smul_sum, h1]

variable (B G V V' Z) in

def kapId : (AE F E)ˣ :=
  ∏ v : B.P, locIdele F (splitPrime (B.τ v))
    (Units.map (complMap (splitPrime_under (B.τ v))).toMonoidHom (kap G V V' Z v.1))

theorem chr_kapId (χ : Chr F E) :
    (χ (kapId B G V V' Z) : ℂ) = ∏ v : B.P, (chrW χ (B.τ v) (kap G V V' Z v.1) : ℂ) := by
  rw [kapId, map_prod]
  exact map_prod Circle.coeHom _ _

variable {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem acts_pureA {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : T (pureA F f g) = pureA F f₁ g := by
  refine h (fun x => g fun i => (x i).2) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero]

theorem pureA_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    pureA F (⇑(c • f)) g = c • pureA F f g := by
  funext x
  simp only [pureA, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem acts_congr {κ : Type} [Fintype κ] {T T₁ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} (e : ∀ Φ ∈ schA F κ, T Φ = T₁ Φ)
    {f f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ} (h : Acts (evI F) T f f₁) : Acts (evI F) T₁ f f₁ :=
  fun r hr => (e _ hr.2).symm.trans (h r hr)

end GlobalTheory.ReBase

end
