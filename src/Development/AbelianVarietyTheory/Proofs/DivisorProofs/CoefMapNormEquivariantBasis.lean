import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef

noncomputable section

namespace GlobalTheory.AdTh.CoefExt

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (φ : K →+* K')
  {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]

theorem map_actP (B : I → GL (Fin n) K) (F : Pol K I n) :
    MvPolynomial.map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) := by
  have h1 : (MvPolynomial.map φ).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc φ (B τ))).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map φ (trAct B F) = trAct (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) :=
    congrArg (fun ψ : Pol K I n →+* Pol K' I n => ψ F) h1
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

def up (v : VV K lam) : VV K' lam := ⟨MvPolynomial.map φ (v : Pol K I n), GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ v.2⟩

theorem up_sum (a : VVIdx lam → K) (v : VVIdx lam → VV K lam) :
    up φ lam (∑ j, a j • v j) = ∑ j, φ (a j) • up φ lam (v j) := by
  apply Subtype.ext
  simp only [up, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eq_C_mul, map_mul, map_C]

theorem exists_coord (v : VV K' lam) : ∃ a : VVIdx lam → K', v = ∑ j, a j • up φ lam (bVV K lam j) := by
  have hv : v ∈ Submodule.span K' (Set.range (bVV K' lam)) := by rw [(bVV K' lam).span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam j
    refine ⟨fun k => φ ((bVV K lam).repr ⟨F, hF⟩ k), ?_⟩
    rw [← up_sum, (bVV K lam).sum_repr]
    exact Subtype.ext ((bVV_coe _ _ _).trans hj)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [← Finset.sum_add_distrib, add_smul]⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun j => c * a j, by simp [Finset.smul_sum, mul_smul]⟩

theorem up_rhoVr {E : Type} [Field E] [NumberField E] [NumberField K] [NumberField K'] (emb : I → E →+* K)
    (g : GL (Fin n) E) (v : VV K lam) :
    up φ lam (rhoVr emb lam g v) = rhoVr (fun τ => φ.comp (emb τ)) lam g (up φ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map φ (actP lam (invTrK (embGL emb g)) (v : Pol K I n)) =
    actP lam (invTrK (embGL (fun τ => φ.comp (emb τ)) g)) (MvPolynomial.map φ (v : Pol K I n))
  rw [map_actP]
  rfl

variable {φ lam} {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

theorem equivariant (hE : ∀ v, c' (up φ lam v) = c₀ v) (T : W →ₗ[ℂ] W) (S : VV K lam →ₗ[K] VV K lam)
    (S' : VV K' lam →ₗ[K'] VV K' lam) (hS : ∀ v, up φ lam (S v) = S' (up φ lam v)) (hT : ∀ v, c₀ (S v) = T (c₀ v))
    (v : VV K' lam) : c' (S' v) = T (c' v) := by
  obtain ⟨a, rfl⟩ := exists_coord φ lam v
  simp only [map_sum, map_smul, map_smulₛₗ, ← hS, hE, hT, RingHom.id_apply]

theorem span_top (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hs : Submodule.span ℂ (Set.range fun j => c₀ (bVV K lam j)) = ⊤) : Submodule.span ℂ (Set.range c') = ⊤ := by
  refine top_le_iff.1 (hs ▸ Submodule.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨_, hE _⟩

theorem linearIndependent (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) {m : ℕ} (b : Fin m → VV K' lam) (hb : LinearIndependent K' b) :
    LinearIndependent ℂ fun j => c' (b j) := by
  classical
  letI : Algebra K' ℂ := σ'.toAlgebra
  choose a ha using fun j => exists_coord φ lam (b j)
  have h1 : LinearIndependent K' a := by
    refine LinearIndependent.of_comp (Fintype.linearCombination K' fun k => up φ lam (bVV K lam k)) ?_
    convert hb using 1
    funext j
    rw [ha j]
    simp [Fintype.linearCombination_apply]
  have h2 : LinearIndependent ℂ fun j => algebraMap K' ℂ ∘ a j := linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k))
    (LinearMap.ker_eq_bot'.2 fun g hg => funext (Fintype.linearIndependent_iff.1 hli g (by simpa [Fintype.linearCombination_apply] using hg)))
  have e : (fun j => c' (b j)) = ⇑(Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k)) ∘ fun j => algebraMap K' ℂ ∘ a j := by
    funext j
    rw [ha j]
    simp only [map_sum, map_smulₛₗ, hE, Function.comp_apply, Fintype.linearCombination_apply]
    rfl
  rw [e]
  exact h3

theorem pairVr_extremal {E : Type} [Field E] [NumberField E] [NumberField K] [StarRing K] (emb : I → E →+* K)
    (v : VV K lam) (hv : (v : Pol K I n) = ten fun τ => extremal K n (lam τ)) : pairVr emb lam 1 v v = 1 := by
  have hG : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have h := pairingExtremal_holds K I n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [polyAction_one₂] at h
  rw [pairVr, pairK_apply, hG, hv, h]

end GlobalTheory.AdTh.CoefExt

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem inner_of_coefTie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : Formalism.L2.DIV.CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : Formalism.L2.DIV.VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (v w : Formalism.L2.DIV.VV D.what₂.LL lam) :
    inner ℂ (c0 v) (c0 w) = D.what₂.embLL (pair v w) := by
  obtain ⟨e, -, he, hp, -⟩ := h
  have hi := P.coef_pair (e.symm v) (e.symm w)
  rwa [he, he, ← hp, e.apply_symm_apply, e.apply_symm_apply] at hi

end GlobalTheory.AdTh

end
