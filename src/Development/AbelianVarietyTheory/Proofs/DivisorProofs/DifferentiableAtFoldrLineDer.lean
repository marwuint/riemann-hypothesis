import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThK.RealLineGrowthDerivative
open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

variable {J : Matrix (Fin n) (Fin n) E}

theorem prod_ofFn_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_partial_last {m : ℕ} {H : (Fin (m + 1) → ℝ) → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun s : Fin m → ℝ => deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 := by
  let v : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  let L : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i
  have hL : ∀ s t, Fin.snoc (α := fun _ => ℝ) s t = L s + t • v := fun s t => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, v]
    · simp [L, v, Fin.castSucc_ne_last]
  have hd : ∀ s, deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 = fderiv ℝ H (L s) v := fun s => by
    simp only [hL]
    have h1 : HasDerivAt (fun t : ℝ => L s + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (L s)
    have h2 := (hH.differentiable (by simp)).differentiableAt (x := L s + (0 : ℝ) • v)
    rw [zero_smul, add_zero] at h2
    have h3 := h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact h3.deriv
  simp only [hd]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp L.contDiff).clm_apply contDiff_const

theorem contDiff_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ (m : ℕ) (δ : Fin m → ℝ → GAd σ J),
      (∀ i, IsRealLine σ J (δ i)) → ∀ x,
      ContDiff ℝ ∞ fun s : Fin m → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => δ i (s i)).prod) := by
  intro l
  induction l with
  | nil => intro _ m δ hδ x; exact hf m δ hδ x
  | cons γ l ih =>
    intro hl m δ hδ x
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    have hH := ih hl' (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ)
      (fun i => Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i) x
    have := contDiff_partial_last hH
    simp only [prod_ofFn_snoc, ← mul_assoc] at this
    simpa only [List.foldr_cons, lineDer] using this

theorem differentiableAt_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (x : GAd σ J) :
    DifferentiableAt ℝ (fun t => l.foldr lineDer f (x * γ t)) 0 := by
  have h := (contDiff_foldr_lineDer hf l hl 1 (fun _ => γ) (fun _ => hγ) x).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
  have h' := (h.differentiable (by simp)) 0
  have e : (fun t => l.foldr lineDer f (x * γ t)) = ((fun s : Fin 1 → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => (fun _ => γ) i (s i)).prod)) ∘ fun t : ℝ => fun _ : Fin 1 => t) := by
    funext t; simp
  rw [e]; exact h'

end GlobalTheory.ThK.RealLineGrowthDerivative

end
