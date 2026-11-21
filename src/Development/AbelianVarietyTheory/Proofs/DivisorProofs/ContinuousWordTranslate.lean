import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothCyclic

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.LowTypeRestriction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Conj
variable {n : ℕ}

theorem conj_lie {J G A B X : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (h : Bᴴ * J * B = G)
    (hX : Xᴴ * J + J * X = 0) : (A * X * B)ᴴ * G + G * (A * X * B) = 0 := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  calc (A * X * B)ᴴ * G + G * (A * X * B)
      = Bᴴ * (Xᴴ * (Aᴴ * Bᴴ) * J + J * (B * A) * X) * B := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_of_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (A * X * B)) = A * NormedSpace.exp (t • X) * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  rw [hB, ← Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ hAB)]
  simp

theorem list_prod_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun a => A * a * B).prod = A * l.prod * B := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  induction l with
  | nil => simp [hAB]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc A * a * B * (A * l.prod * B) = A * a * (B * A) * l.prod * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem expProd_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * B))).prod
      = A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * B := by
  rw [← list_prod_conj hAB, List.map_ofFn]
  simp only [exp_conj_of_mul hAB, Function.comp_def]

end Conj

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def lieJ (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exp_memJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε :=
  exp_mem (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hX t

theorem expProd_memJ {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieJ ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε :=
  list_prod_mem (G := Formalism.REAL.Jm ε) _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_memJ (hX i) _

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε)
    (v : H) : σ a (σ b v) = σ (a * b) v := by
  rw [hσ.1.2 _ ha _ hb]; rfl

def smSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lieJ ε : Set _) σ w}
  add_mem' := fun ha hb k Xs hX => by simpa only [map_add] using (ha k Xs hX).add (hb k Xs hX)
  zero_mem' := fun k Xs _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c w hw k Xs hX => by simpa only [map_smul] using (hw k Xs hX).const_smul c

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h := (hw 1 (fun _ => X) fun _ => hX).comp (contDiff_pi.2 fun _ : Fin 1 => (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)))
  have h2 : ContDiff ℝ ∞ fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h
  exact (h2.differentiable (by simp) 0).hasDerivAt

theorem dRep_mem (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieJ ε) : dRep σ X w ∈ smSub ε σ := by
  intro k Xs hXs
  have h := hw (k + 1) (Fin.snoc Xs X) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  have hs : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp (contDiff_fst (F := ℝ))
  have h2 : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ =>
      σ ((List.ofFn fun i => NormedSpace.exp (z.1 i • Xs i)).prod) (σ (NormedSpace.exp (z.2 • X)) w) := by
    convert h.comp hs using 2 with z
    rw [rep_mul hσ (expProd_memJ hXs _) (exp_memJ hX _)]
    simp only [Function.comp_def, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, List.prod_append,
      List.prod_singleton]
  have h3 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (f := fun (t : Fin k → ℝ) (s : ℝ) =>
      σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ (NormedSpace.exp (s • X)) w))
      (g := fun _ => 0) h2 contDiff_const (by simp)
  convert h3.clm_apply (contDiff_const (c := (1 : ℝ))) using 2 with t
  exact (((σ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_dRep hw hX)).deriv.symm

variable {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}

section Transport
variable {P G : Matrix (Fin n) (Fin n) ℂ}

theorem smoothVec_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (w : H) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w ↔ w ∈ smSub ε σ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  constructor
  · intro hw k Xs hX
    have := hw k (fun i => P⁻¹ * Xs i * P) fun i => conj_lie h2 h (hX i)
    convert this using 2 with t
    rw [expProd_conj h2]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro hw k Xs hX
    simpa only [expProd_conj h1] using hw k (fun i => P * Xs i * P⁻¹) fun i => conj_lie h1 h' (hX i)

theorem sobCont_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) ℓ) : Sobolev₂ (lieJ ε : Set _) σ ℓ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  obtain ⟨S, C, hS, hb⟩ := hℓ
  have e : dRep (fun g => σ (P * g * P⁻¹)) = fun X w => dRep σ (P * X * P⁻¹) w := by
    funext X w
    simp only [dRep, exp_conj_of_mul h1]
  refine ⟨S.map fun l => l.map fun X => P * X * P⁻¹, C, fun l hl X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 h' (hS l' hl' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using
      hb w ((smoothVec_transport hP h w).2 hw)

end Transport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ = smSub (M.ε τ) (M.σ τ) := by
  rw [← Submodule.span_eq (smSub (M.ε τ) (M.σ τ))]
  exact congrArg (Submodule.span ℂ) (Set.ext fun w => smoothVec_transport (M.fr_unit τ) (M.fr_gram τ) w)

end GlobalTheory.SmoothCyclic
