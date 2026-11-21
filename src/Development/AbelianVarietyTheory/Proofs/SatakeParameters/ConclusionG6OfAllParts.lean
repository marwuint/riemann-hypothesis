import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois

noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

theorem charpoly_smul [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem twGL_val {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (W : Submodule K (Fin a → K)) :
    IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
    rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem ss_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := fun W hW => by
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL ρ χ W').2 hW', hc⟩

end Alg

theorem ms_one {s : Multiset ℕ} (h : s.sum = 1) (h1 : ∀ a ∈ s, 1 ≤ a) : s = {1} := by
  have hne : s ≠ 0 := by rintro rfl; simp at h
  have hc := Multiset.card_nsmul_le_sum h1
  have hp := Multiset.card_pos.2 hne
  rw [smul_eq_mul, mul_one, h] at hc
  have hc1 : Multiset.card s = 1 := by omega
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc1
  simp only [Multiset.sum_singleton] at h
  rw [h]

theorem sum_split {M : Type} [AddCommMonoid M] {n m : ℕ} (h : n = m + 1) (f : Fin n → M) :
    ∑ k, f k = ∑ k : Fin m, f (Fin.cast h.symm k.castSucc) + f (Fin.cast h.symm (Fin.last m)) := by
  subst h
  simp [Fin.sum_univ_castSucc]

theorem prod_flatMap' {α M : Type} [CommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_flat {M : Type} [CommMonoid M] (n : ℕ) (d : Fin n → ℕ) (f : Fin n → ℕ → M) :
    (((List.finRange n).map fun k => ((List.range (d k)).map (f k)).prod)).prod =
      ∏ k, ∏ a ∈ Finset.range (d k), f k a := by
  rw [Fin.prod_univ_def]
  congr 1

variable (D : D7) (i : D.nd.Loc)

def eU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)

def cU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (D.nd.chi i 1)

theorem eU_pow (g : G D.host.E D.nd.Om) (a : ℕ) :
    ((((eU D i)⁻¹ ^ a) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) = (epsQ D i g)⁻¹ ^ a := by
  rw [MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rfl

def twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) :
    List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))) :=
  (List.finRange Pa.length).flatMap fun k =>
    (List.range (Pa.get k).d).map fun a => ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩

theorem mem_twList {Pa : List (Part D.naut.CG)}
    {R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))}
    {p : Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))} (hp : p ∈ twList D i Pa R) :
    ∃ k : Fin Pa.length, ∃ a < (Pa.get k).d,
      p = ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
  exact ⟨k, a, List.mem_range.1 ha, rfl⟩

theorem twList_cp (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (g : G D.host.E D.nd.Om) :
    ((twList D i Pa R).map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) (Qbar (D.nd.l i))).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
          ((epsQ D i g)⁻¹ ^ a) := by
  rw [twList, List.map_flatMap, prod_flatMap']
  simp only [List.map_map, Function.comp_def]
  rw [prod_flat]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun a _ => ?_
  rw [twGL_val, charpoly_smul _ (Units.ne_zero _), eU_pow]

theorem mapRep_val {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).map f := rfl

theorem eig_map (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)) (v : Fin D.R.nV → Kf D.nd i)
    (hv0 : v ≠ 0) (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    ∃ w : Fin D.R.nV → Qbar (D.nd.l i), w ≠ 0 ∧ ∀ g,
      ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).mulVec w =
        ((cU D i g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) • w := by
  refine ⟨fun j => D.naut.iotaQ i (v j), fun h => hv0 (funext fun j => ?_), fun g => funext fun j => ?_⟩
  · have := congrFun h j
    exact (D.naut.iotaQ i).injective (by simpa using this)
  · have e1 := congrArg (D.naut.iotaQ i) (congrFun (hv g) j)
    rw [RingHom.map_mulVec, mapRep_val] at e1
    rw [mapRep_val]
    refine e1.trans ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.EigenPoint
