import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PlusPolynomialInclusion

noncomputable section

open Polynomial TensorProduct Matrix Formalism.UG

namespace GlobalTheory.ClassParam

section Cyclic

theorem charpoly_dvd_of_aeval {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) (q : K[X]) (hq : aeval g q = 0) : g.charpoly ∣ q := by
  classical
  by_cases h0 : q = 0
  · simp [h0]
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f]
  have hq0 : q.map f ≠ 0 := Polynomial.map_ne_zero h0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots (Polynomial.map_ne_zero g.charpoly_monic.ne_zero) ?_
  rw [Multiset.le_iff_subset (nodup_roots hs.map)]
  intro μ hμ
  rw [mem_roots hq0]
  have h1 : μ ∈ spectrum Ω (g.map f) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
    exact isRoot_of_mem_roots hμ
  have h2 := spectrum.subset_polynomial_aeval (g.map f) (q.map f) ⟨μ, h1, rfl⟩
  have h3 : aeval (g.map f) (q.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := Fin r) (Algebra.ofId K Ω)) hq
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  rw [h3] at h2
  by_contra hne
  exact (spectrum.mem_iff.1 h2) (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin r) (Fin r) Ω)))

def krylov {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ((g ^ (j : ℕ)) *ᵥ v) i

theorem krylov_map {A B : Type} [CommRing A] [CommRing B] {r : ℕ} (f : A →+* B)
    (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    (krylov g v).map f = krylov (g.map f) (f ∘ v) := by
  ext i j
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem exists_cyclic_field {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) : ∃ v, (krylov g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  refine ⟨(Module.AEval'.of (Matrix.toLin' g)).symm x, fun h => ?_⟩
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (w j)
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [← hw]
    ext i
    simp [q, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  have hd := charpoly_dvd_of_aeval g hs q hq
  have hdeg : q.degree < g.charpoly.degree := by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => lt_of_le_of_lt (degree_monomial_le _ _) ?_
    exact_mod_cast j.2
  have hq0 := eq_zero_of_dvd_of_degree_lt hd hdeg
  apply hw0
  ext j
  have := congrArg (fun p => p.coeff j) hq0
  simpa [q, finset_sum_coeff, coeff_monomial, Fin.val_inj] using this

theorem exists_cyclic {A : Type} [CommRing A] [IsArtinianRing A] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

end Cyclic

section Core

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

structure HidaSetting (σ : A →+* A) (τ : B →+* B) (α : B) (b : Module.Basis (Fin r) A B) : Prop where
  hσ : ∀ a, σ (σ a) = a
  hτ : ∀ y, τ (τ y) = y
  comp : ∀ a, τ (algebraMap A B a) = algebraMap A B (σ a)
  hα : α * τ α = 1
  pow : ∀ i, b i = α ^ (i : ℕ)
  perf : IsUnit (Algebra.traceMatrix A b).det

def tf (A : Type) [CommRing A] [Algebra A B] (τ : B →+* B) (x y y' : B) : A :=
  Algebra.trace A B (x * y * τ y')

def Iso (σ : A →+* A) (τ : B →+* B) (J : Matrix (Fin r) (Fin r) A) (x : B)
    (φ : B ≃ₗ[A] (Fin r → A)) : Prop :=
  ∀ y y', hform σ J (φ y') (φ y) = tf A τ x y y'

def Intw (α : B) (g : Matrix (Fin r) (Fin r) A) (φ : B ≃ₗ[A] (Fin r → A)) : Prop :=
  ∀ u, g *ᵥ u = φ (α * φ.symm u)

variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

def HidaSetting.pb (S : HidaSetting σ τ α b) : PowerBasis A B := ⟨α, r, b, S.pow⟩

theorem HidaSetting.traceForm_bij (S : HidaSetting σ τ α b) :
    Function.Bijective (Algebra.traceForm A B) := by
  have h : IsUnit (LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)).det := by
    have : LinearMap.toMatrix b b.dualBasis (Algebra.traceForm A B)
        = (Algebra.traceMatrix A b)ᵀ := by
      ext i j
      simp [LinearMap.toMatrix_apply, Algebra.traceMatrix_apply]
    rw [this, Matrix.det_transpose]; exact S.perf
  have := (LinearEquiv.ofIsUnitDet h).bijective
  rwa [← LinearEquiv.coe_coe, LinearEquiv.coe_ofIsUnitDet] at this

theorem HidaSetting.exists_trace (S : HidaSetting σ τ α b) (f : B →ₗ[A] A) :
    ∃ x, ∀ y, f y = Algebra.trace A B (x * y) := by
  obtain ⟨x, hx⟩ := S.traceForm_bij.2 f
  exact ⟨x, fun y => by rw [← hx]; rfl⟩

def mulUnit (A : Type) [CommRing A] [Algebra A B] (z : Bˣ) : B ≃ₗ[A] B :=
  LinearEquiv.ofLinear (LinearMap.mulLeft A (z : B)) (LinearMap.mulLeft A ((z⁻¹ : Bˣ) : B))
    (by ext; simp) (by ext; simp)

theorem mulUnit_apply (z : Bˣ) (y : B) : mulUnit A z y = z * y := rfl

theorem mulUnit_symm_apply (z : Bˣ) (y : B) : (mulUnit A z).symm y = (z⁻¹ : Bˣ) * y := rfl

theorem Iso.mul {x : B} {φ : B ≃ₗ[A] (Fin r → A)} (h : Iso σ τ J x φ) (z : Bˣ) :
    Iso σ τ J (x * (z * τ z)) (mulUnit A z ≪≫ₗ φ) := by
  intro y y'
  simp only [LinearEquiv.trans_apply, mulUnit_apply]
  rw [h]
  unfold tf
  congr 1
  rw [map_mul]; ring

theorem Intw.mul {g : Matrix (Fin r) (Fin r) A} {φ : B ≃ₗ[A] (Fin r → A)} (h : Intw α g φ)
    (z : Bˣ) : Intw α g (mulUnit A z ≪≫ₗ φ) := by
  intro u
  rw [h]
  simp only [LinearEquiv.trans_apply, mulUnit_apply, LinearEquiv.symm_trans_apply,
    mulUnit_symm_apply]
  congr 1
  rw [mul_left_comm α, Units.mul_inv_cancel_left]

def gram (τ : B →+* B) (x : B) (e : Module.Basis (Fin r) A B) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun i j => tf A τ x (e i) (e j)

end Core

section Concrete

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

attribute [local instance] algLk

variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

theorem algebraMap_tmul (e : E) (t : k) :
    algebraMap (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) (e ⊗ₜ t) = AdjoinRoot.of P e ⊗ₜ t := rfl

end Concrete

end GlobalTheory.ClassParam
