import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffProdOneSubCMulX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup

noncomputable section

namespace GlobalTheory.Triple

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)

theorem eq_one_of_isOfFinOrder_of_charpoly {K : Type} [Field K] [CharZero K] {n : ℕ} {A : GL (Fin n) K}
    (hA : IsOfFinOrder A) (hc : (A : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : A = 1 := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hA
  have h1 : minpoly K (A : Matrix (Fin n) (Fin n) K) ∣ X ^ m - C 1 := minpoly.dvd _ _ (by
    rw [map_sub, map_pow, aeval_X, map_one, map_one, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self])
  have h2 := ((separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree.squarefree_of_dvd
    h1).isRadical n _ (hc ▸ Matrix.minpoly_dvd_charpoly _)
  have h3 := aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K _)
  rw [map_sub, aeval_X, map_one, sub_eq_zero] at h3
  exact Units.ext h3

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem eval_charpolyRev {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (z : R) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem charpolyRev_of_inv {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) {m : Multiset ℂ}
    (hB : B.charpoly = (m.map fun a => X - C a).prod) : A.charpolyRev = (m.map fun a => 1 - C a⁻¹ * X).prod := by
  have e : ∀ z : ℂ, (Matrix.scalar (Fin n) z - B).det = (m.map fun a => z - a).prod := fun z => by
    rw [← Matrix.eval_charpoly, hB, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (Matrix.scalar (Fin n) 0 - B).det ≠ 0 := by
    rw [map_zero, zero_sub, Matrix.det_neg]
    exact mul_ne_zero (by simp) (Matrix.isUnit_det_of_left_inverse h).ne_zero
  apply Polynomial.funext
  intro z
  refine mul_right_cancel₀ h0 ?_
  have e1 : (1 - z • A) * (Matrix.scalar (Fin n) 0 - B) = Matrix.scalar (Fin n) z - B := by
    rw [map_zero, zero_sub, mul_neg, sub_mul, one_mul, smul_mul_assoc, h, neg_sub, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [eval_charpolyRev, ← Matrix.det_mul, e1, e, e, eval_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  have ha0 : a ≠ 0 := fun h1 => h0 (by
    rw [e]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by rw [h1, sub_self]⟩))
  simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have h : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly, Nat.lt_succ_iff]
    exact (reverse_natDegree_le _).trans (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  have := eval_eq_sum_range' h 1
  simp only [one_pow, mul_one, eval_charpolyRev, one_smul] at this
  exact this.symm

variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}

theorem cyclotomicEps_eq_one_on_inertia {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : eps0 X i σ = 1 := by
  have h1 : cycZ D.host.E D.nd.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  rw [eps0, MonoidHom.comp_apply, h1, map_one]

theorem cyclotomicEps_frobenius_eq_norm {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) = (normV v : ℕ) := by
  show algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E D.nd.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = _
  rw [cycZ_of_isFrob hv hA hσ, map_natCast]

def twistW (s : X.Sig i) : GalE D →* (X.O0 i)ˣ := eps0 X i ^ D.R.t * (chiS i s)⁻¹

def matW (s : X.Sig i) (g : GalE D) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  ((twistW s g : (X.O0 i)ˣ) : X.O0 i) • ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))

theorem matW_eq (s : X.Sig i) (g : GalE D) :
    matW s g = (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g := by
  rw [matW, Tmat, smul_smul, twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val]

theorem matW_mul_inv (s : X.Sig i) (g : GalE D) : matW s g * matW s g⁻¹ = 1 := by
  rw [matW, matW, smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
    map_one, Units.val_one, Units.val_one, one_smul]

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}

theorem notMem_of_mem_pD {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    X.pD_eq i ▸ Finset.mem_coe.2 hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at h with e
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime hl (e ▸ D.host.pde_ne.symm) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h⟩
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime hl (Ne.symm e) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h⟩

theorem matW_of_mem_Ine (hu : UnrRho i s) {v : PlE D.host} (hl : v ∉ placesOver D.host.E (X.l i))
    (hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {g : GalE D} (hI : g ∈ Ine (F := D.host.E) A) :
    matW s g = (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  rw [matW_eq, Tmat, cyclotomicEps_eq_one_on_inertia hl hA hI, hu v hl hg A hA g hI, Units.val_one, Units.val_one, one_pow, one_smul]

variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}

end GlobalTheory.Triple

end
