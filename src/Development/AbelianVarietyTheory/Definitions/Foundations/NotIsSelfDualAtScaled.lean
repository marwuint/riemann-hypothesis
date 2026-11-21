import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.AdelicU.Model

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

variable (E) in

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

omit [NumberField E] in
theorem tmul_mul_inv {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    ((a : Fv F v) ⊗ₜ[F] (1 : E)) * (((a⁻¹ : (Fv F v)ˣ) : Fv F v) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one]; rfl

omit [NumberField E] in
theorem inv_mul_tmul {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    (((a⁻¹ : (Fv F v)ˣ) : Fv F v) ⊗ₜ[F] (1 : E)) * ((a : Fv F v) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [mul_comm, tmul_mul_inv]

variable (E) in

def torMat {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) : Matrix (Fin 2) (Fin 2) (Fv F v ⊗[F] E) :=
  !![(a : Fv F v) ⊗ₜ[F] (1 : E), 0; 0, ((a⁻¹ : (Fv F v)ˣ) : Fv F v) ⊗ₜ[F] (1 : E)]

omit [NumberField E] in
theorem torMat_mul_inv {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) : torMat E a * torMat E a⁻¹ = 1 := by
  have h1 := tmul_mul_inv (E := E) a
  have h2 := inv_mul_tmul (E := E) a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [torMat, Matrix.mul_apply, Fin.sum_univ_two, inv_inv] <;> simp [-Units.val_inv_eq_inv_val, h1, h2, Algebra.TensorProduct.one_def]

def tor {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) : GLoc σ (hyp E) v :=
  ⟨⟨torMat E a, torMat E a⁻¹, torMat_mul_inv a, by simpa using torMat_mul_inv (E := E) a⁻¹⟩, by
    change cT _ (torMat E a) * JR _ (hyp E) * torMat E a = JR _ (hyp E)
    have h1 := tmul_mul_inv (E := E) a
    have h2 := inv_mul_tmul (E := E) a
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-Units.val_inv_eq_inv_val, torMat, cT, JR, hyp, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Matrix.mul_apply, Fin.sum_univ_two, h1, h2,
        Algebra.TensorProduct.one_def]⟩

section Supp

omit [NumberField E] in
theorem map_map_tens {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

omit [NumberField E] in
theorem adTens_eq_one {y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = 1) (h2 : ∀ v, compFin F E v y = 1) : y = 1 := by
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.AutFunCompare.infTens_ext fun w => (map_map_tens _ _ y).trans ((h1 w).trans (map_one _).symm))
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
        (map_map_tens _ _ y).trans ((h2 v).trans (map_one _).symm))
  exact congrFun (congrFun this 0) 0

theorem idem_supp_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e1 : evFin F v ε = 1) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) (g : GAd σ J) :
    (∀ i j, algebraMap (AF F) (AF F ⊗[F] E) ε * ((matHom _ σ J g).1 - 1) i j = ((matHom _ σ J g).1 - 1) i j) ↔
      g ∈ (emb σ J v).range := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1 := by
    change evFin F v ε ⊗ₜ[F] (1 : E) = 1
    rw [e1]; rfl
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A),
      m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := fun φ m => by
    rw [← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  have pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  rw [range_emb, mem_atPts, mem_finPts_iff_forall]
  simp only [pf, pa, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩
  · rintro ⟨h1, h2⟩ i j
    rw [← sub_eq_zero, ← add_eq_right (b := 1)]
    refine adTens_eq_one (fun w => ?_) fun u => ?_
    · rw [map_add, map_sub, map_mul, h1, map_one]; simp
    · rw [map_add, map_sub, map_mul, map_one]
      by_cases hu : u = v
      · subst hu; rw [c1]; simp
      · rw [h2 u hu]; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem suppF_iff {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) (g : GA D V) :
    Formalism.IndefR.Mult.SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  exact idem_supp_iff _ _ v _ (fun _ => rfl) h1 h2 g

theorem emb_mem_KsphC_iff {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : GLoc D.sp.cm.sig V.gram v) :
    emb D.sp.cm.sig V.gram v x ∈ KsphC V ∅ ↔ x ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := by
  rw [KsphC_eq]
  exact ⟨fun h => by simpa using (mem_levelOff.1 h).2.2 v (by simp), emb_mem_levelOff (by simp)⟩

end Supp

end GlobalTheory.AdelicU.Model
