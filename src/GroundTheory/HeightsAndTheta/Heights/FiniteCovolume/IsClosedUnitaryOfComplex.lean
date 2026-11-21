import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume

open NumberField Matrix MeasureTheory
open scoped ENNReal ComplexOrder TensorProduct

def conjE (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toRingEquiv.toRingHom

theorem conjE_apply (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    conjE E x = IsCMField.complexConj E x := rfl

def unitaryOf {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : R →+* R)
    (J : Matrix ι ι R) : Subgroup (GL ι R) where
  carrier := {g | (g : Matrix ι ι R)ᵀ * J * (g : Matrix ι ι R).map σ = J}
  one_mem' := by
    simp [Matrix.map_one _ (map_zero σ) (map_one σ)]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix ι ι R)ᵀ * ((a : Matrix ι ι R)ᵀ * J * (a : Matrix ι ι R).map σ) *
          (b : Matrix ι ι R).map σ := by simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * (a : Matrix ι ι R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    have h2 : (a : Matrix ι ι R).map σ * ((a⁻¹ : GL ι R) : Matrix ι ι R).map σ = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc _ = ((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ *
          ((a : Matrix ι ι R)ᵀ * J * (a : Matrix ι ι R).map σ) *
          ((a⁻¹ : GL ι R) : Matrix ι ι R).map σ := by rw [ha]
      _ = (((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * (a : Matrix ι ι R)ᵀ) * J *
          ((a : Matrix ι ι R).map σ * ((a⁻¹ : GL ι R) : Matrix ι ι R).map σ) := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

structure HermSpace (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) where

  J : Matrix (Fin N) (Fin N) E
  herm : Jᵀ = J.map (conjE E)
  nondeg : IsUnit J.det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def HermSpace.h (V : HermSpace E N) (x y : Fin N → E) : E :=
  ReciprocityTheory.ChartRestriction.G.SA.hf (conjE E) V.J x y

def unitaryGroup (V : HermSpace E N) : Subgroup (GL (Fin N) E) := unitaryOf (conjE E) V.J

def IsLattice (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤

theorem h_add_left (V : HermSpace E N) (a b x : Fin N → E) :
    V.h (a + b) x = V.h a x + V.h b x := by
  simp [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, add_mul, Finset.sum_add_distrib]

theorem h_smul_left (V : HermSpace E N) (c : E) (a x : Fin N → E) :
    V.h (c • a) x = c * V.h a x := by
  simp [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, Finset.mul_sum, mul_assoc]

def dual (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) (Fin N → E) where
  carrier := {y | ∀ x ∈ L, IsIntegral ℤ (V.h y x)}
  zero_mem' := by
    intro x _
    simpa [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf] using (isIntegral_zero : IsIntegral ℤ (0 : E))
  add_mem' := by
    intro a b ha hb x hx
    rw [h_add_left]
    exact (ha x hx).add (hb x hx)
  smul_mem' := by
    intro c a ha x hx
    rw [← IsScalarTower.algebraMap_smul E c a, h_smul_left]
    exact (show IsIntegral ℤ (algebraMap (𝓞 E) E c) from c.isIntegral_coe).mul (ha x hx)

def linO (g : GL (Fin N) E) : (Fin N → E) →ₗ[𝓞 E] (Fin N → E) :=
  (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) E)).restrictScalars (𝓞 E)

def act (g : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  L.map (linO g)

theorem act_mul (g g' : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    act (g * g') L = act g (act g' L) := by
  rw [act, act, act, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  show ((g * g' : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v =
    (g : Matrix (Fin N) (Fin N) E) *ᵥ ((g' : Matrix (Fin N) (Fin N) E) *ᵥ v)
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (L : Submodule (𝓞 E) (Fin N → E)) : act 1 L = L := by
  have : linO (1 : GL (Fin N) E) = LinearMap.id := by
    ext v i; simp [linO]
  simp [act, this]

def stab (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) : Subgroup (unitaryGroup V) where
  carrier := {g | act (g : GL (Fin N) E) L = L}
  one_mem' := act_one L
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, act_mul] at *
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← act_mul, Subgroup.coe_inv, inv_mul_cancel, act_one]

def fixVec (V : HermSpace E N) (v : Fin N → E) : Subgroup (unitaryGroup V) where
  carrier := {g | ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

def placeJ (V : HermSpace E N) (w : InfinitePlace E) : Matrix (Fin N) (Fin N) ℂ :=
  V.J.map w.embedding

def realPoints (V : HermSpace E N) : Subgroup (InfinitePlace E → GL (Fin N) ℂ) :=
  Subgroup.pi Set.univ (fun w => unitaryOf (starRingEnd ℂ) (placeJ V w))

abbrev RealPts (V : HermSpace E N) : Type := ↥(realPoints V)

instance (V : HermSpace E N) : MeasurableSpace (RealPts V) := borel _

instance (V : HermSpace E N) : BorelSpace (RealPts V) := ⟨rfl⟩

theorem map_conj_map_embedding (w : InfinitePlace E) (A : Matrix (Fin N) (Fin N) E) :
    (A.map (conjE E)).map w.embedding = (A.map w.embedding).map (starRingEnd ℂ) := by
  ext i j
  simp [conjE_apply, IsCMField.complexEmbedding_complexConj]

def toReal (V : HermSpace E N) : unitaryGroup V →* realPoints V where
  toFun g := ⟨fun w => Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E), by
    rw [realPoints, Subgroup.mem_pi]
    intro w _
    have hg : ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)ᵀ * V.J *
        ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (conjE E) = V.J := g.2
    show ((Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E) : GL (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)ᵀ * placeJ V w *
        ((Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E) : GL (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ).map (starRingEnd ℂ) = placeJ V w
    have := congrArg (fun A : Matrix (Fin N) (Fin N) E => A.map w.embedding) hg
    simp only [Matrix.map_mul, Matrix.transpose_map, map_conj_map_embedding] at this
    exact this⟩
  map_one' := by
    ext w : 2
    simp
  map_mul' := by
    intro a b
    ext w : 2
    simp

abbrev gammaVecInf (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → E) :
    Subgroup (RealPts V) :=
  (stab V L ⊓ fixVec V v).map (toReal V)

def realVec (v : Fin N → E) : InfinitePlace E → Fin N → ℂ := fun w i => w.embedding (v i)

def gAct {V : HermSpace E N} (g : RealPts V) (x : InfinitePlace E → Fin N → ℂ) :
    InfinitePlace E → Fin N → ℂ :=
  fun w => (((g : InfinitePlace E → GL (Fin N) ℂ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ x w

structure Majorant (V : HermSpace E N) where

  H : InfinitePlace E → Matrix (Fin N) (Fin N) ℂ
  posDef : ∀ w, (H w).PosDef
  involution : ∀ w, placeJ V w * (H w)⁻¹ * placeJ V w = H w

def Majorant.norm {V : HermSpace E N} (M : Majorant V) (x : InfinitePlace E → Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ w, (ReciprocityTheory.ChartRestriction.G.SA.hf (starRingEnd ℂ) (M.H w) (x w) (x w)).re)

section Adelic

def AdE (E : Type) [Field E] [NumberField E] [IsCMField E] : Type :=
  AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E

instance : CommRing (AdE E) :=
  inferInstanceAs (CommRing (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))

instance : Algebra (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (AdE E) :=
  inferInstanceAs (Algebra _ (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))

instance : TopologicalSpace (AdE E) :=
  moduleTopology (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (AdE E)

variable (E) in

def conjA : AdE E →+* AdE E :=
  (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E)
    (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)))
    (IsCMField.complexConj E).toAlgHom).toRingHom

variable (E) in

def inclA : E →+* AdE E :=
  (Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E]
    (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).toRingHom

def adelicPoints (V : HermSpace E N) : Subgroup (GL (Fin N) (AdE E)) :=
  unitaryOf (conjA E) (V.J.map (inclA E))

instance (V : HermSpace E N) : MeasurableSpace (adelicPoints V) := borel _

instance (V : HermSpace E N) : BorelSpace (adelicPoints V) := ⟨rfl⟩

end Adelic

def fDeg (E : Type) [Field E] [NumberField E] [IsCMField E] : ℕ :=
  Module.finrank ℚ (maximalRealSubfield E)

theorem isClosed_unitaryOf_complex (J : Matrix (Fin N) (Fin N) ℂ) :
    IsClosed (unitaryOf (starRingEnd ℂ) J : Set (GL (Fin N) ℂ)) := by
  have h1 : Continuous (fun g : GL (Fin N) ℂ => (g : Matrix (Fin N) (Fin N) ℂ)) :=
    Units.continuous_val
  have hc : Continuous (fun g : GL (Fin N) ℂ =>
      (g : Matrix (Fin N) (Fin N) ℂ)ᵀ * J * (g : Matrix (Fin N) (Fin N) ℂ).map (starRingEnd ℂ)) :=
    (h1.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (h1.matrix_map Complex.continuous_conj)
  exact isClosed_eq hc continuous_const

theorem isClosed_realPoints (V : HermSpace E N) :
    IsClosed (realPoints V : Set (InfinitePlace E → GL (Fin N) ℂ)) := by
  rw [realPoints, Subgroup.coe_pi]
  exact isClosed_set_pi (fun w _ => isClosed_unitaryOf_complex _)

instance (V : HermSpace E N) : LocallyCompactSpace (RealPts V) := by
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → ℂ))
  exact (isClosed_realPoints V).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : IsCMField (CyclotomicField 4 ℚ) := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact @IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) _ _ {4} ⟨4, rfl, by norm_num⟩
    (CyclotomicField.isCyclotomicExtension 4 ℚ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
