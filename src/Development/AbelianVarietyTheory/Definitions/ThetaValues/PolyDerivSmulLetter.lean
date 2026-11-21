import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint

open NumberField Matrix Complex
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def per (x : Frame X.Ψ r) (v : Fin r → E) : X.Ψ × Fin r → ℂ := fun p =>
  if (p.2 : ℕ) < X.p0 then hermC p.1.1 X.Gm (FD.col (mat x p.1) p.2) (Data.emb p.1.1 v)
  else ((mat x p.1)⁻¹ *ᵥ Data.emb p.1.1 v) p.2

def rowType (p : X.Ψ × Fin r) : E →+* ℂ :=
  if (p.2 : ℕ) < X.p0 then ComplexEmbedding.conjugate p.1.1 else p.1.1

theorem per_apply (x : Frame X.Ψ r) (v : Fin r → E) (p : X.Ψ × Fin r) :
    per X x v p = if (p.2 : ℕ) < X.p0 then
      hermC p.1.1 X.Gm (FD.col (mat x p.1) p.2) (Data.emb p.1.1 v)
      else ((mat x p.1)⁻¹ *ᵥ Data.emb p.1.1 v) p.2 := rfl

theorem per_of_lt (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) {a : Fin r} (h : (a : ℕ) < X.p0) :
    per X x v (τ, a) = hermC τ.1 X.Gm (FD.col (mat x τ) a) (Data.emb τ.1 v) := if_pos h

theorem per_of_le (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) {a : Fin r} (h : X.p0 ≤ (a : ℕ)) :
    per X x v (τ, a) = ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a := if_neg (not_lt.2 h)

theorem rowType_of_lt (τ : X.Ψ) {a : Fin r} (h : (a : ℕ) < X.p0) :
    rowType X (τ, a) = ComplexEmbedding.conjugate τ.1 := if_pos h

theorem rowType_of_le (τ : X.Ψ) {a : Fin r} (h : X.p0 ≤ (a : ℕ)) : rowType X (τ, a) = τ.1 :=
  if_neg (not_lt.2 h)

theorem per_add (x : Frame X.Ψ r) (u v : Fin r → E) :
    per X x (u + v) = per X x u + per X x v := by
  funext p
  have h : Data.emb p.1.1 (u + v) = Data.emb p.1.1 u + Data.emb p.1.1 v := by
    funext a; simp [Data.emb]
  simp only [per, Pi.add_apply, h]
  split_ifs
  · simp [hermC, mul_add, Finset.sum_add_distrib]
  · rw [mulVec_add, Pi.add_apply]

theorem per_smul (x : Frame X.Ψ r) (α : E) (v : Fin r → E) (p : X.Ψ × Fin r) :
    per X x (α • v) p = rowType X p α * per X x v p := by
  have h : Data.emb p.1.1 (α • v) = p.1.1 α • Data.emb p.1.1 v := by
    funext a; simp [Data.emb]
  simp only [per, rowType, h]
  split_ifs
  · simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
      ComplexEmbedding.conjugate_coe_eq]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]

theorem per_ratSmul (x : Frame X.Ψ r) (q : ℚ) (v : Fin r → E) :
    per X x (q • v) = q • per X x v := by
  funext p
  rw [← Rat.cast_smul_eq_qsmul E, per_smul, map_ratCast, Pi.smul_apply, Rat.smul_def]

def perLin (x : Frame X.Ψ r) : (Fin r → E) →ₗ[ℚ] (X.Ψ × Fin r → ℂ) where
  toFun := per X x
  map_add' := per_add X x
  map_smul' := per_ratSmul X x

@[simp] theorem perLin_apply (x : Frame X.Ψ r) (v : Fin r → E) : perLin X x v = per X x v := rfl

@[simp] theorem per_zero (x : Frame X.Ψ r) : per X x 0 = 0 := map_zero (perLin X x)

theorem per_neg (x : Frame X.Ψ r) (v : Fin r → E) : per X x (-v) = -per X x v :=
  map_neg (perLin X x) v

theorem per_zsmul (x : Frame X.Ψ r) (m : ℤ) (v : Fin r → E) : per X x (m • v) = m • per X x v :=
  map_zsmul (perLin X x) m v

theorem per_sum {ι : Type*} (x : Frame X.Ψ r) (s : Finset ι) (v : ι → Fin r → E) :
    per X x (∑ i ∈ s, v i) = ∑ i ∈ s, per X x (v i) := map_sum (perLin X x) v s

def EF (u v : Fin r → E) : ℚ := EFf (X.κ0 / 2) X.Gm u v

theorem EF_def (u v : Fin r → E) :
    EF X u v = Algebra.trace ℚ E (-(X.κ0 / 2) * herm X.Gm u v) := rfl

theorem im_neg_half_pos (τ : X.Ψ) : 0 < (τ.1 (-(X.κ0 / 2))).im := by
  have := X.κ0_sign τ
  simp only [map_neg, map_div₀, map_ofNat, neg_im, div_ofNat_im]
  linarith

theorem EF_eq_or : (∀ u v, EF X u v = EFf X.ξ0 X.Gm u v) ∨
    ∀ u v, EF X u v = -EFf X.ξ0 X.Gm u v := by
  rcases X.κ0_xi with h | h
  · refine Or.inl fun u v => ?_
    rw [EF, h, mul_div_cancel_left₀ _ two_ne_zero]
  · refine Or.inr fun u v => ?_
    rw [EF_def, EFf, ← map_neg, h]
    congr 1; ring

variable {g : ℕ}

def IsSympl (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Prop :=
  ∀ a b, EF X (bas a) (bas b) = -(omegaStd a b : ℤ)

section Periods

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

def perMat (s : Fin g → Fin g ⊕ Fin g) (x : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i k => per X x (bas (Pi.single (s k) 1)) (idx i)

def hMat (x : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ := (perMat X bas idx Sum.inl x)⁻¹

def tauMat (x : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  hMat X bas idx x * perMat X bas idx Sum.inr x

def imInv (x : Frame X.Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  (((tauMat X bas idx x).map Complex.im)⁻¹).map fun t : ℝ => (t : ℂ)

@[simp] theorem perMat_apply (s : Fin g → Fin g ⊕ Fin g) (x : Frame X.Ψ r) (i k : Fin g) :
    perMat X bas idx s x i k = per X x (bas (Pi.single (s k) 1)) (idx i) := rfl

theorem perMat_mulVec_single (s : Fin g → Fin g ⊕ Fin g) (x : Frame X.Ψ r) (k : Fin g) :
    perMat X bas idx s x *ᵥ Pi.single k 1 = per X x (bas (Pi.single (s k) 1)) ∘ idx := by
  funext i; simp

theorem imInv_eq (x : Frame X.Ψ r) :
    imInv X bas idx x = ((tauMat X bas idx x).map fun z => (z.im : ℂ))⁻¹ := by
  have hd : ((tauMat X bas idx x).map fun z => (z.im : ℂ)) =
      Complex.ofRealHom.mapMatrix ((tauMat X bas idx x).map Complex.im) := rfl
  by_cases h : IsUnit ((tauMat X bas idx x).map Complex.im).det
  · refine (Matrix.inv_eq_left_inv ?_).symm
    rw [hd, imInv]
    change Complex.ofRealHom.mapMatrix _ * _ = _
    rw [← map_mul, nonsing_inv_mul _ h, map_one]
  · rw [imInv, nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit]
    · simp
    · rw [hd, ← RingHom.map_det]
      simpa using h

theorem per_bas (x : Frame X.Ψ r) (m : Fin g ⊕ Fin g → ℤ) :
    per X x (bas m) ∘ idx = perMat X bas idx Sum.inl x *ᵥ (fun k => (m (Sum.inl k) : ℂ)) +
      perMat X bas idx Sum.inr x *ᵥ fun k => (m (Sum.inr k) : ℂ) := by
  have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
    funext j; simp [Pi.single_apply]
  funext i
  conv_lhs => rw [hm, map_sum, AddSubmonoidClass.coe_finset_sum, per_sum]
  simp only [map_zsmul, AddSubgroupClass.coe_zsmul, per_zsmul, Fintype.sum_sum_type]
  simp [mulVec, dotProduct, mul_comm]

theorem hMat_mulVec_per {x : Frame X.Ψ r} (h : IsUnit (perMat X bas idx Sum.inl x).det)
    (m : Fin g ⊕ Fin g → ℤ) :
    hMat X bas idx x *ᵥ (per X x (bas m) ∘ idx) = (fun k => (m (Sum.inl k) : ℂ)) +
      tauMat X bas idx x *ᵥ fun k => (m (Sum.inr k) : ℂ) := by
  rw [per_bas, mulVec_add, mulVec_mulVec, mulVec_mulVec, tauMat]
  congr 1
  rw [hMat, nonsing_inv_mul _ h, one_mulVec]

def canFn (a b : Fin g → ℝ) (x : Frame X.Ψ r) (z : Fin g → ℂ) : ℂ :=
  cexp (Real.pi / 2 * ((hMat X bas idx x *ᵥ z) ⬝ᵥ imInv X bas idx x *ᵥ (hMat X bas idx x *ᵥ z))) *
    thetaChar (tauMat X bas idx x) (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (hMat X bas idx x *ᵥ z)

end Periods

section Rows

def rowIdx {p q r : ℕ} (hr : p + q = r) : Fin q ⊕ Fin p ≃ Fin r :=
  (Equiv.sumComm _ _).trans ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr hr)))

@[simp] theorem rowIdx_inl {p q r : ℕ} (hr : p + q = r) (i : Fin q) :
    (rowIdx hr (Sum.inl i) : ℕ) = p + i := rfl

@[simp] theorem rowIdx_inr {p q r : ℕ} (hr : p + q = r) (i : Fin p) :
    (rowIdx hr (Sum.inr i) : ℕ) = p - 1 - i := by
  change p - (i + 1) = _
  omega

variable {q0 : ℕ} (hr : X.p0 + q0 = r)

def rowOf : X.Ψ × (Fin q0 ⊕ Fin X.p0) ≃ X.Ψ × Fin r := Equiv.prodCongr (Equiv.refl _) (rowIdx hr)

@[simp] theorem rowOf_apply (τ : X.Ψ) (ρ : Fin q0 ⊕ Fin X.p0) :
    rowOf X hr (τ, ρ) = (τ, rowIdx hr ρ) := rfl

theorem rowType_rowOf_inl (τ : X.Ψ) (i : Fin q0) : rowType X (rowOf X hr (τ, Sum.inl i)) = τ.1 :=
  rowType_of_le X τ (by simp)

theorem rowType_rowOf_inr (τ : X.Ψ) (i : Fin X.p0) :
    rowType X (rowOf X hr (τ, Sum.inr i)) = ComplexEmbedding.conjugate τ.1 :=
  rowType_of_lt X τ (by have := i.isLt; rw [rowIdx_inr]; omega)

def wtOf (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (n : ℕ) : Wt X.Ψ r := fun τ a =>
  Sum.elim (fun i => (Harm.partOf (c τ) i : ℤ) + (n / 2 : ℕ))
    (fun i => -(Harm.partOf (c' τ) i : ℤ) - (n / 2 : ℕ)) ((rowIdx hr).symm a)

@[simp] theorem wtOf_inl (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (n : ℕ) (τ : X.Ψ)
    (i : Fin q0) :
    wtOf X hr c c' n τ (rowIdx hr (Sum.inl i)) = (Harm.partOf (c τ) i : ℤ) + (n / 2 : ℕ) := by
  rw [wtOf, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem wtOf_inr (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (n : ℕ) (τ : X.Ψ)
    (i : Fin X.p0) :
    wtOf X hr c c' n τ (rowIdx hr (Sum.inr i)) = -(Harm.partOf (c' τ) i : ℤ) - (n / 2 : ℕ) := by
  rw [wtOf, Equiv.symm_apply_apply, Sum.elim_inr]

theorem wtOf_isDominant (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (n : ℕ) :
    X.IsDominant (wtOf X hr c c' n) := by
  intro τ
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ <;>
    obtain ⟨i | i, rfl⟩ := (rowIdx hr).surjective i <;>
    obtain ⟨j | j, rfl⟩ := (rowIdx hr).surjective j <;>
    have hi := i.isLt <;> have hj := j.isLt <;>
    simp only [Fin.le_def, rowIdx_inl, rowIdx_inr, wtOf_inl, wtOf_inr] <;> intro h₁ h₂ <;>
    first
      | omega
      | (have := Harm.partOf_antitone (c τ) (show i ≤ j by rw [Fin.le_def]; omega); omega)
      | (have := Harm.partOf_antitone (c' τ) (show j ≤ i by rw [Fin.le_def]; omega); omega)

end Rows

section Series

variable {q0 : ℕ} (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
  (idx : Fin g ≃ X.Ψ × Fin r)

def letterDir {n : ℕ} (l : Harm.Var X.Ψ q0 X.p0 (Fin n)) : Fin n → Fin g → ℂ :=
  Pi.single l.2.2 (Pi.single (idx.symm (rowOf X hr (l.1, l.2.1))) 1)

def thFr (n : ℕ) (a b : Fin n → Fin g → ℝ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (x : Frame X.Ψ r) : ℂ :=
  (hMat X bas idx x).det ^ (n / 2) *
    polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas idx (a k) (b k) x (z k)) 0

variable (n : ℕ) (a b : Fin n → Fin g → ℝ)

theorem thFr_add (P Q : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thFr X hr bas idx n a b (P + Q) = thFr X hr bas idx n a b P + thFr X hr bas idx n a b Q := by
  funext x
  simp only [thFr, I2.polyDeriv_add, mul_add, Pi.add_apply]

theorem thFr_smul (c : ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thFr X hr bas idx n a b (c • P) = c • thFr X hr bas idx n a b P := by
  funext x
  simp only [thFr, I2.polyDeriv_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

def thFrLin : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n) →ₗ[ℂ] (Frame X.Ψ r → ℂ) where
  toFun := thFr X hr bas idx n a b
  map_add' := thFr_add X hr bas idx n a b
  map_smul' := thFr_smul X hr bas idx n a b

@[simp] theorem thFrLin_apply (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thFrLin X hr bas idx n a b P = thFr X hr bas idx n a b P := rfl

@[simp] theorem thFr_zero : thFr X hr bas idx n a b 0 = 0 := map_zero (thFrLin X hr bas idx n a b)

end Series

section Diagonal

def rowFac (d : X.Ψ → Fin r → ℂ) (p : X.Ψ × Fin r) : ℂ :=
  if (p.2 : ℕ) < X.p0 then d p.1 p.2 else (d p.1 p.2)⁻¹

variable {X} {d : X.Ψ → Fin r → ℂ} (hd : ∀ τ a, d τ a ≠ 0)
include hd

theorem rowFac_ne_zero (p : X.Ψ × Fin r) : rowFac X d p ≠ 0 := by
  unfold rowFac
  split_ifs
  · exact hd _ _
  · exact inv_ne_zero (hd _ _)

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

omit hd in

theorem polyDeriv_smul_letter {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (s : σ → ℂ) (t : ℂ) (h : ∀ m ∈ P.support, (m.prod fun l e => s l ^ e) = t)
    (u : σ → W) (F : W → ℂ) (w : W) :
    polyDeriv P (fun l => s l • u l) F w = t * polyDeriv P u F w := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, ← h m hm, mul_left_comm]
  have h1 := (finCongr (Multiset.length_toList (Finsupp.toMultiset m)).symm).prod_comp
    fun k => s ((Finsupp.toMultiset m).toList.get k)
  have h2 : ∏ k, s ((Finsupp.toMultiset m).toList.get k) =
      ((Finsupp.toMultiset m).toList.map s).prod := by
    simp [← Fin.prod_univ_fun_getElem]
  refine congrArg (· * _) ((h1.trans h2).trans ?_)
  rw [Multiset.prod_map_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]

end Diagonal

namespace Gauss

open HyperbolicCusp
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)

instance : Unique flagData.Ψ :=
  have hne : Nonempty flagData.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E4 →+* ℂ) := inferInstance
    by_cases h : τ ∈ flagData.Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, not_not.1 (mt (flagData.cmType τ).2 h)⟩⟩
  { default := Classical.choice hne
    uniq := fun τ => Subtype.ext <| RingHom.ext fun z => by
      obtain ⟨p, q, rfl⟩ := exists_rat z
      simp [emb_ii_eq] }

end Gauss

end

end GlobalTheory.ThFr
