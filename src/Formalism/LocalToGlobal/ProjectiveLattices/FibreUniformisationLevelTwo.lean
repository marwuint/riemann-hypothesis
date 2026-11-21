import Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PerFr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_add {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (v + w) = Data.emb σ v + Data.emb σ w := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_add _ _ _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [Matrix.mulVec_add]; done)
    | (simp [hermC, Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [mul_add, add_mul, Finset.sum_add_distrib, map_add])

theorem perFr_zero {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x 0 τ i = 0 := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (0 : Fin r → E) = 0 := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_zero _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [hermC]; done)
    | (unfold hermC; simp)

end PerFr

section Lin

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : Fin g → ℂ :=
  Pi.single (e.symm ⟨τ, i⟩) 1

theorem eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (q : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eb e τ i (e.symm q) = if q = ⟨τ, i⟩ then 1 else 0 := by
  by_cases hq : q = ⟨τ, i⟩
  · subst hq
    simp [eb]
  · simp [eb, hq, Pi.single_apply, e.symm.injective.eq_iff]

theorem sum_eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ)
    (c : Fin (Dw.mult τ) → ℂ) (l : Fin (Dw.mult τ)) : (∑ j, c j • eb e τ j) (e.symm ⟨τ, l⟩) = c l := by
  simp [Finset.sum_apply, eb_apply]

def blkF {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (z : Fin g → ℂ)
    (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : ℂ :=
  ∑ l, A p.1 p.2 l * z (e.symm ⟨p.1, l⟩)

def blkL {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z j := blkF e A z (e j)
  map_add' z z' := by
    funext j; simp [blkF, mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext j; simp [blkF, Finset.mul_sum, mul_left_comm]

theorem blkL_symm {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (z : Fin g → ℂ)
    (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : blkL e A z (e.symm p) = blkF e A z p := by
  show blkF e A z (e (e.symm p)) = blkF e A z p
  rw [Equiv.apply_symm_apply]

theorem blkL_comp {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (z : Fin g → ℂ) :
    blkL e A (blkL e B z) = blkL e (fun τ => A τ * B τ) z := by
  funext j
  show blkF e A (blkL e B z) (e j) = blkF e (fun τ => A τ * B τ) z (e j)
  simp only [blkF, blkL_symm, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  first
    | exact Finset.sum_comm
    | (rw [Finset.sum_comm])
    | (conv_lhs => rw [Finset.sum_comm])

theorem blkL_one {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (z : Fin g → ℂ) :
    blkL e (fun _ => 1) z = z := by
  funext j
  show blkF e (fun _ => 1) z (e j) = z j
  simp [blkF, Matrix.one_apply]

def blkE {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det) :
    (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
  LinearEquiv.ofLinear (blkL e A) (blkL e fun τ => (A τ)⁻¹)
    (LinearMap.ext fun z => by
      have h1 : (fun τ => A τ * (A τ)⁻¹) = fun _ => 1 := funext fun τ => Matrix.mul_nonsing_inv _ (hA τ)
      simp only [LinearMap.comp_apply, blkL_comp, h1, blkL_one, LinearMap.id_apply])
    (LinearMap.ext fun z => by
      have h1 : (fun τ => (A τ)⁻¹ * A τ) = fun _ => 1 := funext fun τ => Matrix.nonsing_inv_mul _ (hA τ)
      simp only [LinearMap.comp_apply, blkL_comp, h1, blkL_one, LinearMap.id_apply])

theorem blkE_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det)
    (z : Fin g → ℂ) : blkE e A hA z = blkL e A z := rfl

end Lin

section Der

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} {e1 e2 : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e2 (h z) = e1 z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hv : IsDerivAt0 e1 w v) : IsDerivAt0 e2 (h w) v := by
  unfold IsDerivAt0 at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have h0 : h 0 = 0 := map_zero h
  have h3 : e2 0 = e1 0 := by simpa [h0] using he 0
  refine ⟨h1.trans h3.symm, ?_⟩
  intro U hU f
  refine (h2 U hU f).trans ?_
  have hfun : (fun z => valAt' (e1 z) U f) =
      (fun y => valAt' (e2 y) U f) ∘ (LinearEquiv.toContinuousLinearEquiv h) := by
    funext z
    simp [he]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp [h0]

end Der

section Fam

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def pmOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) where
  toFun a := fun j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  map_zero' := by
    funext j
    simp [perFr_zero]
  map_add' a b := by
    funext j
    simp [perFr_add]

def ExpUniq {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P P' : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P' →
    ∀ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b, gam a = a + l.M • b) →
      (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, P' (gam a) = h (P a)) →
      ∀ z, (F.ex i P' (h z)).left = (F.ex i P z).left

def ExpLin {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (m : ℕ) (w : Fin m → (Fin g → ℂ)) (vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
      (cf : Fin m → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) →
      IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v → IsCombAt (F.u i P) vs cf v

def ExpTan {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (w : Fin g → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      IsDerivAt0 (fun z => (F.ex i P z).left) w v →
      IsTanAt (F.u i P) v ∧ ∀ j, w = Pi.single j 1 → IsEigAt c (e j).1 v

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}

theorem derivAt_exists {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left, IsDerivAt0 (fun z => (F.ex i P z).left) w v := by
  obtain ⟨v, hv, -⟩ := (F.ex_diff i P hP).1 w
  exact ⟨_, hv⟩

def blkP {Di : Datum H} (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hA : ∀ τ, IsUnit (A τ).det)
    (P : Di.La →+ (Fin g → ℂ)) : Di.La →+ (Fin g → ℂ) :=
  (blkE e A hA).toLinearMap.toAddMonoidHom.comp P

theorem blockDiagonal_comp_apply {Di : Datum H} (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hA : ∀ τ, IsUnit (A τ).det) (P : Di.La →+ (Fin g → ℂ)) (a : Di.La) :
    blkP (e := e) A hA P a = blkE e A hA (P a) := rfl

end Fam

end Formalism.L2.Pj
