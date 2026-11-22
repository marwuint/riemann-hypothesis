import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates

noncomputable section

namespace GlobalTheory.Mem.SJ

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs}

structure Read (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) where

  wU : D.what₂.Word → (fc X.zs).Dc.Mem

  eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V

  eRR : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V

  jV : (Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb D.what₂.mu0

  v0 : Bs.v0 = InfinitePlace.mk D.what₂.embLL

  twist : ∀ a, Bs.v0.embedding a = cj s (D.what₂.embLL a)

variable {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}

structure Seam (R : Read D X fc s) (cr : Crd A fc) where

  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc X.zs).Dc.a (R.wU u)) → ℂ)

  cF : (Fin ((fc X.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0

  eR : D.what₂.EE →ₛₗ[cj s] X.EE

  cφ_eq : ∀ u x, (cφ u).symm (cpt D.what₂.embLL x) = D.jN u (R.eNu u x)

  cF_eq : ∀ y, cF (cpt D.what₂.embLL y) = R.jV y

  eR_eq : ∀ y, eR (D.jEE (R.eRR y)) = X.iC cr true Bs.μ0 (cpt Bs.v0.embedding y)

namespace Read

variable (R : Read D X fc s)

def DcPt : Prop :=
  ∀ u x y, D.what₂.embLL ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y) = D.what₂.perCol u D.what₂.mu0 (D.jN u (R.eNu u x)) (R.jV y)

def ReadingFormsSpanGoodSubspace : Prop := Submodule.span ℂ (Set.range R.jV) = D.what₂.V0 D.what₂.mu0

def IotaRd (cr : Crd A fc) : Prop :=
  ∀ y, D.what₂.iota D.what₂.mu0 (R.jV y) =
    D.jEE (R.eRR ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec y)))

def NuTie : Prop := ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (R.wU u)) (R.eNu u)

def RRTie (cr : Crd A fc) : Prop := ∃ L, HLatTie D.div.RR L (X.XE cr true) R.eRR

end Read

structure CxFacts (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : Prop where

  wf : (fc X.zs).Df1.WF

  h2 : X.H2 cr true

  pos : X.H4pos

  theta : ∀ y, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) =
    X.Θ Bs.μ0 (X.jR Bs.μ0 (cr.toR X.zs true Bs.μ0 (((fc X.zs).Df1.Pq Bs.μ0).mulVec y)))

def cjv (s : Bool) {n : ℕ} (x : Fin n → ℂ) : Fin n → ℂ := fun i => cj s (x i)

namespace Seam

variable {R : Read D X fc s} {cr : Crd A fc} (M : Seam R cr)

def ChainTie : Prop :=
  ∀ u (x : Fin ((fc X.zs).Dc.a (R.wU u)) → D.what₂.LL) (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
    D.what₂.perCol u D.what₂.mu0 ((M.cφ u).symm (cpt D.what₂.embLL x)) (M.cF (cpt D.what₂.embLL y)) =
      D.what₂.embLL ((fc X.zs).Dc.Pt (R.wU u) Bs.μ0 x y)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range M.cF

def RowTie (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t) : Prop :=
  (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ (∃ c : ℝ, 0 < c ∧ ∀ F, ‖M.eR F‖ = c * ‖F‖) ∧
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL,
      X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = lam • M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y)))

def ColNorm : Prop :=
  ∀ u, ∃ c : ℝ, 0 < c ∧ ∀ φ : D.what₂.Mu u, Formalism.DivisionValues.fnorm ((fc X.zs).Dc.Xc (R.wU u) Bs.v0) (cjv s (M.cφ u φ)) = c * ‖φ‖

end Seam

section Extend

theorem lin_cpt_semilinear {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem lin_bijective_of_form {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    Function.Bijective (lin fun k => j (e (Pi.single k 1))) := by
  classical
  have hcpt : ∀ y, lin (fun k => j (e (Pi.single k 1))) (cpt σ y) = j (e y) := fun y =>
    lin_cpt_semilinear σ (j.comp e.toLinearMap) y
  have hsurj : Function.Surjective (lin fun k => j (e (Pi.single k 1))) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine LinearMap.mem_range.2 ⟨cpt σ (e.symm (b i)), ?_⟩
    rw [hcpt, LinearEquiv.apply_symm_apply]
  have : Module.Finite K V := Module.Finite.equiv e
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  let bE := Module.Basis.mk hb.1 hb.2.ge
  have : FiniteDimensional ℂ E := Module.Finite.of_basis bE
  have hdim : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis bE, ← Module.finrank_eq_card_basis b,
      ← e.finrank_eq, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩

def cjvL (s : Bool) (n : ℕ) : (Fin n → ℂ) →ₛₗ[cj s] (Fin n → ℂ) where
  toFun := cjv s
  map_add' x y := by funext i; simp [cjv]
  map_smul' a x := by funext i; simp [cjv]

namespace Read

variable (R : Read D X fc s)

include R in

theorem cjv_cpt_embLL {n : ℕ} (x : Fin n → D.what₂.LL) : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
  funext i
  simp only [cjv, cpt]
  rw [R.twist]

def colCrd (u : D.what₂.Word) : (Fin ((fc X.zs).Dc.a (R.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u :=
  LinearEquiv.ofBijective _ (lin_bijective_of_form D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u))

def rowCrd : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ) ≃ₗ[ℂ] D.what₂.EE :=
  LinearEquiv.ofBijective _ (lin_bijective_of_form D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis)

theorem rowCrd_cpt (y : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) :
    R.rowCrd (cpt D.what₂.embLL y) = D.jEE (R.eRR y) := by
  simp only [rowCrd, LinearEquiv.ofBijective_apply]
  exact lin_cpt_semilinear _ (D.jEE.comp R.eRR.toLinearMap) y

def seam (cr : Crd A fc) : Seam R cr where
  cφ u := (R.colCrd u).symm
  cF := lin fun k => R.jV (Pi.single k 1)
  eR := (X.iC cr true Bs.μ0).comp ((cjvL s _).comp R.rowCrd.symm.toLinearMap)
  cφ_eq u x := lin_cpt_semilinear D.what₂.embLL ((D.jN u).comp (R.eNu u).toLinearMap) x
  cF_eq y := lin_cpt_semilinear _ _ y
  eR_eq y := by
    show X.iC cr true Bs.μ0 (cjv s (R.rowCrd.symm _)) = _
    rw [← R.rowCrd_cpt, LinearEquiv.symm_apply_apply, R.cjv_cpt_embLL]

instance (cr : Crd A fc) : Inhabited (Seam R cr) := ⟨R.seam cr⟩

end Read

end Extend

namespace Seam

end Seam

section OfTie

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

variable (F : Face D A) (X : CxData A.fam.amb) {S₀ : IndefData (A.side F.P0 F.ψ0 X.zs)} {X₀ : BaseLevelRowSide D}
  (I : DivisionCompatibilityData D A F.P0 F.ψ0 F.P1 F.ψ1 X.zs S₀ (X.data F.cr true) X₀ (F.Dc X.zs))

variable {Sp : SPer (F.Dc X.zs)} {C : ColData (F.Dc X.zs) Sp (X.data F.cr true)}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin ((F.Dc X.zs).a u) → D.what₂.LL)}

end OfTie

section Place

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

end Block

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (F : Face D A)

variable (X : CxData A.fam.amb) {n : ℕ}

end Place

end GlobalTheory.Mem.SJ

end
