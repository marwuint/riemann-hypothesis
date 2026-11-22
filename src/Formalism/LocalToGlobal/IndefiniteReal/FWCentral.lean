import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
import Formalism.LocalToGlobal.ProjectiveLattices.MuValFix
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

noncomputable section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.JoinChr Formalism.IndefR.Links
  Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Central

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G0 : Type} [Group G0] [Fintype G0] (A : FormsL LL Ks WL W G0)

def cen (ζ : LLˣ) (z : G0) : WL →ₗ[LL] WL := (ζ : LL) • A.ρ z

theorem cen_apply (ζ : LLˣ) (z : G0) (x : WL) : cen A ζ z x = (ζ : LL) • A.ρ z x := rfl

variable {ζ : LLˣ} {z : G0}

end Central

section Mat

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
  (i : Fin D.R.m)

theorem principal_form_tensor_expansion (c : Fin (finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → ℂ) :
    Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).w0C b i c) =
      ∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) := by
  have hnP : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < RealDat.nP F.lv2 b := by unfold RealDat.nP; exact_mod_cast Nat.card_pos
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype
    (∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) •
      (⟨R.toRealDat.bC F.lv2 b i _ l, Submodule.subset_span ⟨l, rfl⟩⟩ : R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = _
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.map_smul, smul_comm]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
    (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) = _
  rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hnP, one_smul]

end Mat

section Phase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_zero {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    phiC T hV a 0 = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  rw [CoreJ.phiJ, map_zero, map_zero, smul_zero]

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_apply {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (h : σ = σ') {W : HSp D} (hV : T.V j σ = W) (hV' : T.V j σ' = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    phiC T hV a f g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV' (T.dict j σ'))
      (muPin W (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.cE j σ')) (rdU (T.U j σ') f) g := by
  subst h
  subst hV
  rfl

theorem FWTie.evaluates_of_lUnif (t : FWTie T R κ v₀) (hU : R.LUnif) : t.Evaluates := by
  intro i σ hσ hV
  refine t.ev i σ hσ hV (Classical.byContradiction fun hn => hn ⟨0, fun f => ?_⟩)
  have h0 := t.ev0 i σ hσ hV hn
  have h1 := (hU i σ).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent
  have h2 : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = 0 :=
    funext fun k => absurd (by rw [h0]; rfl) (h1.ne_zero k)
  have h3 : f = 0 := (t.e i).map_eq_zero_iff.1 (Subtype.ext h2)
  subst h3
  exact (congrArg (fun F : MMap (R.MW i σ) => F (v₀ i σ)) (R.HW i σ).e.map_zero).trans (phiC_zero hV _).symm

theorem FWTie.rat_of_val (t : FWTie T R κ v₀) (ht : t.Evaluates) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (hinj : Function.Injective (evAt R i σ (v₀ i σ))) {w : (R.HW i σ).H} {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κ i)
    (h : ∀ g, evAt R i σ (v₀ i σ) w g = ∑ k, σ (a k) * phiC T hV (wtA (κ i)) (f k : T.R ((i : ℕ) + 1)) g) :
    ∃ y, (R.FW i).j σ y = w := by
  refine ⟨∑ k, a k • ((t.e i (f k) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL), hinj (funext fun g => ?_)⟩
  rw [h g, evAt, map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, map_smul, ← ht i σ hσ hV (f k)]
  rfl

theorem baseEmbedding_restriction_eq_coefficientInclusion (t : FWTie T R κ v₀) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    res T (sg0 D A) = O.s0 :=
  (congrArg (res T) (sgAt_mk _ R.hv0)).trans ((res_embLL T t.alg_eq t.laws.pins.2.2.1).trans (sOv_eq T.toCore O.c' O.hle).symm)

theorem phi_eq_phiC {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) {σ : T.Q.c.F →+* ℂ} (hs : σ = O.s0)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (g : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) f g = phiC T hV a f g :=
  (phiC_apply hs hV O.hV a f g).symm

theorem evAt_smul (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) (c : ℂ) (w : (R.HW i σ).H) (g : GA D (Wc D i)) :
    evAt R i σ v (c • w) g = c * (R.HW i σ).e w v g := by
  rw [evAt, map_smul]
  rfl

theorem phase_of_phRat (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.PhRat (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph)
    (x : A.fam.amb.FL i A.μ0) : ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) (baseEmbedding_restriction_eq_coefficientInclusion t O)).trans O.hV
  have hg : ∀ y, D.what₂.embLL y = sg0 D A y := fun y => (DFunLike.congr_fun (sgAt_mk _ R.hv0) y).symm
  (h x).elim fun _ h1 => h1.elim fun a h2 => h2.elim fun f hf =>
    t.rat_of_val (t.evaluates_of_lUnif hU) (base_embedding_good T R t.alg_eq t.laws.pins.2.2.1) hV hinj a f fun g =>
      (evAt_smul i _ _ ph _ g).trans ((hf g).trans (Finset.sum_congr rfl fun _ _ =>
        congrArg₂ (· * ·) (hg _) (phi_eq_phiC O (baseEmbedding_restriction_eq_coefficientInclusion t O) hV _ _ g)))

theorem phase_of_oneMap (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph) :
    ‖ph‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  ⟨h.2.1.2.2.2.2.1, phase_of_phRat t hU hinj O h.2.2⟩

end Phase

end Formalism.IndefR.FWT
