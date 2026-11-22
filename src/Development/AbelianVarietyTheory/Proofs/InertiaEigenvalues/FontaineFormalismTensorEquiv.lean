import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorMultiplication
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation

noncomputable section

namespace GlobalTheory.FontCmp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Tools

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

variable (LL) in

def mB (b : B) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

@[simp] theorem mB_tmul (b b' : B) (v : V) : mB LL b (v ⊗ₜ[Qp] b') = v ⊗ₜ[Qp] (b * b') := by
  simp [mB]

theorem mulVB_eq (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (LL := LL) c x = mB LL (algebraMap K₀ B c) x := rfl

theorem mB_mul (b b' : B) (x : V ⊗[Qp] B) : mB LL (b * b') x = mB LL b (mB LL b' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [mul_assoc]
  | add a c ha hc => simp only [map_add, ha, hc]

theorem mB_add (b b' : B) (x : V ⊗[Qp] B) : mB LL (b + b') x = mB LL b x + mB LL b' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [add_mul, tmul_add]
  | add a c ha hc => simp only [map_add, ha, hc]; abel

theorem mB_one (x : V ⊗[Qp] B) : mB LL (1 : B) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add a c ha hc => simp only [map_add, ha, hc]

theorem comm_smulB (b : B) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • x) = mB LL b (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add, ha, hc]

def mK (ρ : Representation LL G V) (c : K₀) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ) :=
  (mB LL (algebraMap K₀ B c)).restrict (fun x hx => by
    rw [CrystallineSubrepresentation.mem_Dcris] at hx ⊢
    intro g
    rw [← mulVB_eq, CrystallineSubrepresentation.actVB_mulVB, hx])

@[simp] theorem coe_mK (ρ : Representation LL G V) (c : K₀) (d : ↥(Dcris PD ρ)) :
    (mK PD ρ c d : V ⊗[Qp] B) = mB LL (algebraMap K₀ B c) d := rfl

theorem cmp_ind {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    {P : V ⊗[Qp] B → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hb : ∀ (b : B) (d : ↥(Dcris PD ρ)), P (mB LL b d)) (x : V ⊗[Qp] B) : P x := by
  obtain ⟨u, hu⟩ := h.2 ((TensorProduct.comm Qp B V).symm x)
  have : x = TensorProduct.comm Qp B V (CrystallineSubrepresentation.comparison PD ρ u) := by rw [hu]; simp
  subst this
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul b d =>
    rw [CrystallineSubrepresentation.comparison_tmul, comm_smulB (LL := LL)]
    exact hb b ⟨_, d.2⟩
  | add a c ha hc => simpa only [map_add] using hadd _ _ ha hc

include PD in
theorem exists_retr : ∃ lam : B →ₗ[K₀] K₀, lam 1 = 1 := by
  have : (1 : B) ≠ 0 := by
    intro h
    apply PD.not_mem_filtration_two
    rw [← mul_one PD.t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K₀ this
  exact ⟨(f 1)⁻¹ • f, by simp [hf]⟩

theorem prod_mB_left (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (mB LL b x ⊗ₜ[LL] y) = mB LL b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_assoc]

theorem prod_mB_right (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] mB LL b y) = mB LL b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_left_comm]

theorem act_prod (ρ : Representation LL G V) (ρ' : Representation LL G V') (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    actVB PD (ρ.tprod ρ') g (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) =
      CrystallineSubrepresentation.prodB (actVB PD ρ g x ⊗ₜ[LL] actVB PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, actVB]

theorem prod_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (x : ↥(Dcris PD ρ)) (y : ↥(Dcris PD ρ')) :
    CrystallineSubrepresentation.prodB (LL := LL) ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B)) ∈ Dcris PD (ρ.tprod ρ') := by
  rw [CrystallineSubrepresentation.mem_Dcris]
  intro g
  rw [act_prod, (CrystallineSubrepresentation.mem_Dcris PD ρ x).1 x.2, (CrystallineSubrepresentation.mem_Dcris PD ρ' y).1 y.2]

theorem unit_eq : Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  obtain ⟨lam, hl⟩ := exists_retr PD
  ext x
  rw [CrystallineSubrepresentation.mem_Dcris]
  constructor
  · intro hx

    let ctr : (LL →ₗ[Qp] Qp) → (LL ⊗[Qp] B →ₗ[Qp] B) := fun f =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B f
    have hc : ∀ f g y, ctr f (actVB PD (Representation.trivial LL G LL) g y) =
        PD.actB g (ctr f y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul a b =>
        simp only [ctr, actVB]
        simp
        rw [← IsScalarTower.algebraMap_smul K₀ (f a) b, map_smul, IsScalarTower.algebraMap_smul]
    let r : B →ₗ[Qp] K₀ := lam.restrictScalars Qp
    let j : K₀ →ₗ[Qp] B := (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap
    have hr : ∀ f y, ctr f (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) j
        (LinearMap.lTensor LL r y)) = j (r (ctr f y)) := by
      intro f y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul a b => simp [ctr]
    have hsep : ∀ y : LL ⊗[Qp] B, (∀ f, ctr f y = 0) → y = 0 := by
      intro y hy
      classical
      let bs := Module.Free.chooseBasis Qp LL
      apply (TensorProduct.comm Qp LL B).injective
      apply (TensorProduct.equivFinsuppOfBasisRight bs).injective
      ext i
      have : ∀ y : LL ⊗[Qp] B, TensorProduct.equivFinsuppOfBasisRight bs
          (TensorProduct.comm Qp LL B y) i = ctr (bs.coord i) y := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]
        | tmul a b => simp [ctr]
      simp [this, hy]
    refine ⟨LinearMap.lTensor LL r x, ?_⟩
    rw [← sub_eq_zero]
    apply hsep
    intro f
    rw [map_sub, hr]
    obtain ⟨c, hc'⟩ := PD.invB (ctr f x) (fun g => by rw [← hc, hx])
    rw [← hc', sub_eq_zero]
    change algebraMap K₀ B (lam (algebraMap K₀ B c)) = _
    rw [Algebra.algebraMap_eq_smul_one c, map_smul, hl]
    simp [Algebra.algebraMap_eq_smul_one]
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul a b => simp [actVB]

variable (LL V) in

def actKK (τ : K₀ →ₐ[Qp] LL) : K₀ ⊗[Qp] K₀ →+ (V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) :=
  liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
      (fun c => τ a • mB LL (algebraMap K₀ B c))
      (fun c c' => by ext x; simp [mB_add, add_mul, tmul_add]))
      (fun a a' => by ext c x; simp [add_smul]))
    (fun r a c => by
      ext v b
      simp only [AddMonoidHom.mk'_apply, map_smul, AlgebraTensorModule.curry_apply,
        LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.smul_apply, mB_tmul]
      rw [smul_assoc, smul_comm r, ← tmul_smul, ← smul_mul_assoc, Algebra.smul_def r c, map_mul,
        ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def])

theorem mem_DcrisL (ρ : Representation LL G V) (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧ ∀ c : K₀, mB LL (algebraMap K₀ B c) x = τ c • x := by
  simp [DcrisL, Submodule.mem_iInf, sub_eq_zero, mulVB_eq]

end Tools

theorem inv_iff : CrystallineSubrepresentation.InvariantsEq PD ↔ TensorMultiplication.InvB PD := Iff.rfl

variable (LL : Type) [Field LL] [Algebra Qp LL]

theorem sub_iff : CrystallineSubrepresentation.SubCrys PD LL ↔ TensorMultiplication.CrysSub PD LL := Iff.rfl

theorem quot_iff : CrystallineSubrepresentation.QuotCrys PD LL ↔ TensorMultiplication.CrysQuot PD LL := Iff.rfl

theorem sum_iff : CrystallineSubrepresentation.SumCrys PD LL ↔ TensorMultiplication.CrysSum PD LL := Iff.rfl

theorem tensor_iff : CrystallineSubrepresentation.TensorCrys PD LL ↔ TensorMultiplication.CrysTensor PD LL := Iff.rfl

theorem dual_iff : CrystallineSubrepresentation.DualCrys PD LL ↔ TensorMultiplication.CrysDual PD LL := Iff.rfl

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

end GlobalTheory.FontCmp
