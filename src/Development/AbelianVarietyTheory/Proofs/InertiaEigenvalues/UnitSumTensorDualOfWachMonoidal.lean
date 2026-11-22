import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorLatticeUnitPart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR

noncomputable section

namespace GlobalTheory.Cmp.WachMonoidal

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke

section Crys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem tensorB_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g (CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x) =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem tensorB_id (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [CrystallineSubrepresentation.tensorB]

theorem tensorB_zero (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

theorem tensorB_add (f g : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (f + g) x =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x + CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB, add_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]; abel

theorem coe_DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : CrystallineSubrepresentation.IsEquivariant ρ ρ' f) (x : ↥(Dcris PD ρ)) :
    (CrystallineSubrepresentation.DcrisMap PD hf x : V' ⊗[Qp] B) = CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x := rfl

theorem isCrys_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have h1 : CrystallineSubrepresentation.IsEquivariant ρ ρ' e.toLinearMap := he
  have h2 : CrystallineSubrepresentation.IsEquivariant ρ' ρ e.symm.toLinearMap := fun g x => by
    apply e.injective
    simp [he]
  let E : ↥(Dcris PD ρ) ≃ₗ[LL] ↥(Dcris PD ρ') :=
    LinearEquiv.ofLinear (CrystallineSubrepresentation.DcrisMap PD h1) (CrystallineSubrepresentation.DcrisMap PD h2)
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
  unfold IsCrys at h ⊢
  rw [← E.finrank_eq, ← e.finrank_eq, h]

theorem finite_Dcris [FiniteDimensional LL V] {ρ : Representation LL G V} (h : IsCrys PD ρ) :
    Module.Finite LL ↥(Dcris PD ρ) := by
  rcases Nat.eq_zero_or_pos (finrank LL ↥(Dcris PD ρ)) with h0 | h0
  · have := PD.finK₀
    have hK : 0 < finrank Qp K₀ := Module.finrank_pos
    unfold IsCrys at h
    have hV : finrank LL V = 0 := by
      rw [h0] at h
      rcases Nat.mul_eq_zero.mp h.symm with h | h
      · omega
      · exact h
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    infer_instance
  · exact Module.finite_of_finrank_pos h0

theorem isCrys_prod [FiniteDimensional LL V] [FiniteDimensional LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : IsCrys PD ρ) (h' : IsCrys PD ρ') : IsCrys PD (ρ.prod ρ') := by
  have := finite_Dcris PD h
  have := finite_Dcris PD h'
  have e1 : CrystallineSubrepresentation.IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V') := fun g x => by
    simp [Representation.prod]
  have e2 : CrystallineSubrepresentation.IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V') := fun g x => by
    simp [Representation.prod]
  have p1 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ (LinearMap.fst LL V V') := fun g x => by
    simp [Representation.prod]
  have p2 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ' (LinearMap.snd LL V V') := fun g x => by
    simp [Representation.prod]
  let E : (↥(Dcris PD ρ) × ↥(Dcris PD ρ')) ≃ₗ[LL] ↥(Dcris PD (ρ.prod ρ')) :=
    LinearEquiv.ofLinear ((CrystallineSubrepresentation.DcrisMap PD e1).coprod (CrystallineSubrepresentation.DcrisMap PD e2))
      ((CrystallineSubrepresentation.DcrisMap PD p1).prod (CrystallineSubrepresentation.DcrisMap PD p2))
      (by
        refine LinearMap.ext fun x => Subtype.ext ?_
        simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
          Submodule.coe_add, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [← tensorB_add, show (LinearMap.inl LL V V').comp (LinearMap.fst LL V V') +
          (LinearMap.inr LL V V').comp (LinearMap.snd LL V V') = LinearMap.id by ext <;> simp,
          tensorB_id])
      (by
        refine LinearMap.ext fun x => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, tensorB_id, tensorB_zero, add_zero]
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, tensorB_id, tensorB_zero, zero_add])
  unfold IsCrys at h h' ⊢
  rw [← E.finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end Crys

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem isCrys_of_isSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L)
    (i' : LatHom T'.L T''.L) (h : IsCrys PD T.ρ) (h' : IsCrys PD T'.ρ) (hs : TensorLatticeUnitPart.IsSumLat i i') :
    IsCrys PD T''.ρ :=
  isCrys_of_equiv PD (LinearEquiv.ofBijective (i.f.coprod i'.f) hs.1)
    (fun g x => by simp [Representation.prod, i.equiv, i'.equiv]) (isCrys_prod PD h h')

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unit_iff (E : EtTie W RA RW inclR φR gR πA) : UnitDualParts.UnitFor E ↔ TensorLatticeUnitPart.UnitAt W E :=
  Iff.rfl

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

end GlobalTheory.Cmp.WachMonoidal
