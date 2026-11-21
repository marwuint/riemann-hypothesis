import Formalism.WeaklyAdmissibleFiltrations.StatementPC
import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section Stable
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem pc_actVB_mul (PD : PeriodData G Qp K₀ K B BdR) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, map_mul, AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pc_actVB_res (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, AlgebraTensorModule.map_tmul, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pc_mem_Dpcris {x : V ⊗[Qp] B} :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ (h : G) x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, pc_actVB_res]

theorem pc_Dpcris_stable (g : G) {x : V ⊗[Qp] B} (hx : x ∈ PC.Dpcris ρ) :
    actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [pc_mem_Dpcris] at hx ⊢
  intro h
  have hmem : g⁻¹ * (h : G) * g ∈ PC.H := by
    have := PC.normal.conj_mem (h : G) h.2 g⁻¹
    rwa [inv_inv] at this
  have e : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
  rw [← pc_actVB_mul, e, pc_actVB_mul, hx ⟨_, hmem⟩]

end Stable

end Formalism.WeaklyAdmissibleFiltrations
