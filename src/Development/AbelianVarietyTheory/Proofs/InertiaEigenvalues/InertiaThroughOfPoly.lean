import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPoly

theorem aeval_mem_of_stable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (p : L[X]) : ∀ x ∈ D, Polynomial.aeval f p x ∈ D := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Module.algebraMap_end_apply] using D.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using D.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    have := ih _ (hD x hx)
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact this

section
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

theorem actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ (g * h) x = actVB PC.PD ρ g (actVB PC.PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actVB_one' (x : V ⊗[Qp] B) : actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actVB_resH (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_Dpcris_iff (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ g ∈ PC.H, actVB PC.PD ρ g x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]

theorem Dpcris_stable (g : G) : ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  intro x hx
  rw [mem_Dpcris_iff] at hx ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ PC.H := by simpa using PC.normal.conj_mem h hh g⁻¹
  rw [← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]

end

end GlobalTheory.PassPoly

end
