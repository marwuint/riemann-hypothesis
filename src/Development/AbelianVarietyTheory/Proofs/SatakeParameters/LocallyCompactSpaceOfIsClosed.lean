import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SmoothCartan
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryRepR

noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic MeasureTheory
open scoped Matrix ComplexOrder

namespace GlobalTheory.Mt.Adelic

section HeckeFam

variable {Gf : Type} [Group Gf] (Kf : Subgroup Gf)

def IsHeckeFam {n : ℕ} (z : Fin n → Gf) : Prop :=
  ∀ k ∈ Kf, (Finset.univ.val.map fun i => ((k * z i : Gf) : Gf ⧸ Kf)) =
    Finset.univ.val.map fun i => ((z i : Gf) : Gf ⧸ Kf)

variable {Kf}

theorem sum_heckeFam {M : Type*} [AddCommMonoid M] {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z)
    (F : Gf ⧸ Kf → M) {k : Gf} (hk : k ∈ Kf) :
    ∑ i, F ((k * z i : Gf) : Gf ⧸ Kf) = ∑ i, F ((z i : Gf) : Gf ⧸ Kf) := by
  have h := congrArg (fun m => (m.map F).sum) (hz k hk)
  simpa only [Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def] using h

end HeckeFam

section Fix

variable {G Gf : Type} [Group G] [TopologicalSpace G] [Group Gf] [TopologicalSpace Gf]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def infRep (π : UnitaryRep (G × Gf) H) : UnitaryRep G H where
  toHom := π.toHom.comp (MonoidHom.inl G Gf)
  continuous_orbit' v := (π.continuous_orbit v).comp (continuous_id.prodMk continuous_const)

theorem infRep_apply (π : UnitaryRep (G × Gf) H) (g : G) (v : H) : infRep π g v = π (g, 1) v := rfl

def fixSub (π : UnitaryRep (G × Gf) H) (Kf : Subgroup Gf) : Submodule ℂ H where
  carrier := {v | ∀ k ∈ Kf, π (1, k) v = v}
  add_mem' {a b} ha hb k hk := by simp only [Set.mem_setOf_eq, map_add, ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c v hv k hk := by simp only [Set.mem_setOf_eq, map_smul, hv k hk]

variable (π : UnitaryRep (G × Gf) H) (Kf : Subgroup Gf)

theorem mem_fixSub {v : H} : v ∈ fixSub π Kf ↔ ∀ k ∈ Kf, π (1, k) v = v := Iff.rfl

theorem isClosed_fixSub : IsClosed (fixSub π Kf : Set H) := by
  have e : (fixSub π Kf : Set H) = ⋂ k ∈ Kf, {v | π (1, k) v = v} := by
    ext v; simp [mem_fixSub]
  rw [e]
  exact isClosed_biInter fun k _ => isClosed_eq (π (1, k)).continuous continuous_id

instance completeSpace_fixSub : CompleteSpace (fixSub π Kf) := (isClosed_fixSub π Kf).completeSpace_coe

variable {π Kf}

theorem op_fix_congr {v : H} (hv : v ∈ fixSub π Kf) {x y : Gf} (h : (x : Gf ⧸ Kf) = y) :
    π (1, x) v = π (1, y) v := by
  rw [QuotientGroup.eq] at h
  rw [show ((1 : G), y) = (1, x) * (1, x⁻¹ * y) by ext <;> simp, UnitaryRep.map_mul_apply, hv _ h]

theorem heckeVec_mem {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) {v : H} (hv : v ∈ fixSub π Kf) :
    (∑ i, π (1, z i)) v ∈ fixSub π Kf := by
  intro k hk
  let F : Gf ⧸ Kf → H := fun y => π (1, y.out) v
  have hF : ∀ x : Gf, π (1, x) v = F (x : Gf ⧸ Kf) := fun x =>
    op_fix_congr hv (QuotientGroup.out_eq' (x : Gf ⧸ Kf)).symm
  simp only [ContinuousLinearMap.sum_apply, map_sum]
  calc ∑ i, π (1, k) (π (1, z i) v) = ∑ i, F ((k * z i : Gf) : Gf ⧸ Kf) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← UnitaryRep.map_mul_apply, show ((1 : G), k) * (1, z i) = (1, k * z i) by ext <;> simp, hF]
    _ = ∑ i, F ((z i : Gf) : Gf ⧸ Kf) := sum_heckeFam hz F hk
    _ = ∑ i, π (1, z i) v := Finset.sum_congr rfl fun i _ => (hF _).symm

def heckeOp {n : ℕ} {z : Fin n → Gf} (hz : IsHeckeFam Kf z) : fixSub π Kf →L[ℂ] fixSub π Kf :=
  ((∑ i, π (1, z i)).comp (fixSub π Kf).subtypeL).codRestrict (fixSub π Kf) fun v => heckeVec_mem hz v.2

end Fix

end GlobalTheory.Mt.Adelic

namespace GlobalTheory.Mt.Adelic

section Rel

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

section Coch

variable {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M]
  [IsScalarTower ℝ ℂ M]

def postL (Φ : Module.End ℂ M) (q : ℕ) : (P [⋀^Fin q]→ₗ[ℝ] M) →ₗ[ℂ] (P [⋀^Fin q]→ₗ[ℝ] M) where
  toFun f := (Φ.restrictScalars ℝ).compAlternatingMap f
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

theorem postL_apply (Φ : Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) (v : Fin q → P) :
    postL Φ q f v = Φ (f v) := rfl

end Coch

section Smooth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
  (T : H →L[ℂ] H) (hT : ∀ g v, T (π g v) = π g (T v))

include hT in
theorem expOrbit_op (v : H) : D.lie.expOrbit (CartanData.toBanach π) (T v) =
    (T.restrictScalars ℝ) ∘ D.lie.expOrbit (CartanData.toBanach π) v := by
  funext Y
  exact (hT _ v).symm

include hT in
theorem smooth_op {v : H} (hv : v ∈ D.SmV π) : T v ∈ D.SmV π := by
  have hv' : D.lie.IsSmoothVector (CartanData.toBanach π) v := hv
  show D.lie.IsSmoothVector (CartanData.toBanach π) (T v)
  rw [IsExpLieAlgebra.isSmoothVector_iff] at hv' ⊢
  rw [expOrbit_op D π T hT]
  exact (T.restrictScalars ℝ).contDiff.comp hv'

def opS : Module.End ℂ (D.SmV π) :=
  (T : H →ₗ[ℂ] H).restrict fun _ hv => smooth_op D π T hT hv

def opT (d : ℕ) : Module.End ℂ (Fin d → D.SmV π) :=
  LinearMap.pi fun i => (opS D π T hT).comp (LinearMap.proj i)

theorem opT_apply {d : ℕ} (w : Fin d → D.SmV π) (i : Fin d) : opT D π T hT d w i = opS D π T hT (w i) := rfl

variable {d : ℕ} (ξ : G →* Matrix (Fin d) (Fin d) ℂ)

end Smooth

end Rel

end GlobalTheory.Mt.Adelic

namespace GlobalTheory.Mt.Adelic

section Left

variable {Γ₀ Gf : Type} [Group Γ₀] [Group Gf] (ρf : Γ₀ →* Gf) (Kf : Subgroup Gf)

abbrev yAct : MulAction Γ₀ (Gf ⧸ Kf) := MulAction.compHom (Gf ⧸ Kf) ρf

def funRepY {d : ℕ} (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ Γ₀ (Gf ⧸ Kf → Fin d → ℂ) :=
  @funRep Γ₀ _ (Gf ⧸ Kf) (yAct ρf Kf) d ξ₀

theorem funRepY_apply {d : ℕ} (ξ₀ : Γ₀ →* Matrix (Fin d) (Fin d) ℂ) (γ : Γ₀) (φ : Gf ⧸ Kf → Fin d → ℂ) (x : Gf) :
    funRepY ρf Kf ξ₀ γ φ (x : Gf ⧸ Kf) = ξ₀ γ *ᵥ φ ((ρf γ⁻¹ * x : Gf) : Gf ⧸ Kf) := rfl

variable {ρf Kf} {d : ℕ}

end Left

end GlobalTheory.Mt.Adelic

namespace GlobalTheory.Mt.Adelic

end GlobalTheory.Mt.Adelic
