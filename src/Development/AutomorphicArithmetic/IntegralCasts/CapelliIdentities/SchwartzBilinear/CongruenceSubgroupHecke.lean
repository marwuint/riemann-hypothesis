import Mathlib

namespace UpperTheory.Reformulated.B.P6.CongruenceSubgroupHecke

open scoped DivisionSemiring Semifield Field AddCommGroup DivInvMonoid Group Set DFunLike RingHom Semiring LinearMap MonoidHom MulOneClass Monoid MulZeroOneClass Module.End Membership SetLike Subgroup Units Subtype HSMul SMulZeroClass AddZero AddZeroClass AddMonoid SubNegMonoid AddGroup DistribSMul DistribMulAction Module HAdd AddCommMonoid OfNat Zero Submodule AddSubmonoid AddSubsemigroup One Ring CommRing NonAssocRing NonAssocCommRing Subring DivisionRing NonAssocSemiring Valuation ValuativeRel CommSemiring Classical Ideal Singleton HPow SubmonoidClass Matrix Fin Matrix.GeneralLinearGroup Algebra SubsemiringClass HasQuotient Ideal.Quotient Complex MulZeroClass Pi EquivLike MulEquiv ZPow LE PartialOrder ConditionallyCompletePartialOrderSup ConditionallyCompletePartialOrder ConditionallyCompleteLattice ConditionallyCompleteLinearOrder Int HMul

theorem GlobalTheory.PRep.eig_obl_1 :
    ∀ {k G V : Type} [inst_h0 : Field k] [inst_h1 : Group G] [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V}, Membership.mem (γ := Set V) {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) v} a → Membership.mem (γ := Set V) {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h7 : V) ↦ V) (DFunLike.coe (β := fun (x_h8 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h9 : ↥H) ↦ kˣ) χ h)) v} b → ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h10 : V) ↦ V) (DFunLike.coe (β := fun (x_h11 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) (a + b) = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h12 : ↥H) ↦ kˣ) χ h)) (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  simp only [Set.mem_setOf_eq] at ha hb
  rw [map_add, ha h, hb h, smul_add]

theorem GlobalTheory.PRep.eig_obl_2 :
    ∀ {k G V : Type} [inst_h0 : Field k] [inst_h1 : Group G] [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) (OfNat.ofNat (nat_lit 0)) = HSMul.hSMul (α := k) (β := V) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) (OfNat.ofNat (nat_lit 0)) := by
  intro k G V _ _ _ _ ρ H χ h
  simp

theorem GlobalTheory.PRep.eig_obl_3 :
    ∀ {k G V : Type} [inst_h0 : Field k] [inst_h1 : Group G] [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V}, Membership.mem (γ := Set V) {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) v} v → ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h7 : V) ↦ V) (DFunLike.coe (β := fun (x_h8 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) (c • v) = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h9 : ↥H) ↦ kˣ) χ h)) (c • v) := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  simp only [Set.mem_setOf_eq] at hv
  rw [map_smul, hv h, smul_comm]

noncomputable def GlobalTheory.PRep.eig :
    {k G V : Type} → [inst_h0 : Field k] → [inst_h1 : Group G] → [inst_h2 : AddCommGroup V] → [inst_h3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
  fun {k G V : Type} {inst_h0 : Field k} {inst_h1 : Group G} {inst_h2 : AddCommGroup V} {inst_h3 : _root_.Module k V} (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦ { carrier := {v : V | ∀ (h : ↥H), DFunLike.coe (F := V →ₗ[k] V) (β := fun (x_h4 : V) ↦ V) (DFunLike.coe (β := fun (x_h5 : G) ↦ V →ₗ[k] V) ρ (h.val (p := fun (x : G) ↦ x ∈ H)) : V →ₗ[k] V) v = HSMul.hSMul (α := k) (Units.val (DFunLike.coe (β := fun (x_h6 : ↥H) ↦ kˣ) χ h)) v}, add_mem' := @GlobalTheory.PRep.eig_obl_1 k G V inst_h0 inst_h1 inst_h2 inst_h3 ρ H χ, zero_mem' := GlobalTheory.PRep.eig_obl_2 ρ H χ, smul_mem' := GlobalTheory.PRep.eig_obl_3 ρ H χ }

end UpperTheory.Reformulated.B.P6.CongruenceSubgroupHecke
