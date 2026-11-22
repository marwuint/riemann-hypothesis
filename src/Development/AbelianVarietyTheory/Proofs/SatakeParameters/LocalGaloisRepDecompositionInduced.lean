import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.PstLine

section Letter

variable {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* End LL D)
  (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) {M : Type} [AddCommGroup M] [Module F M]

def letterLift (q : D →+ M) (h1 : ∀ (a : LL) x, q (a • x) = algebraMap LL F a • q x)
    (h2 : ∀ c x, q (m c x) = τ c • q x) : Letter m F τ →ₗ[F] M :=
  letI : Module LL M := Module.compHom M (algebraMap LL F)
  haveI : IsScalarTower LL F M := ⟨fun a b x => by
    show (a • b) • x = algebraMap LL F a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let q' : D →ₗ[LL] M := { toFun := q, map_add' := map_add q, map_smul' := h1 }
  Submodule.liftQ (letterKer m F τ) (q'.liftBaseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul z x =>
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.baseChange_tmul,
        LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.liftBaseChange_tmul]
      show z • q (m c x) - τ c • z • q x = 0
      rw [h2, smul_comm, sub_self]
    | add y z hy hz => rw [map_add]; exact add_mem hy hz)

@[simp] theorem letterLift_mk (q : D →+ M) (h1 : ∀ (a : LL) x, q (a • x) = algebraMap LL F a • q x)
    (h2 : ∀ c x, q (m c x) = τ c • q x) (x : D) :
    letterLift m F τ q h1 h2 (letterMk m F τ x) = q x := by
  show (1 : F) • q x = q x
  rw [one_smul]

end Letter

section St

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V')

def stMap : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := f.rTensor (Bst P)

@[simp] theorem stMap_tmul (v : V) (b : Bst P) : stMap P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem stMap_smul {a : ↥L.1} {a' : ↥L'.1} (h : ∀ x, f (a • x) = a' • f x) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (a • x) = a' • stMap P f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [smul_tmul', stMap_tmul, h, stMap_tmul, smul_tmul']
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

variable {f ρ ρ'}

theorem stMap_stRep (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (stRep P ρ g x) = stRep P ρ' g (stMap P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [he]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem stMap_mem_Dpst (he : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρ) :
    stMap P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← stMap_stRep P he, hx g hg]⟩

def dMap (he : ∀ g x, f (ρ g x) = ρ' g (f x)) : ↥(Dpst P ρ) →+ ↥(Dpst P ρ') where
  toFun x := ⟨stMap P f x, stMap_mem_Dpst P he x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_dMap (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (x : ↥(Dpst P ρ)) :
    (dMap P he x : V' ⊗[ℚ_[l]] Bst P) = stMap P f x := rfl

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x))

include he

end St

section Fun

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

structure IsMor (hL : L.1 ≤ L'.1) (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V)
    (ρ' : Representation ↥L'.1 ↥(GK K) V') : Prop where
  smul : ∀ (a : ↥L.1) x, f (a • x) = IntermediateField.inclusion hL a • f x
  equiv : ∀ g x, f (ρ g x) = ρ' g (f x)

variable {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ')

end Fun

section Model

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1) (m : ℕ) (r : ↥Gw →* GL (Fin m) ↥L.1)

def incV : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L'.1) :=
  (IntermediateField.inclusion hL).toLinearMap.compLeft (Fin m)

abbrev upRep : ↥Gw →* GL (Fin m) ↥L'.1 := mapRep (IntermediateField.inclusion hL).toRingHom r

theorem isMor_incV : IsMor hL (incV hL m) (Bw.repE L r) (Bw.repE L' (upRep hL m r)) where
  smul a x := funext fun i => map_mul (IntermediateField.inclusion hL) a (x i)
  equiv g x := funext fun i => by
    exact RingHom.map_mulVec (IntermediateField.inclusion hL).toRingHom _ x i

end Model

end GlobalTheory.PstLine
