import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankLeFinrankInfPerpXPlus

noncomputable section

namespace GlobalTheory.IntPair

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Module

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

def SameRed (F' F'' : FlagD H r) (β β₁ : V ≃ₗ[K] V) : Prop := ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X

def RedMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) : Type :=
  Quot fun β β₁ : {β : V ≃ₗ[K] V // IsPairMap F F' F'' Λ g β} => SameRed F' F'' β.1 β₁.1

abbrev AutRed (F : FlagD H r) (Λ : Submodule R V) : Type := RedMap F F F Λ 1

def corank (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : ℕ :=
  finrank K (↥(perp H (xPlus F)) ⧸ (fixSp F F' F'' β ⊔ F.X).submoduleOf (perp H (xPlus F)))

def IsScalar (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Prop :=
  IsTransv F F' ∧ IsTransv F F'' ∧ corank F F' F'' β = 1 ∧
    ∀ y y' a a', IsSig F F' y y' a a' → IsSig F F'' y (β y') a a'

def Carry (s : V ≃ₗ[K] V) (F F₁ : FlagD H r) : Prop :=
  s ∈ isomGrp H ∧ (∀ x, s x ∈ F₁.X ↔ x ∈ F.X) ∧ s F.z - F₁.z ∈ F₁.X

structure Moves (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) (G' G'' : FlagD H r) (β₁ s₁ s₂ : V ≃ₗ[K] V) : Prop where
  base₁ : Carry s₁ F F
  base₂ : Carry s₂ F F
  fst : Carry s₁ F' G'
  snd : Carry s₂ F'' G''
  agree : SameRed F F s₂ s₁
  comm : SameRed F' G'' (β.trans s₂) (s₁.trans β₁)

variable {F F' F'' F₁ G' G'' : FlagD H r} {Λ Λ₁ : Submodule R V} {g : R} {β β₁ s s₁ s₂ : V ≃ₗ[K] V}

namespace RedMap

def mk (β : V ≃ₗ[K] V) (h : IsPairMap F F' F'' Λ g β) : RedMap F F' F'' Λ g := Quot.mk _ ⟨β, h⟩

end RedMap

instance (F : FlagD H r) (Λ : Submodule R V) : Nonempty (AutRed F Λ) :=
  ⟨RedMap.mk _ (isPairMap_refl (IsCong.refl F Λ 1))⟩

theorem fixSp_sup_le (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : fixSp F F' F'' β ⊔ F.X ≤ perp H (xPlus F) :=
  sup_le ((fixSp_le _ _ _ _).trans ((wSp_eq F F').le.trans inf_le_left)) (X_le_perp_xPlus F)

variable [FiniteDimensional K V]

theorem corank_add (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) :
    corank F F' F'' β + finrank K ↥(fixSp F F' F'' β ⊔ F.X) = finrank K (perp H (xPlus F)) := by
  rw [corank, ← (Submodule.submoduleOfEquivOfLe (fixSp_sup_le F F' F'' β)).finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

theorem corank_symm (h : IsPairMap F F' F'' Λ g β) : corank F F'' F' β.symm = corank F F' F'' β := by
  have a := corank_add F F' F'' β
  have b := corank_add F F'' F' β.symm
  rw [h.fixSp_sup_X] at b
  omega

theorem IsScalar.symm (h : IsScalar F F' F'' β) (hp : IsPairMap F F' F'' Λ g β) : IsScalar F F'' F' β.symm := by
  have key {G G₁ : FlagD H r} {A B : FlagD H r} (h1 : IsTransv A G) (h2 : IsTransv B G₁) (t : V ≃ₗ[K] V)
      (h3 : ∀ y ∈ norLift A G, t y ∈ norLift B G₁) (y : V) (hy : t y ∈ norLift B G₁) : y ∈ norLift A G := by
    have : (norLift A G).map (t : V →ₗ[K] V) = norLift B G₁ :=
      Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h3 y hy) (by
        rw [LinearEquiv.finrank_map_eq, (norLift_decomp K V H r _ _ h1).1, (norLift_decomp K V H r _ _ h2).1])
    rw [← this] at hy
    simpa using hy
  refine ⟨h.2.1, h.1, (corank_symm hp).trans h.2.2.1, fun y y' a a' k => ?_⟩
  obtain ⟨y', rfl⟩ := β.surjective y'
  have h1 : y ∈ norLift F F' := key h.1 h.2.1 (LinearEquiv.refl K V) (fun y hy => by
    obtain ⟨b, b', e⟩ := exists_isSig hy (zero_mem _)
    exact (h.2.2.2 _ _ _ _ e).1) y k.1
  have h2 : y' ∈ norLift F' F := key h.1.symm h.2.1.symm β (fun y hy => by
    obtain ⟨b, b', e⟩ := exists_isSig (zero_mem _) hy
    exact (h.2.2.2 _ _ _ _ e).2.1) y' k.2.1
  obtain ⟨b, b', e⟩ := exists_isSig h1 h2
  obtain ⟨rfl, rfl⟩ := (h.2.2.2 _ _ _ _ e).unique h.2.1.disjoint_xPlus k
  simpa using e

omit [FiniteDimensional K V]

namespace Carry

theorem refl (F : FlagD H r) : Carry (LinearEquiv.refl K V) F F :=
  ⟨(mem_isomGrp H _).2 fun _ _ => rfl, fun _ => Iff.rfl, by simp⟩

theorem symm (h : Carry s F F₁) : Carry s.symm F₁ F := by
  refine ⟨inv_mem h.1, fun x => by rw [← h.2.1]; simp, ?_⟩
  rw [← h.2.1, map_sub, s.apply_symm_apply, ← neg_sub]
  exact neg_mem h.2.2

theorem perp_iff (h : Carry s F F₁) {A B : Submodule K V} (e : ∀ x, s x ∈ B ↔ x ∈ A) (x : V) :
    s x ∈ perp H B ↔ x ∈ perp H A := by
  rw [mem_perp_iff, mem_perp_iff, s.surjective.forall]
  simp only [e, (mem_isomGrp H s).1 h.1]

theorem perp (h : Carry s F F₁) (x : V) : s x ∈ perp H F₁.X ↔ x ∈ perp H F.X := h.perp_iff h.2.1 x

end Carry

namespace Moves

variable (h : Moves F F' F'' β G' G'' β₁ s₁ s₂)
include h

theorem symm : Moves F G' G'' β₁ F' F'' β s₁.symm s₂.symm := by
  refine ⟨h.base₁.symm, h.base₂.symm, h.fst.symm, h.snd.symm, s₁.surjective.forall.2 fun x hx => ?_,
    s₁.surjective.forall.2 fun x hx => ?_⟩
  · rw [← h.base₂.2.1, ← neg_mem_iff]
    simpa using h.agree x ((h.base₁.perp x).1 hx)
  · rw [← h.snd.2.1, ← neg_mem_iff]
    simpa using h.comm x ((h.fst.perp x).1 hx)

end Moves

end GlobalTheory.IntPair

end
