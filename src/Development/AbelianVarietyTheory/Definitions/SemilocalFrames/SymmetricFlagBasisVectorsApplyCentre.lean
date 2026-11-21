import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram

noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

@[simp] theorem ofHSpace_B {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (x y : S.V) : (ofHSpace S).B x y = S.hT y x := rfl

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

def xPlus (F : FlagD H r) : Submodule K V := F.X ⊔ Submodule.span K {F.z}

abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X

def IsTransv (F F' : FlagD H r) : Prop :=
  Module.finrank K (V0 F F') = 2 * r + 2 ∧ Disjoint (V0 F F') (wSp F F')

def norLift (F F' : FlagD H r) : Submodule K V := V0 F F' ⊓ perp H (xPlus F)

def IsComp (F F' : FlagD H r) (u : V) (a a' : K) : Prop := u - a • F.z - a' • F'.z ∈ F.X ⊔ F'.X

def IsSig (F F' : FlagD H r) (y y' : V) (a a' : K) : Prop :=
  y ∈ norLift F F' ∧ y' ∈ norLift F' F ∧ IsComp F F' (y - y') a a'

def IsCong (F F' : FlagD H r) (Λ : Submodule R V) (g : R) : Prop :=
  latX F' Λ ⊔ smulLat g Λ = latX F Λ ⊔ smulLat g Λ ∧ F'.z - F.z ∈ latX F Λ ⊔ smulLat g Λ

def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X

def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ

def fixSp (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Submodule K V where
  carrier := {x | x ∈ wSp F F' ∧ ∃ x'' ∈ wSp F F'', x - x'' ∈ F.X ∧ β x - x'' ∈ F''.X}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha, h1, h2⟩ ⟨hy, b, hb, h3, h4⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem h1 h3
    · rw [map_add, add_sub_add_comm]; exact add_mem h2 h4
  smul_mem' := by
    rintro c x ⟨hx, a, ha, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hx, c • a, Submodule.smul_mem _ c ha, ?_, ?_⟩
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h1
    · rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c h2

theorem B_eq_zero_comm {x y : V} : H.B x y = 0 ↔ H.B y x = 0 :=
  ⟨fun h => by rw [← H.herm, h, star_zero], fun h => by rw [← H.herm, h, star_zero]⟩

theorem perp_anti {S S' : Submodule K V} (h : S ≤ S') : perp H S' ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H S' y).1 hy x (h hx)

theorem perp_sup (S S' : Submodule K V) : perp H (S ⊔ S') = perp H S ⊓ perp H S' := by
  refine le_antisymm (le_inf (perp_anti le_sup_left) (perp_anti le_sup_right)) fun y hy => ?_
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, (mem_perp_iff H _ y).1 hy.1 a ha, (mem_perp_iff H _ y).1 hy.2 b hb, add_zero]

theorem mem_perp_span (s : Set V) (y : V) :
    y ∈ perp H (Submodule.span K s) ↔ ∀ x ∈ s, H.B y x = 0 := by
  rw [mem_perp_iff]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, ha, smul_zero]

theorem X_eq_span (F : FlagD H r) :
    F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  rw [FlagD.X, FlagD.Xa, ← Set.image_univ]
  congr 2
  ext b
  simp

theorem mem_perp_X (F : FlagD H r) (y : V) :
    y ∈ perp H F.X ↔ ∀ a : Fin r, H.B y (F.e a.castSucc) = 0 := by
  rw [X_eq_span, mem_perp_span, Set.forall_mem_range]

theorem X_le_perp (F : FlagD H r) : F.X ≤ perp H F.X := by
  intro x hx
  refine (mem_perp_X F x).2 fun a => B_eq_zero_comm.1 ?_
  exact (mem_perp_iff H _ _).1 ((mem_perp_X F _).2 fun b => F.iso a b) x hx

theorem z_mem_perp (F : FlagD H r) : F.z ∈ perp H F.X :=
  (mem_perp_X F _).2 fun a => B_eq_zero_comm.1 (F.zperp a)

theorem form_flag_vector_self (F : FlagD H r) : H.B F.z F.z = -F.T := F.zz

theorem X_le_xPlus (F : FlagD H r) : F.X ≤ xPlus F := le_sup_left

theorem z_mem_xPlus (F : FlagD H r) : F.z ∈ xPlus F :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem xPlus_eq_span (F : FlagD H r) : xPlus F = Submodule.span K (Set.range F.e) := by
  rw [xPlus, X_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Fin.exists_fin_succ', FlagD.z, eq_comm]

theorem mem_perp_xPlus (F : FlagD H r) (y : V) :
    y ∈ perp H (xPlus F) ↔ y ∈ perp H F.X ∧ H.B y F.z = 0 := by
  rw [xPlus, perp_sup, Submodule.mem_inf, mem_perp_span]
  simp

theorem X_le_perp_xPlus (F : FlagD H r) : F.X ≤ perp H (xPlus F) := fun x hx =>
  (mem_perp_xPlus F x).2 ⟨X_le_perp F hx, B_eq_zero_comm.1 ((mem_perp_iff H _ _).1 (z_mem_perp F) x hx)⟩

theorem eq_zero_of_smul_z_mem (F : FlagD H r) {a : K} (h : a • F.z ∈ F.X) : a = 0 := by
  have h1 := ((mem_perp_xPlus F _).1 (X_le_perp_xPlus F h)).2
  rw [map_smul, LinearMap.smul_apply, form_flag_vector_self, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_right (neg_ne_zero.2 F.hT)

omit [StarRing K] in

theorem mem_imLat (s : V ≃ₗ[K] V) (M : Submodule R V) (x : V) : x ∈ imLat s M ↔ ∃ y ∈ M, s y = x := Iff.rfl

theorem mem_latX (F : FlagD H r) (Λ : Submodule R V) (x : V) : x ∈ latX F Λ ↔ x ∈ Λ ∧ x ∈ F.X := Iff.rfl

theorem mem_redLat (F : FlagD H r) (Λ : Submodule R V) (x : V) :
    x ∈ redLat F Λ ↔ x ∈ perp H F.X ∧ ∃ a ∈ F.X, x + a ∈ Λ := by
  constructor
  · intro h
    obtain ⟨l, hl, a, ha, rfl⟩ := Submodule.mem_sup.1 h
    exact ⟨add_mem hl.2 (X_le_perp F ha), -a, neg_mem ha, by simpa using hl.1⟩
  · rintro ⟨h, a, ha, hl⟩
    exact Submodule.mem_sup.2 ⟨x + a, ⟨hl, add_mem h (X_le_perp F ha)⟩, -a, neg_mem ha, by simp⟩

theorem xPlus_sup (F F' : FlagD H r) : xPlus F ⊔ xPlus F' = V0 F F' := by
  rw [xPlus, xPlus, V0, Submodule.span_insert, sup_sup_sup_comm]

theorem jointSpan_comm (F F' : FlagD H r) : V0 F' F = V0 F F' := by
  rw [← xPlus_sup, ← xPlus_sup, sup_comm]

theorem wSp_comm (F F' : FlagD H r) : wSp F' F = wSp F F' := by rw [wSp, wSp, jointSpan_comm]

theorem wSp_eq (F F' : FlagD H r) : wSp F F' = perp H (xPlus F) ⊓ perp H (xPlus F') := by
  rw [wSp, ← xPlus_sup, perp_sup]

theorem mem_norLift (F F' : FlagD H r) (y : V) :
    y ∈ norLift F F' ↔ y ∈ V0 F F' ∧ y ∈ perp H (xPlus F) := Iff.rfl

theorem norLift_inf (F F' : FlagD H r) : norLift F F' ⊓ norLift F' F = V0 F F' ⊓ wSp F F' := by
  rw [norLift, norLift, wSp_eq, jointSpan_comm F F', inf_inf_inf_comm, inf_idem]

theorem IsTransv.symm {F F' : FlagD H r} (h : IsTransv F F') : IsTransv F' F := by
  rw [IsTransv, jointSpan_comm, wSp_comm]; exact h

theorem IsTransv.disjoint_norLift {F F' : FlagD H r} (h : IsTransv F F') :
    Disjoint (norLift F F') (norLift F' F) := by
  rw [disjoint_iff, norLift_inf]; exact h.2.eq_bot

theorem IsTransv.disjoint_xPlus {F F' : FlagD H r} (h : IsTransv F F') : Disjoint (xPlus F) (xPlus F') := by
  have hf : ∀ G : FlagD H r, Module.Finite K (xPlus G) := fun G => by
    rw [xPlus_eq_span]; exact Module.Finite.span_of_finite K (Set.finite_range _)
  have hd : ∀ G : FlagD H r, Module.finrank K (xPlus G) ≤ r + 1 := fun G => by
    rw [xPlus_eq_span]; exact (finrank_range_le_card (R := K) G.e).trans (by simp)
  have := hf F
  have := hf F'
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (xPlus F) (xPlus F')
  rw [xPlus_sup, h.1] at h1
  have h2 := hd F
  have h3 := hd F'
  have : Module.Finite K ↥(xPlus F ⊓ xPlus F') := Submodule.finiteDimensional_inf_left _ _
  rw [disjoint_iff, ← Submodule.finrank_eq_zero]
  omega

theorem exists_isComp_iff (F F' : FlagD H r) (u : V) : (∃ a a', IsComp F F' u a a') ↔ u ∈ V0 F F' := by
  constructor
  · rintro ⟨a, a', h⟩
    exact Submodule.mem_sup.2 ⟨_, h, a • F.z + a' • F'.z, Submodule.mem_span_pair.2 ⟨a, a', rfl⟩, by abel⟩
  · intro h
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, a', rfl⟩ := Submodule.mem_span_pair.1 hy
    refine ⟨a, a', ?_⟩
    unfold IsComp
    convert hx using 1
    abel

theorem isComp_iff (F F' : FlagD H r) (u : V) (a a' : K) :
    IsComp F F' u a a' ↔ ∃ ξ ∈ F.X, ∃ ξ' ∈ F'.X, u = ξ + a • F.z + ξ' + a' • F'.z := by
  rw [IsComp, Submodule.mem_sup]
  refine exists_congr fun ξ => and_congr_right fun _ => exists_congr fun ξ' => and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [add_right_comm ξ, h]; abel
  · rintro rfl; abel

theorem IsComp.swap {F F' : FlagD H r} {u : V} {a a' : K} (h : IsComp F F' u a a') : IsComp F' F u a' a := by
  rw [IsComp, sub_right_comm, sup_comm]; exact h

theorem IsComp.add {F F' : FlagD H r} {u v : V} {a a' b b' : K} (h : IsComp F F' u a a')
    (k : IsComp F F' v b b') : IsComp F F' (u + v) (a + b) (a' + b') := by
  unfold IsComp at *
  convert add_mem h k using 1
  rw [add_smul, add_smul]; abel

theorem IsComp.smul {F F' : FlagD H r} {u : V} {a a' : K} (h : IsComp F F' u a a') (c : K) :
    IsComp F F' (c • u) (c * a) (c * a') := by
  unfold IsComp at *
  convert Submodule.smul_mem _ c h using 1
  rw [smul_sub, smul_sub, mul_smul, mul_smul]

theorem IsComp.sub {F F' : FlagD H r} {u v : V} {a a' b b' : K} (h : IsComp F F' u a a')
    (k : IsComp F F' v b b') : IsComp F F' (u - v) (a - b) (a' - b') := by
  simpa [sub_eq_add_neg] using h.add (k.smul (-1))

theorem IsComp.unique {F F' : FlagD H r} (hd : Disjoint (xPlus F) (xPlus F')) {u : V} {a a' b b' : K}
    (h : IsComp F F' u a a') (k : IsComp F F' u b b') : a = b ∧ a' = b' := by
  have key : ∀ {G G' : FlagD H r} {c c' : K}, Disjoint (xPlus G) (xPlus G') → IsComp G G' 0 c c' → c = 0 := by
    intro G G' c c' hG hc
    obtain ⟨ξ, hξ, ξ', hξ', e⟩ := (isComp_iff _ _ _ _ _).1 hc
    have h1 : ξ + c • G.z ∈ xPlus G := add_mem (X_le_xPlus G hξ) (Submodule.smul_mem _ c (z_mem_xPlus G))
    have h2 : ξ + c • G.z ∈ xPlus G' := by
      rw [add_assoc (ξ + c • G.z)] at e
      rw [eq_neg_of_add_eq_zero_left e.symm]
      exact neg_mem (add_mem (X_le_xPlus G' hξ') (Submodule.smul_mem _ c' (z_mem_xPlus G')))
    have h3 := Submodule.disjoint_def.1 hG _ h1 h2
    refine eq_zero_of_smul_z_mem G ?_
    rw [eq_neg_of_add_eq_zero_right h3]
    exact neg_mem hξ
  have h0 := h.sub k
  rw [sub_self] at h0
  exact ⟨sub_eq_zero.1 (key hd h0), sub_eq_zero.1 (key hd.symm h0.swap)⟩

theorem exists_isSig {F F' : FlagD H r} {y y' : V} (hy : y ∈ norLift F F') (hy' : y' ∈ norLift F' F) :
    ∃ a a', IsSig F F' y y' a a' := by
  obtain ⟨a, a', h⟩ := (exists_isComp_iff F F' (y - y')).2 (sub_mem hy.1 (jointSpan_comm F F' ▸ hy'.1))
  exact ⟨a, a', hy, hy', h⟩

theorem IsSig.unique {F F' : FlagD H r} (hd : Disjoint (xPlus F) (xPlus F')) {y y' : V} {a a' b b' : K}
    (h : IsSig F F' y y' a a') (k : IsSig F F' y y' b b') : a = b ∧ a' = b' := h.2.2.unique hd k.2.2

theorem IsSig.smul {F F' : FlagD H r} {y y' : V} {a a' : K} (h : IsSig F F' y y' a a') (c : K) :
    IsSig F F' (c • y) (c • y') (c * a) (c * a') :=
  ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, by rw [← smul_sub]; exact h.2.2.smul c⟩

theorem IsCong.refl (F : FlagD H r) (Λ : Submodule R V) (g : R) : IsCong F F Λ g := ⟨rfl, by simp⟩

theorem IsCong.symm {F F' : FlagD H r} {Λ : Submodule R V} {g : R} (h : IsCong F F' Λ g) : IsCong F' F Λ g :=
  ⟨h.1.symm, by rw [h.1, ← neg_sub]; exact neg_mem h.2⟩

theorem IsCong.trans {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} (h : IsCong F F' Λ g)
    (k : IsCong F' F'' Λ g) : IsCong F F'' Λ g :=
  ⟨k.1.trans h.1, by rw [← sub_add_sub_cancel _ F'.z]; exact add_mem (h.1.le k.2) h.2⟩

section Pair

variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

theorem IsPairMap.mem_X_iff (h : IsPairMap F F' F'' Λ g β) (x : V) : β x ∈ F''.X ↔ x ∈ F'.X := by
  rw [← h.1]; simp

theorem IsPairMap.mem_perp_iff (h : IsPairMap F F' F'' Λ g β) (x : V) :
    β x ∈ perp H F''.X ↔ x ∈ perp H F'.X := by
  rw [← h.2.1]; simp

theorem IsPairMap.mem_redLat_iff (h : IsPairMap F F' F'' Λ g β) (x : V) :
    β x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ := by
  rw [← h.2.2.2.1, mem_imLat]
  exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem isPairMap_of_mem_iff (h1 : ∀ x, β x ∈ F''.X ↔ x ∈ F'.X)
    (h2 : ∀ x, β x ∈ perp H F''.X ↔ x ∈ perp H F'.X)
    (h3 : ∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y)
    (h4 : ∀ x, β x ∈ redLat F'' Λ ↔ x ∈ redLat F' Λ) (h5 : β F'.z - F''.z ∈ F''.X)
    (h6 : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
      l'' - l' ∈ latX F Λ ⊔ smulLat g Λ) : IsPairMap F F' F'' Λ g β := by
  have k : ∀ {S S' : Submodule K V}, (∀ x, β x ∈ S' ↔ x ∈ S) → S.map (β : V →ₗ[K] V) = S' := by
    intro S S' hS
    ext y
    obtain ⟨x, rfl⟩ := β.surjective y
    rw [hS]; simp
  refine ⟨k h1, k h2, h3, ?_, h5, h6⟩
  ext y
  obtain ⟨x, rfl⟩ := β.surjective y
  rw [h4, mem_imLat]
  exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem IsPairMap.symm (h : IsPairMap F F' F'' Λ g β) : IsPairMap F F'' F' Λ g β.symm := by
  refine isPairMap_of_mem_iff (fun x => by rw [← h.mem_X_iff]; simp) (fun x => by rw [← h.mem_perp_iff]; simp)
    (fun x hx y hy => ?_) (fun x => by rw [← h.mem_redLat_iff]; simp) ?_ fun l hl l' hl' e => ?_
  · rw [← h.2.2.1 _ (by rw [← h.mem_perp_iff]; simpa using hx) _ (by rw [← h.mem_perp_iff]; simpa using hy)]
    simp
  · rw [← h.mem_X_iff, map_sub, β.apply_symm_apply, ← neg_sub]
    exact neg_mem h.2.2.2.2.1
  · rw [← h.mem_X_iff, map_sub, β.apply_symm_apply, ← neg_sub, neg_mem_iff] at e
    rw [← neg_sub]
    exact neg_mem (h.2.2.2.2.2 l' hl' l hl e)

theorem isPairMap_of_aut (hc : IsCong F F'' Λ g) (hβ : β ∈ isomGrp H) (hΛ : imLat β Λ = Λ)
    (hX : F'.X.map (β : V →ₗ[K] V) = F''.X) (hz : β F'.z - F''.z ∈ F''.X)
    (hι : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), β l' - l' ∈ latX F Λ ⊔ smulLat g Λ) :
    IsPairMap F F' F'' Λ g β := by
  have hB := (mem_isomGrp H β).1 hβ
  have k0 : ∀ x, β x ∈ Λ ↔ x ∈ Λ := fun x => by
    conv_lhs => rw [← hΛ, mem_imLat]
    exact ⟨fun ⟨y, hy, e⟩ => β.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have k1 : ∀ x, β x ∈ F''.X ↔ x ∈ F'.X := fun x => by rw [← hX]; simp
  have k2 : ∀ x, β x ∈ perp H F''.X ↔ x ∈ perp H F'.X := fun x => by
    rw [mem_perp_iff, mem_perp_iff, β.surjective.forall]
    simp only [k1, hB]
  refine isPairMap_of_mem_iff k1 k2 (fun x _ y _ => hB x y) (fun x => ?_) hz fun l hl l' hl' e => ?_
  · rw [mem_redLat, mem_redLat, k2, β.surjective.exists]
    simp only [k1, ← map_add, k0]
  · have h1 : β l - l' ∈ latX F Λ ⊔ smulLat g Λ :=
      hc.1 ▸ Submodule.mem_sup_left ⟨sub_mem ((k0 l).2 hl.1) hl'.1, e⟩
    simpa using sub_mem (hι l hl) h1

theorem isPairMap_refl (hc : IsCong F F' Λ g) : IsPairMap F F' F' Λ g (LinearEquiv.refl K V) :=
  isPairMap_of_aut hc ((mem_isomGrp H _).2 fun _ _ => rfl) (by ext x; simp [mem_imLat]) (by simp) (by simp)
    (by simp)

theorem fixSp_le (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : fixSp F F' F'' β ≤ wSp F F' := fun _ h => h.1

theorem IsPairMap.fixSp_sup_X (h : IsPairMap F F' F'' Λ g β) :
    fixSp F F'' F' β.symm ⊔ F.X = fixSp F F' F'' β ⊔ F.X := by
  have key : ∀ {G G' : FlagD H r} {γ : V ≃ₗ[K] V}, IsPairMap F G G' Λ g γ →
      fixSp F G G' γ ⊔ F.X ≤ fixSp F G' G γ.symm ⊔ F.X := by
    intro G G' γ k
    refine sup_le ?_ le_sup_right
    rintro x ⟨hx, y, hy, h1, h2⟩
    refine Submodule.mem_sup.2 ⟨y, ⟨hy, x, hx, by rw [← neg_sub]; exact neg_mem h1, ?_⟩, x - y, h1, by simp⟩
    rw [← k.mem_X_iff, map_sub, γ.apply_symm_apply, ← neg_sub]
    exact neg_mem h2
  exact le_antisymm (key h.symm) (key h)

end Pair

namespace FlagExample

open NumberField Formalism.BasicNotions.Examples₂

variable (E : Type) [Field E] [NumberField E] [StarRing E]

abbrev sp : HermSpace E (wittSpace E 2 1).V := ofHSpace (wittSpace E 2 1)

def vec (v : Fin 5 → ℤ) : (wittSpace E 2 1).V := (fun i => (v i : E) : Fin 5 → E)

def co (x : (wittSpace E 2 1).V) : Fin 5 → E := x

theorem sp_B (x y : (wittSpace E 2 1).V) : (sp E).B x y =
    -(star (co E y 0) * co E x 0) - star (co E y 1) * co E x 1 + star (co E y 2) * co E x 2 +
      star (co E y 3) * co E x 3 + star (co E y 4) * co E x 4 := by
  show ∑ i : Fin 5, star (co E y i) * sgn (wittSigns 2 1 i) * co E x i = _
  have h0 : wittSigns 2 1 (0 : Fin 5) = true := rfl
  have h1 : wittSigns 2 1 (1 : Fin 5) = true := rfl
  have h2 : wittSigns 2 1 (2 : Fin 5) = false := rfl
  have h3 : wittSigns 2 1 (3 : Fin 5) = false := rfl
  have h4 : wittSigns 2 1 (4 : Fin 5) = false := rfl
  rw [Fin.sum_univ_five, h0, h1, h2, h3, h4]
  simp only [sgn, if_true, Bool.false_eq_true, if_false]
  ring

theorem sp_B_vec (v w : Fin 5 → ℤ) : (sp E).B (vec E v) (vec E w) =
    ((-(w 0 * v 0) - w 1 * v 1 + w 2 * v 2 + w 3 * v 3 + w 4 * v 4 : ℤ) : E) := by
  rw [sp_B]; simp [co, vec]

def fl (m s : ℤ) (h1 : m * m = m) (h2 : s * s = m) : FlagD (sp E) 1 where
  e := ![vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m], vec E ![0, 1 + 2 * m, 0, 2 * s, -2 * m]]
  T := 1
  indep := by
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h (2 : Fin 5)
    have h0 : ((1 : ℤ) : E) = 0 := this
    simp at h0
  iso := by
    intro b c
    rw [Subsingleton.elim b 0, Subsingleton.elim c 0]
    refine (sp_B_vec E _ _).trans (Int.cast_eq_zero.2 ?_)
    simp; linarith
  zperp := by
    intro b
    rw [Subsingleton.elim b 0]
    refine (sp_B_vec E _ _).trans (Int.cast_eq_zero.2 ?_)
    simp; linarith
  zz := by
    refine (sp_B_vec E _ _).trans (Eq.trans (congrArg _ (?_ : _ = (-1 : ℤ))) (by simp))
    simp; linarith
  hT := one_ne_zero

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

theorem symmetricFlagBasisVectors_apply_centre : (fl E m s h1 h2).z = vec E ![0, 1 + 2 * m, 0, 2 * s, -2 * m] := rfl

end FlagExample

end GlobalTheory.SA

end
