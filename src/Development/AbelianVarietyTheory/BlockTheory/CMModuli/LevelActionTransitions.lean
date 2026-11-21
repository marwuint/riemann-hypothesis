import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.OpenModelSections

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Group

variable (D : Datum H)

def nLa (n : ℕ) : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))

theorem mem_nLa {n : ℕ} {x : D.La} : x ∈ nLa D n ↔ ∃ y, x = n • y := by
  simp only [nLa, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, eq_comm]

abbrev LaMod (n : ℕ+) : Type := D.La ⧸ nLa D n

abbrev cls (n : ℕ+) (a : D.La) : LaMod D n := Submodule.Quotient.mk a

theorem cls_eq {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ ∃ y, a = b + (n : ℕ) • y := by
  rw [Submodule.Quotient.eq, mem_nLa]
  exact exists_congr fun y => by rw [sub_eq_iff_eq_add']

def KMax : Subgroup (∀ n : ℕ+, LaMod D n ≃ₗ[𝓞 E] LaMod D n) where
  carrier := {g | (∀ (n m : ℕ+) (a b : D.La), g (n * m) (cls D _ a) = cls D _ b → g n (cls D n a) = cls D n b) ∧
    ∀ (n : ℕ+) (a b a' b' : D.La), g n (cls D n a) = cls D n a' → g n (cls D n b) = cls D n b' →
      D.EF a' b' ≡ D.EF a b [ZMOD (n : ℕ)]}
  one_mem' := by
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · obtain ⟨y, hy⟩ := (cls_eq D).mp h
      exact (cls_eq D).mpr ⟨(m : ℕ) • y, by rw [hy, PNat.mul_coe, mul_smul]⟩
    · obtain ⟨y, rfl⟩ := (cls_eq D).mp ha
      obtain ⟨z, rfl⟩ := (cls_eq D).mp hb
      refine Int.modEq_iff_dvd.mpr ⟨D.EF a' z + D.EF y b' + (n : ℕ) * D.EF y z, ?_⟩
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      ring
  mul_mem' := by
    rintro g g' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (g' (n * m) (cls D _ a))
      change g (n * m) (g' (n * m) (cls D _ a)) = _ at h
      change g n (g' n (cls D _ a)) = _
      rw [h1' n m a c hc.symm]
      exact h1 n m c b (by rw [← h, ← hc])
    · obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (g' n (cls D _ a))
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (g' n (cls D _ b))
      change g n (g' n (cls D _ a)) = _ at ha
      change g n (g' n (cls D _ b)) = _ at hb
      exact (h2 n c d a' b' (by rw [← ha, ← hc]) (by rw [← hb, ← hd])).trans (h2' n a b c d hc.symm hd.symm)
  inv_mem' := by
    rintro g ⟨h1, h2⟩
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · change (g (n * m)).symm (cls D _ a) = _ at h
      change (g n).symm (cls D _ a) = _
      rw [LinearEquiv.symm_apply_eq] at h ⊢
      exact (h1 n m b a h.symm).symm
    · change (g n).symm (cls D _ a) = _ at ha
      change (g n).symm (cls D _ b) = _ at hb
      rw [LinearEquiv.symm_apply_eq] at ha hb
      exact (h2 n a' b' a b ha.symm hb.symm).symm

variable {D}

def modulus (l : Level H) : ℕ+ := ⟨l.M', Nat.lcm_pos (by have := l.three_le; omega) l.A_pos⟩

def Sends (l : Level H) (g : KMax D) (a b : D.La) : Prop :=
  g.1 (modulus l) (cls D _ a) = cls D _ b

def FixesLevel (l : Level H) (g : KMax D) : Prop :=
  ∀ a b, Sends l g a b → a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ∧ a - b ∈ nLa D l.A

theorem exists_sends (l : Level H) (g : KMax D) (a : D.La) : ∃ b, Sends l g a b := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (g.1 (modulus l) (cls D _ a))
  exact ⟨b, hb.symm⟩

end Group

end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
