import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

noncomputable section

namespace GlobalTheory.GLp.Model

open Polynomial GlobalTheory.GLq GlobalTheory.GLp
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem red_surjective (n : ℕ) : Function.Surjective (red g n) := by
  intro x
  have hs : Function.Surjective (PadicInt.toZMod (p := g)) := ZMod.ringHom_surjective _
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun i j => Function.surjInv hs ((x : Mt g n) i j)
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (x : Mt g n) := by
    ext i j; exact Function.surjInv_eq hs _
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 x.isUnit).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).2 hd).unit, ?_⟩
  ext i j
  exact congrFun (congrFun hM i) j

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero, MonoidHom.mem_ker]

theorem lift_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (k : GL (Fin n) ℤ_[g]) : π (lift g n (red g n k)) v = π (inc g n k) v := by
  have h := Function.invFun_eq (f := red g n) ⟨k, rfl⟩
  have h2 := (mem_principalCongruenceFixedVectors_iff π v).1 hv (k⁻¹ * Function.invFun (red g n) (red g n k)) (by simp [h])
  have : lift g n (red g n k) = inc g n k * inc g n (k⁻¹ * Function.invFun (red g n) (red g n k)) := by
    simp [lift]
  rw [this, map_mul, Module.End.mul_apply, h2]

theorem isIrrRep_iff {G : Type} [Group G] (π : Representation ℂ G V) : IsIrrRep π ↔ π.IsIrreducible := by
  constructor
  · rintro ⟨hn, h⟩
    haveI : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun e => by
      have : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule e
      exact bot_ne_top this⟩
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun x v hv => W.apply_mem_toSubmodule x hv) with e | e
    · left; exact Subrepresentation.toSubmodule_injective e
    · right; exact Subrepresentation.toSubmodule_injective e
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have : (⊥ : Subrepresentation π) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
      exact bot_ne_top this
    · rcases eq_bot_or_eq_top (⟨W, fun x v hv => hW x v hv⟩ : Subrepresentation π) with e | e
      · left; exact congrArg Subrepresentation.toSubmodule e
      · right; exact congrArg Subrepresentation.toSubmodule e

def chRep {G : Type} [Group G] (φ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun x := (φ x : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

@[simp] theorem chRep_apply {G : Type} [Group G] (φ : G →* ℂˣ) (x : G) (v : ℂ) : chRep φ x v = φ x * v := by
  simp [chRep]

theorem isIrrRep_chRep {G : Type} [Group G] (φ : G →* ℂˣ) : IsIrrRep (chRep φ) :=
  ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

def unitPart : ℚ_[g]ˣ →* ℤ_[g]ˣ where
  toFun x := PadicInt.mkUnits (u := (x : ℚ_[g]) * (g : ℚ_[g]) ^ (-(x : ℚ_[g]).valuation)) (by
    have hg : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, norm_zpow, Padic.norm_p, inv_zpow', neg_neg,
      ← zpow_add₀ hg]; simp)
  map_one' := by
    apply Units.ext; apply Subtype.ext; simp
  map_mul' x y := by
    have hg : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
    apply Units.ext; apply Subtype.ext
    simp only [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, Padic.valuation_mul x.ne_zero y.ne_zero,
      neg_add, zpow_add₀ hg]
    ring

def tame (χ : (ZMod g)ˣ →* ℂˣ) : ℚ_[g]ˣ →* ℂˣ :=
  χ.comp ((Units.map (PadicInt.toZMod (p := g)).toMonoidHom).comp unitPart)

def detRep (n : ℕ) (μ : ℚ_[g]ˣ →* ℂˣ) : Representation ℂ (GL (Fin n) ℚ_[g]) ℂ :=
  chRep (μ.comp Matrix.GeneralLinearGroup.det)

theorem exists_gen (L : LabelDatum g) : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 ∧
    orderOf u = g - 1 := by
  have hp : g.Prime := Fact.out
  have ho := L.gen_order 1 one_pos
  rw [pow_one] at ho
  have h1 : L.gen 1 ^ (g - 1) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hpos : 0 < g - 1 := by have := hp.two_le; omega
  have h2 : L.gen 1 ^ g = L.gen 1 := by
    have : L.gen 1 ^ g = L.gen 1 ^ (g - 1 + 1) := by congr 1; omega
    rw [this, pow_succ, h1, one_mul]
  obtain ⟨c, hc⟩ : ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = L.gen 1 := by
    obtain ⟨m, hm⟩ := (mem_bot_iff_intCast g (Formalism.CyclotomicNorms.Fbar g)).1
      ((Subfield.mem_bot_iff_pow_eq_self (Formalism.CyclotomicNorms.Fbar g) g).2 h2)
    exact ⟨m, by simpa using hm⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc] at h1; simp [hpos.ne'] at h1
  refine ⟨Units.mk0 c hc0, hc, ?_⟩
  rw [← ho, ← hc, ← orderOf_units, Units.val_mk0]
  exact (orderOf_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom (algebraMap (ZMod g) _).injective c).symm

theorem isCharLab_exists (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) : ∃ c, IsCharLab L χ c := by
  obtain ⟨u, hu, ho⟩ := exists_gen L
  have hpos : 0 < g - 1 := by have := (Fact.out : g.Prime).two_le; omega
  haveI : NeZero (g - 1) := ⟨hpos.ne'⟩
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have hprim : IsPrimitiveRoot (T u) (g - 1) := by
    rw [← ho, ← orderOf_injective T hT u]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (χ u : ℂ)) (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ho, pow_orderOf_eq_one]; simp)
  refine ⟨(u ^ m : (ZMod g)ˣ), Units.ne_zero _, fun w hw => ?_⟩
  have : w = u := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hw.trans hu.symm))
  rw [this, ← hm, ← map_pow]; rfl

theorem hasLab_monic (L : LabelDatum g) (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X])
    (h : HasLab L π f) : f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
  by_contra hf
  obtain ⟨v, -, hv⟩ := h
  simp [GLq.Model.eSerC_zero L n f hf, actK] at hv

end GlobalTheory.GLp.Model
