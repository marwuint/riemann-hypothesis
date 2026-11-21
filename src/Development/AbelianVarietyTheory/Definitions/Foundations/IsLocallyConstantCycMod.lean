import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def Sys (W : R2 Ω l) (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) : Prop :=
  (∀ s i j, mat W s i j ∈ c.O) ∧ y ∈ Z1 (Loc.colRep W) ∧ (∀ s i, y s i ∈ c.O) ∧ Unr W y ∧
    ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
      KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ

def NzAt (W : R2 Ω l) (A : ValuationSubring Ω) (y : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∃ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 ∧ mat W s 1 1 = 1 ∧ y s 1 ≠ 0

def Layer (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (r : ℕ)
    (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  (∀ s x, z s x ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
    z (s * t) x = z s x + (ν s : Qbar l) * z t (x * (cycMod ℚ Ω l r s)⁻¹)

def IwSys (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) :
    Prop :=
  (∀ r, Layer c A ν r (Z r)) ∧ ∀ r s (x : (ZMod (l ^ r))ˣ),
    Z r s x = ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), Z (r + 1) s x'

def sp {r : ℕ} (η : (ZMod (l ^ r))ˣ → Qbar l) (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (s : G ℚ Ω) : Qbar l :=
  ∑ x, η x * z s x

def SpLink (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  ∀ n : ℕ, ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
    Cg n (y s 1) (sp (fun x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Z r) s)

theorem not_gr_of_nzAt {W : R2 Ω l} {A : ValuationSubring Ω} {y : G ℚ Ω → Fin 2 → Qbar l} (h : NzAt W A y) : ¬ Gr W A y := by
  rintro ⟨x, hx⟩
  obtain ⟨s, hs, -, h11, hy⟩ := h
  apply hy
  rw [hx s (Ine_le_Dec (F := ℚ) A hs), h11, one_mul, sub_self]

theorem es_of_sys {W : R2 Ω l} {A : ValuationSubring Ω} (h : ∃ c y S', Sys W c y S' ∧ NzAt W A y) : ES W A := by
  obtain ⟨c, y, S', ⟨hW, hy, hyO, hU, hT⟩, hnz⟩ := h
  exact ⟨c, y, S', hW, hy, hyO, hU, not_gr_of_nzAt hnz, hT⟩

def IwSysC (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω →* (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) :
    Prop :=
  IwSys c A ν Z ∧ ∀ r x, ContinuousOn (fun s => Z r s x) (Dec (F := ℚ) A)

namespace IwC

variable {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω →* (Qbar l)ˣ}

theorem smul {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (h : IwSysC c A ν Z) {a : Qbar l} (ha : a ∈ c.O) :
    IwSysC c A ν fun r s x => a * Z r s x := by
  refine ⟨⟨fun r => ⟨fun s x => mul_mem ha ((h.1.1 r).1 s x), fun s hs t ht x => ?_⟩, fun r s x => ?_⟩,
    fun r x => continuousOn_const.mul (h.2 r x)⟩
  · beta_reduce
    rw [(h.1.1 r).2 s hs t ht x]
    ring
  · beta_reduce
    rw [h.1.2 r s x, Finset.mul_sum]

theorem map_cycMod_succ (r : ℕ) (s : G ℚ Ω) :
    Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom (cycMod ℚ Ω l (r + 1) s) =
      cycMod ℚ Ω l r s := by
  ext
  simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow _ _ (Nat.le_succ r)]

private lemma continuous_toZModPow_foundations {l : ℕ} [Fact l.Prime] (r : ℕ) :
    Continuous (PadicInt.toZModPow (p := l) r) := by
  rw [continuous_discrete_rng]
  intro b
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨(l : ℝ) ^ (-(r : ℤ)), zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _, fun y hy => ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [← hx, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

theorem isLocallyConstant_cycMod [IsAlgClosure ℚ Ω] (r : ℕ) : IsLocallyConstant (cycMod ℚ Ω l r) := by
  rw [IsLocallyConstant.iff_continuous]
  exact (Units.continuous_map (continuous_toZModPow_foundations (l := l) r)).comp (continuous_cycZ ℚ Ω l)

end IwC

end GlobalTheory.KZ

end
