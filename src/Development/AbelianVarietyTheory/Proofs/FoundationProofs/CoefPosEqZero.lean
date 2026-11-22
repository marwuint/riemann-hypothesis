import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UnitPiece

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in

theorem sum_antidiag (n : ℕ) (G : ℤ → ℤ → K) :
    ∑ q ∈ (n : ℤ).divisorsAntidiag, G q.1 q.2 =
      ∑ d ∈ n.divisors, (G ((n / d : ℕ) : ℤ) d + G (-((n / d : ℕ) : ℤ)) (-(d : ℤ))) := by
  rw [Int.divisorsAntidiag_natCast, sum_disjUnion, sum_map, sum_map, ← sum_add_distrib]
  exact Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => G a b + G (-(a : ℤ)) (-(b : ℤ)))

theorem coefPos_eq (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) :
    coefPos j M ζ a₁ a₂ n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if q.1 ≡ a₁ [ZMOD M] then (q.2.sign : K) * ((q.1 : K) / M) ^ (j - 1) * ζ ^ (a₂ * q.2) else 0 := by
  rw [sum_antidiag n (fun A d => if A ≡ a₁ [ZMOD M] then (d.sign : K) * ((A : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0)]
  unfold coefPos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0, sub_eq_add_neg]
  congr 1
  · split_ifs <;> simp [-Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]
  · split_ifs <;> simp [neg_div, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

def primeTo (p m : ℕ) [NeZero p] : Finset (ZMod (p ^ m)) := univ.filter fun c => ¬ p ∣ c.val

omit [CharZero K] in

theorem sum_unitSet (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m))
    (H : ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ γ ∈ unitSet p m, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det.val : ℕ) : ZMod (p ^ m)) *
      H ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1)
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b := by
  have e : ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b =
      ∑ w ∈ primeTo p m ×ˢ ((univ : Finset (ZMod (p ^ m))) ×ˢ (primeTo p m ×ˢ (univ : Finset (ZMod (p ^ m))))),
        ψ (w.1 * w.2.2.2 - w.2.1 * w.2.2.1) * H w.1 w.2.1 w.2.2.1 w.2.2.2 := by
    simp only [sum_product]
  rw [e]
  refine sum_of_injOn (fun γ : GL (Fin 2) (ZMod (p ^ m)) =>
    ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1,
     (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1)) ?_ ?_ ?_ ?_
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  · intro γ hγ
    simpa [unitSet, primeTo] using hγ
  · rintro ⟨u, a, v, b⟩ hw hn
    by_cases hu : IsUnit (u * b - a * v)
    · exfalso
      apply hn
      refine ⟨Matrix.GeneralLinearGroup.mk'' !![u, a; v, b] (by simpa [Matrix.det_fin_two] using hu), ?_, ?_⟩
      · simpa [unitSet, primeTo] using hw
      · simp
    · simp only
      rw [MulChar.map_nonunit _ hu, zero_mul]
  · intro γ _
    simp only [ZMod.natCast_zmod_val, Matrix.det_fin_two]

theorem dvd_val_iff (p m : ℕ) [NeZero p] (hm : 1 ≤ m) (z : ℤ) :
    p ∣ (z : ZMod (p ^ m)).val ↔ (p : ℤ) ∣ z := by
  rw [← Int.natCast_dvd_natCast, ZMod.val_intCast]
  have h : (p : ℤ) ∣ ((p ^ m : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by omega)
  rw [Int.emod_def]
  exact dvd_sub_left (h.mul_right _)

theorem col_sum (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (y₁ y₂ n₁ n₂ d d' : ℤ)
    (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₁ * d)) *
          (ψ⁻¹ (d' : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₂ * d')) else 0 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : 0 < N * p ^ m := Nat.mul_pos hN (pow_pos hp.pos m)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have hζN : IsPrimitiveRoot (ζ ^ N) (p ^ m) := hζ.pow hpos rfl
  have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self _ (by omega)
  have hunit : ∀ z : ℤ, IsUnit (z : ZMod (p ^ m)) ↔ ¬ (p : ℤ) ∣ z := by
    intro z
    rw [← dvd_val_iff p m hm, ← ZMod.natCast_zmod_val (z : ZMod (p ^ m)), ZMod.isUnit_iff_coprime,
      Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd, ZMod.natCast_zmod_val]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.KummerEisensteinGalois.ChSum.charSum p m K ψ (ζ ^ N) hm hψ hζN n₁ n₂ d d' (fun h => h₁ h.1)
  have e : ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      (∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
        (ζ ^ N) ^ ((a.val : ℤ) * d + (b.val : ℤ) * d')) *
        ((ζ ^ (p ^ m)) ^ (y₁ * d) * (ζ ^ (p ^ m)) ^ (y₂ * d')) := by
    simp only [sum_mul]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm a, mul_assoc, mul_assoc, ← zpow_natCast ζ N, ← zpow_natCast ζ (p ^ m), ← zpow_mul, ← zpow_mul,
      ← zpow_mul, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0]
    congr 2
    push_cast; ring
  rw [e]
  obtain ⟨w, hw⟩ := (hunit n₁).mpr h₁
  split_ifs with hc
  · obtain ⟨hs, -, hd'⟩ := hc
    obtain ⟨v, hv⟩ := (hunit d').mpr hd'
    rw [hdvd] at hs
    push_cast at hs
    rw [← hw, ← hv] at hs
    have hww : ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * w = 1 := w.inv_mul
    rw [c1 (v * w⁻¹) ?_ ?_]
    · have : ψ⁻¹ ((v * w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) = ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (d' : ZMod (p ^ m)) := by
        rw [Units.val_mul, map_mul, ← hw, ← hv, mul_comm]
        congr 1
        rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
      rw [this]; ring
    · rw [Units.val_mul]
      linear_combination ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * hs - (d : ZMod (p ^ m)) * hww
    · rw [Units.val_mul, ← hw, ← hv]
      linear_combination (-(v : ZMod (p ^ m))) * hww
  · rw [c2, zero_mul]
    rintro ⟨u, hd, hd'⟩
    apply hc
    refine ⟨?_, ?_, ?_⟩
    · rw [hdvd]; push_cast; rw [hd, hd']; ring
    · rw [← hunit, hd]; exact u.isUnit.mul ((hunit n₂).mpr h₂).neg
    · rw [← hunit, hd']; exact u.isUnit.mul ((hunit n₁).mpr h₁)

omit [CharZero K] in

theorem sum_affine (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (u c : ZMod (p ^ m)) (hu : IsUnit u) : ∑ b : ZMod (p ^ m), ψ (u * b + c) = 0 := by
  have hp : p.Prime := Fact.out
  have hne : ψ ≠ 1 := by
    intro h
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hψ
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne hψ
  obtain ⟨w, rfl⟩ := hu
  rw [← MulChar.sum_eq_zero_of_ne_one hne]
  exact Equiv.sum_comp ((Units.mulLeft w).trans (Equiv.addRight c)) ψ

theorem isUnit_of_mem (p m : ℕ) [Fact p.Prime] {u : ZMod (p ^ m)} (hu : u ∈ primeTo p m) : IsUnit u := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.natCast_zmod_val u, ZMod.isUnit_iff_coprime]
  exact ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hu).2).symm).pow_right m

omit [CharZero K] in

theorem sum_zero_left (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → K) (g : ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u * g v b) = 0 := by
  refine sum_eq_zero fun u _ => ?_
  rw [sum_comm]
  refine sum_eq_zero fun v hv => ?_
  rw [sum_comm]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_mul, ← zero_mul (f u * g v b), ← sum_affine p m hm ψ hψ (-v) (u * b) (isUnit_of_mem p m hv).neg]
  congr 1
  exact sum_congr rfl fun a _ => by congr 1; ring

omit [CharZero K] in

theorem sum_zero_right (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → ZMod (p ^ m) → K) (g : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u a * g v) = 0 := by
  refine sum_eq_zero fun u hu => sum_eq_zero fun a _ => sum_eq_zero fun v _ => ?_
  rw [← sum_mul, ← zero_mul (f u a * g v), ← sum_affine p m hm ψ hψ u (-(a * v)) (isUnit_of_mem p m hu)]
  simp only [sub_eq_add_neg]

end GlobalTheory.KummerEisensteinGalois.UnitPiece
