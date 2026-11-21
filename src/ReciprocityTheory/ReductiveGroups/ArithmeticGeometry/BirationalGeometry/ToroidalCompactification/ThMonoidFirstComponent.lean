import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

variable (A U) in

@[ext] structure Th where

  x : A

  f : A → U

instance : Monoid (Th A U) where
  mul g h := ⟨g.x * h.x, fun y => g.f y * h.f (y * g.x)⟩
  one := ⟨1, fun _ => 1⟩
  mul_assoc g h k := Th.ext (_root_.mul_assoc _ _ _) (funext fun y => by
    show g.f y * h.f (y * g.x) * k.f (y * (g.x * h.x)) = g.f y * (h.f (y * g.x) * k.f (y * g.x * h.x))
    rw [_root_.mul_assoc, _root_.mul_assoc y])
  one_mul g := Th.ext (_root_.one_mul _) (funext fun y => by show 1 * g.f (y * 1) = _; rw [_root_.one_mul, _root_.mul_one])
  mul_one g := Th.ext (_root_.mul_one _) (funext fun y => _root_.mul_one _)

theorem Th.adapted_frame_mul_vecMulVec (g h : Th A U) : (g * h).x = g.x * h.x := rfl
theorem Th.mul_f (g h : Th A U) (y : A) : (g * h).f y = g.f y * h.f (y * g.x) := rfl

theorem Th.theta_pow_x (g : Th A U) (n : ℕ) : (g ^ n).x = g.x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, Th.adapted_frame_mul_vecMulVec, ih]

theorem Th.pow_f (g : Th A U) (n : ℕ) (y : A) : (g ^ n).f y = ∏ j ∈ Finset.range n, g.f (y * g.x ^ j) := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, Th.mul_f, ih, Th.theta_pow_x, Finset.prod_range_succ]

structure Th.Sym (ν : A → U) (N : ℕ) (g : Th A U) : Prop where
  pow : g ^ N = 1
  sym : ∀ y, g.f (y * g.x⁻¹) * ν y * g.f y⁻¹ = ν (y * g.x⁻¹)

variable {ν ν' : A → U} {N : ℕ} {g h : Th A U}

theorem Th.Sym.of_dvd {N' : ℕ} (s : g.Sym ν N) (d : N ∣ N') : g.Sym ν N' := ⟨by obtain ⟨r, rfl⟩ := d; rw [pow_mul, s.pow, one_pow], s.sym⟩

theorem Th.Sym.mul (s : g.Sym ν N) (t : h.Sym ν N) (c : Commute g h) : (g * h).Sym ν N := by
  refine ⟨by rw [c.mul_pow, s.pow, t.pow, _root_.mul_one], fun y => ?_⟩
  have a₁ := congrArg Additive.ofMul (s.sym y)
  have a₂ := congrArg Additive.ofMul (t.sym (y * g.x⁻¹))
  have a₃ := congrArg (fun q : Th A U => Additive.ofMul (q.f (y * g.x⁻¹ * h.x⁻¹))) c.eq
  have e₁ : y * (g.x * h.x)⁻¹ = y * g.x⁻¹ * h.x⁻¹ := by rw [mul_inv, _root_.mul_assoc]
  have e₂ : (y * g.x⁻¹)⁻¹ = y⁻¹ * g.x := by rw [mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [Th.mul_f, Th.adapted_frame_mul_vecMulVec, e₁, e₂, inv_mul_cancel_right, ofMul_mul] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃

theorem Th.Sym.unique (hN : Odd N) (s : g.Sym ν N) (t : h.Sym ν N) (ex : g.x = h.x) {c : U} (e : ∀ y, g.f y = c * h.f y) :
    g = h := by
  have p : c ^ N = 1 := by
    have a := congrArg (fun q : Th A U => q.f 1) s.pow
    have b := congrArg (fun q : Th A U => q.f 1) t.pow
    simp only [Th.pow_f, e, ex, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at a b
    rw [b] at a; exact (_root_.mul_one _).symm.trans a
  have q : c ^ 2 = 1 := by
    have a := congrArg Additive.ofMul (s.sym 1)
    have b := congrArg Additive.ofMul (t.sym 1)
    apply Additive.ofMul.injective
    simp only [e, ex, ofMul_mul, ofMul_pow, ofMul_one] at a b ⊢
    linear_combination (norm := abel) a - b
  obtain ⟨m, rfl⟩ := hN
  rw [pow_succ, pow_mul, q, one_pow, _root_.one_mul] at p
  exact Th.ext ex (funext fun y => by rw [e, p, _root_.one_mul])

def Th.pull (f : A →* A) (δ : A → U) (x : A) (g : Th A U) : Th A U := ⟨x, fun y => δ y * g.f (f y) * (δ (y * x))⁻¹⟩

theorem Th.Sym.pull (s : g.Sym ν N) (f : A →* A) (δ : A → U) {x : A} (hx : f x = g.x) (hN : x ^ N = 1) {κ : U}
    (hν : ∀ y, ν' y = κ * (δ y * (δ y⁻¹)⁻¹ * ν (f y))) : (g.pull f δ x).Sym ν' N := by
  have tel : ∀ n y, ((g.pull f δ x) ^ n).f y = δ y * (g ^ n).f (f y) * (δ (y * x ^ n))⁻¹ := fun n y => by
    induction n with
    | zero => rw [pow_zero, pow_zero, pow_zero, _root_.mul_one]; show 1 = δ y * 1 * _; simp
    | succ n ih =>
      rw [pow_succ, pow_succ g, Th.mul_f, Th.mul_f, ih, Th.theta_pow_x, Th.theta_pow_x, pow_succ, ← _root_.mul_assoc y, ← hx, ← map_pow,
        ← map_mul]
      apply Additive.ofMul.injective
      simp only [Th.pull, ofMul_mul, ofMul_inv]
      abel
  refine ⟨Th.ext ((Th.theta_pow_x _ _).trans hN) (funext fun y => ?_), fun y => ?_⟩
  · rw [tel, s.pow, hN, _root_.mul_one]; show δ y * 1 * _ = 1; simp
  · have a := congrArg Additive.ofMul (s.sym (f y))
    have e₂ : (y * x⁻¹)⁻¹ = y⁻¹ * x := by rw [mul_inv, inv_inv]
    apply Additive.ofMul.injective
    simp only [Th.pull, hν, e₂, inv_mul_cancel_right, map_mul, map_inv, hx, ofMul_mul, ofMul_inv] at a ⊢
    linear_combination (norm := abel) a

end Alg

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {T T' : Over S} (σ : T' ⟶ T) (z : T'.left)
  (J : (T'.left ⟶ A.left) → L.L.ι)

def IsGeo (k : ℕ) (x : T ⟶ A) (g : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ) : Prop :=
  g.x = σ ≫ x ∧ ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L.L φ ε)),
    u.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (snd T A).left ^ k * (h ((fst T A ≫ x) * snd T A).left ^ k)⁻¹) ∧ ∀ y, val u (lift σ y).left z J = g.f y

variable {σ z J} (hJ : Good L.L z J) {k : ℕ} {x x' : T ⟶ A} {g g' : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ}
include hJ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
