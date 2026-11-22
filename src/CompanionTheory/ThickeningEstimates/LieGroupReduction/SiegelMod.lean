import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelHaar
import Formalism.SatakeDualWeyl.Statement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Set Matrix
open Formalism.UG (cT cT_mul cT_one)
open scoped NNReal ENNReal Pointwise

namespace CompanionTheory.ThKR.Sieg

variable {R : Type} [CommRing R] {s : R →+* R} {n k : ℕ} {J : Matrix (Fin n) (Fin n) R} {X Y : Matrix (Fin n) (Fin k) R}

section Alg

theorem cT_add {a b : Type} (P Q : Matrix a b R) : cT s (P + Q) = cT s P + cT s Q := Matrix.ext fun _ _ => map_add s _ _

theorem cT_sub {a b : Type} (P Q : Matrix a b R) : cT s (P - Q) = cT s P - cT s Q := Matrix.ext fun _ _ => map_sub s _ _

theorem cT_neg {a b : Type} (P : Matrix a b R) : cT s (-P) = -cT s P := Matrix.ext fun _ _ => map_neg s _

theorem cT_zero {a b : Type} : cT s (0 : Matrix a b R) = 0 := Matrix.ext fun _ _ => map_zero s

theorem cT_smul {a b : Type} (c : R) (P : Matrix a b R) : cT s (c • P) = s c • cT s P :=
  Matrix.ext fun _ _ => map_mul s _ _

variable (s J X Y) in

structure Fr : Prop where
  ss : ∀ x, s (s x) = x
  herm : cT s J = J
  xx : cT s X * J * X = 0
  yy : cT s Y * J * Y = 0
  xy : cT s X * J * Y = 1

theorem Fr.cc (h : Fr s J X Y) {a b : Type} (P : Matrix a b R) : cT s (cT s P) = P := Matrix.ext fun _ _ => h.ss _

theorem Fr.swap (h : Fr s J X Y) {a b : Type} (P : Matrix (Fin n) a R) (Q : Matrix (Fin n) b R) :
    cT s (cT s P * J * Q) = cT s Q * J * P := by
  rw [cT_mul, cT_mul, h.cc, h.herm, Matrix.mul_assoc]

theorem Fr.yx (h : Fr s J X Y) : cT s Y * J * X = 1 := by rw [← h.swap, h.xy, cT_one]

theorem Fr.zero (h : Fr s J X Y) {a b : Type} {P : Matrix (Fin n) a R} {Q : Matrix (Fin n) b R}
    (e : cT s P * J * Q = 0) : cT s Q * J * P = 0 := by rw [← h.swap, e, cT_zero]

theorem gram_unitary {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * J * g = J) {a b : Type} (P : Matrix (Fin n) a R)
    (Q : Matrix (Fin n) b R) : cT s (g * P) * J * (g * Q) = cT s P * J * Q := by
  conv_rhs => rw [← hg]
  simp only [cT_mul, Matrix.mul_assoc]

theorem Fr.par (h : Fr s J X Y) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * J * g = J) {B : Matrix (Fin k) (Fin k) R}
    (hB : g * X = X * B) : cT s Y * J * (g * X) = B ∧ cT s B * (cT s X * J * (g * Y)) = 1 ∧
      cT s X * J * (g * Y) * cT s B = 1 ∧ cT s X * J * g = cT s X * J * (g * Y) * (cT s X * J) := by
  have h1 : cT s B * (cT s X * J * g) = cT s X * J := by
    have := gram_unitary hg X (1 : Matrix (Fin n) (Fin n) R)
    rwa [hB, cT_mul, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s X)] at this
  have h2 : cT s B * (cT s X * J * (g * Y)) = 1 := by
    rw [← Matrix.mul_assoc (cT s X * J), ← Matrix.mul_assoc, h1, h.xy]
  have h3 := mul_eq_one_comm.1 h2
  refine ⟨by rw [hB, ← Matrix.mul_assoc, h.yx, Matrix.one_mul], h2, h3, ?_⟩
  conv_rhs => enter [2]; rw [← h1]
  rw [← Matrix.mul_assoc _ (cT s B), h3, Matrix.one_mul]

theorem Fr.symm (h : Fr s J X Y) : Fr s J Y X := ⟨h.ss, h.herm, h.yy, h.xx, h.yx⟩

theorem Fr.ext (h : Fr s J X Y) {g g' : Matrix (Fin n) (Fin n) R} (h1 : g * X = g' * X) (h2 : g * Y = g' * Y)
    (h3 : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → cT s Y * J * Z = 0 → g * Z = g' * Z) : g = g' := by
  have := h3 (1 - X * (cT s Y * J) - Y * (cT s X * J))
    (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xx, h.xy]; simp)
    (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx]; simp)
  simpa only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h1, h2, Matrix.mul_one, sub_left_inj]
    using this

theorem Fr.comm (h : Fr s J X Y) {l b : Matrix (Fin n) (Fin n) R} (hl : cT s l * J * l = J)
    {B D B' D' : Matrix (Fin k) (Fin k) R} (hB : l * X = X * B) (hD : l * Y = Y * D) (hB' : b * X = X * B')
    (hD' : b * Y = Y * D') (e1 : B * B' = B' * B) (e2 : D * D' = D' * D)
    (hb : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → cT s Y * J * Z = 0 → b * Z = Z) : b * l = l * b := by
  refine h.ext ?_ ?_ fun Z h1 h2 => ?_
  · rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hB', Matrix.mul_assoc l, hB', ← Matrix.mul_assoc l, hB,
      Matrix.mul_assoc, Matrix.mul_assoc, e1]
  · rw [Matrix.mul_assoc, hD, ← Matrix.mul_assoc, hD', Matrix.mul_assoc l, hD', ← Matrix.mul_assoc l, hD,
      Matrix.mul_assoc, Matrix.mul_assoc, e2]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hb Z h1 h2, hb]
    · rw [← Matrix.mul_assoc, (h.par hl hB).2.2.2, Matrix.mul_assoc, h1, Matrix.mul_zero]
    · rw [← Matrix.mul_assoc, (h.symm.par hl hD).2.2.2, Matrix.mul_assoc, h2, Matrix.mul_zero]

variable (s J X) in

def eich (Z : Matrix (Fin n) (Fin k) R) (c : Matrix (Fin k) (Fin k) R) : Matrix (Fin n) (Fin n) R :=
  1 + Z * (cT s X * J) - X * (cT s Z * J) + X * c * (cT s X * J)

theorem Fr.eich_mul_of (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (c : Matrix (Fin k) (Fin k) R) {a : Type}
    {U : Matrix (Fin n) a R} (hU : cT s X * J * U = 0) : eich s J X Z c * U = U - X * (cT s Z * J * U) := by
  simp only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), hU, Matrix.mul_assoc X (cT s Z * J)]
  simp

theorem Fr.eich_X (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s X * J * Z = 0) (c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z c * X = X := by rw [h.eich_mul_of c h.xx, h.zero hZ]; simp

theorem Fr.eich_Y (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s Y * J * Z = 0) (c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z c * Y = Y + Z + X * c := by
  simp only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), h.xy, Matrix.mul_assoc X (cT s Z * J),
    h.zero hZ]
  simp

theorem Fr.eich_mul (h : Fr s J X Y) {Z₀ Z : Matrix (Fin n) (Fin k) R} (h₀ : cT s X * J * Z₀ = 0) (hZ : cT s X * J * Z = 0)
    (c₀ c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z₀ c₀ * eich s J X Z c = eich s J X (Z₀ + Z) (c₀ + c - cT s Z₀ * J * Z) := by
  conv_lhs => rw [show eich s J X Z c = 1 + _ - _ + _ from rfl]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc (eich s J X Z₀ c₀), Matrix.mul_assoc X c,
    h.eich_X h₀, h.eich_mul_of c₀ hZ]
  simp only [eich, cT_add, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem eich_zero : eich s J X 0 0 = 1 := by simp [eich, cT_zero]

variable (s J X Y) in

def W1 : AddSubgroup (Matrix (Fin n) (Fin k) R) where
  carrier := {Z | cT s X * J * Z = 0 ∧ cT s Y * J * Z = 0}
  zero_mem' := by simp
  add_mem' ha hb := ⟨by rw [Matrix.mul_add, ha.1, hb.1, add_zero], by rw [Matrix.mul_add, ha.2, hb.2, add_zero]⟩
  neg_mem' ha := ⟨by rw [Matrix.mul_neg, ha.1, neg_zero], by rw [Matrix.mul_neg, ha.2, neg_zero]⟩

variable (s k) in

def W2 : AddSubgroup (Matrix (Fin k) (Fin k) R) where
  carrier := {c | cT s c = -c}
  zero_mem' := by simp [cT_zero]
  add_mem' {a b} (ha : cT s a = -a) (hb : cT s b = -b) := show cT s _ = _ by rw [cT_add, ha, hb, neg_add]
  neg_mem' {a} (ha : cT s a = -a) := show cT s _ = _ by rw [cT_neg, ha]

variable [Invertible (2 : R)]

theorem s_half : s ⅟2 = ⅟2 := by
  have : s ⅟2 * 2 = 1 := by
    have := congrArg s (invOf_mul_self (2 : R))
    rwa [map_mul, map_one, map_ofNat] at this
  exact (invOf_eq_left_inv this).symm

theorem half_add {a b : Type} (P : Matrix a b R) : (⅟2 : R) • P + (⅟2 : R) • P = P := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

def Fr.β (h : Fr s J X Y) : W1 s J X Y →+ W1 s J X Y →+ W2 s k :=
  AddMonoidHom.mk' (fun Z₀ => AddMonoidHom.mk' (fun Z =>
    ⟨(⅟2 : R) • (cT s Z.1 * J * Z₀.1 - cT s Z₀.1 * J * Z.1), show cT s _ = _ by
      rw [cT_smul, s_half, cT_sub, h.swap, h.swap, ← smul_neg, neg_sub]⟩)
    fun a b => Subtype.ext (by
      simp only [AddSubgroup.coe_add, cT_add, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub]; abel))
    fun a b => AddMonoidHom.ext fun c => Subtype.ext (by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, AddSubgroup.coe_add, cT_add, Matrix.add_mul,
        Matrix.mul_add, smul_add, smul_sub]; abel)

theorem Fr.β_val (h : Fr s J X Y) (Z₀ Z : W1 s J X Y) :
    (h.β Z₀ Z).1 = (⅟2 : R) • (cT s Z.1 * J * Z₀.1 - cT s Z₀.1 * J * Z.1) := rfl

def Fr.nMat (h : Fr s J X Y) : Heis h.β →* Matrix (Fin n) (Fin n) R where
  toFun x := eich s J X x.1.1 (x.2.1 - (⅟2 : R) • (cT s x.1.1 * J * x.1.1))
  map_one' := by
    change eich s J X 0 (0 - (⅟2 : R) • (cT s (0 : Matrix (Fin n) (Fin k) R) * J * 0)) = 1
    simp [eich_zero]
  map_mul' x y := by
    have key : ∀ (Z₀ Z : Matrix (Fin n) (Fin k) R) (c₀ c : Matrix (Fin k) (Fin k) R),
        c₀ + c + (⅟2 : R) • (cT s Z * J * Z₀ - cT s Z₀ * J * Z) - (⅟2 : R) • (cT s (Z₀ + Z) * J * (Z₀ + Z)) =
          c₀ - (⅟2 : R) • (cT s Z₀ * J * Z₀) + (c - (⅟2 : R) • (cT s Z * J * Z)) - cT s Z₀ * J * Z := fun Z₀ Z c₀ c => by
      simp only [cT_add, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub]
      have := half_add (cT s Z₀ * J * Z)
      generalize (⅟2 : R) • (cT s Z₀ * J * Z) = m at this ⊢
      rw [← this]
      abel
    rw [h.eich_mul x.1.2.1 y.1.2.1]
    exact congrArg (eich s J X (x.1.1 + y.1.1)) (key x.1.1 y.1.1 x.2.1 y.2.1)

theorem Fr.nMat_apply (h : Fr s J X Y) (x : Heis h.β) :
    h.nMat x = eich s J X x.1.1 (x.2.1 - (⅟2 : R) • (cT s x.1.1 * J * x.1.1)) := rfl

theorem Fr.decomp_inj (h : Fr s J X Y) {Z Z' : Matrix (Fin n) (Fin k) R} (hZ : cT s Y * J * Z = 0) (hZ' : cT s Y * J * Z' = 0)
    {c c' : Matrix (Fin k) (Fin k) R} (e : Y + Z + X * c = Y + Z' + X * c') : Z = Z' ∧ c = c' := by
  have e1 := congrArg (cT s Y * J * ·) e
  simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, h.yx, hZ, hZ', Matrix.one_mul] at e1
  obtain rfl := add_left_cancel e1
  exact ⟨by simpa using e, rfl⟩

theorem Fr.nMat_inj (h : Fr s J X Y) {x y : Heis h.β} (e : h.nMat x * Y = h.nMat y * Y) : x = y := by
  rw [h.nMat_apply, h.nMat_apply, h.eich_Y x.1.2.2, h.eich_Y y.1.2.2] at e
  obtain ⟨e1, e2⟩ := h.decomp_inj x.1.2.2 y.1.2.2 e
  rw [e1, sub_left_inj] at e2
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

def Fr.pt (h : Fr s J X Y) (W : Matrix (Fin n) (Fin k) R) (h1 : cT s X * J * W = 1) (h2 : cT s W * J * W = 0) : Heis h.β :=
  (⟨W - Y - X * (cT s Y * J * W),
    by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, h1, h.xy, h.xx]; simp,
    by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, h.yy, h.yx]; simp⟩,
   ⟨(⅟2 : R) • (cT s Y * J * W - cT s W * J * Y), show cT s _ = _ by
      rw [cT_smul, s_half, cT_sub, h.swap, h.swap, ← smul_neg, neg_sub]⟩)

theorem Fr.nMat_pt (h : Fr s J X Y) (W : Matrix (Fin n) (Fin k) R) (h1 : cT s X * J * W = 1) (h2 : cT s W * J * W = 0) :
    h.nMat (h.pt W h1 h2) * Y = W := by
  rw [h.nMat_apply, h.eich_Y (h.pt W h1 h2).1.2.2]
  have h3 : cT s W * J * X = 1 := by rw [← h.swap, h1, cT_one]
  have e : cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)) =
      -(cT s Y * J * W) - cT s W * J * Y := by
    rw [cT_sub, cT_sub, cT_mul, h.swap]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc (cT s W * J * Y), ← Matrix.mul_assoc _ X, h1, h2, h3,
      h.xx, h.xy, h.yx, h.yy]
    simp
  change Y + (W - Y - X * (cT s Y * J * W)) + X * ((⅟2 : R) • (cT s Y * J * W - cT s W * J * Y) -
    (⅟2 : R) • (cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)))) = W
  rw [e, ← smul_sub, show cT s Y * J * W - cT s W * J * Y - (-(cT s Y * J * W) - cT s W * J * Y) =
    cT s Y * J * W + cT s Y * J * W by abel, smul_add, half_add]
  abel

end Alg

section Top

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]

instance lcMat (a b : ℕ) : LocallyCompactSpace (Matrix (Fin a) (Fin b) R) :=
  inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → R))

instance scMat (a b : ℕ) : SecondCountableTopology (Matrix (Fin a) (Fin b) R) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → R))

instance scSub {a b : ℕ} (W : AddSubgroup (Matrix (Fin a) (Fin b) R)) : SecondCountableTopology W :=
  TopologicalSpace.Subtype.secondCountableTopology (W : Set (Matrix (Fin a) (Fin b) R))

@[reducible] def msMat (a b : ℕ) : MeasurableSpace (Matrix (Fin a) (Fin b) R) := borel _

attribute [local instance] msMat

local instance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) R) := ⟨rfl⟩

end Top

end CompanionTheory.ThKR.Sieg

end
