import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Ring

variable {S : Type} [CommRing S] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def emb0 (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) : Matrix m m S :=
  1 + V * (x - 1) * P

structure IsFrame (c : S →+* S) (J : Matrix m m S) (K : Matrix n n S) (a : S) (V : Matrix m n S)
    (P : Matrix n m S) : Prop where
  pv : P * V = 1
  jv : J * V = a • (cT c P * K)
  vj : cT c V * J = a • (K * P)

theorem cT_add (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X + Y) = cT c X + cT c Y := by
  ext i j; simp [cT]

theorem cT_sub (c : S →+* S) {p q : Type} (X Y : Matrix p q S) : cT c (X - Y) = cT c X - cT c Y := by
  ext i j; simp [cT]

theorem frame_embedding_one (V : Matrix m n S) (P : Matrix n m S) : emb0 V P 1 = 1 := by simp [emb0]

theorem embed_mul {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) (x y : Matrix n n S) :
    emb0 V P (x * y) = emb0 V P x * emb0 V P y := by
  have e : V * (x - 1) * P * (V * (y - 1) * P) = V * ((x - 1) * (y - 1)) * P := by
    calc V * (x - 1) * P * (V * (y - 1) * P) = V * (x - 1) * (P * V) * (y - 1) * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [emb0, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e]
  have e2 : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by noncomm_ring
  rw [e2]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

def embHom {V : Matrix m n S} {P : Matrix n m S} (h : P * V = 1) : Matrix n n S →* Matrix m m S where
  toFun := emb0 V P
  map_one' := frame_embedding_one V P
  map_mul' := embed_mul h

theorem conj_transpose_frame_embedding (c : S →+* S) (V : Matrix m n S) (P : Matrix n m S) (x : Matrix n n S) :
    cT c (emb0 V P x) = 1 + cT c P * (cT c x - 1) * cT c V := by
  rw [emb0, cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]

theorem frame_embedding_form_defect {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) (x : Matrix n n S) :
    cT c (emb0 V P x) * J * emb0 V P x = J + a • (cT c P * (cT c x * K * x - K) * P) := by
  have hvjv : cT c V * J * V = a • K := by
    rw [h.vj, Matrix.smul_mul, Matrix.mul_assoc, h.pv, Matrix.mul_one]
  set A := x - 1 with hA
  set B := cT c x - 1 with hB
  have hx : x = A + 1 := by rw [hA]; abel
  have hcx : cT c x = B + 1 := by rw [hB]; abel
  have e1 : cT c x * K * x - K = K * A + B * K + B * K * A := by
    rw [hcx, hx]; noncomm_ring
  have t1 : J * (V * A * P) = a • (cT c P * (K * A) * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.jv]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  have t2 : cT c P * B * cT c V * J = a • (cT c P * (B * K) * P) := by
    rw [Matrix.mul_assoc _ (cT c V) J, h.vj]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have t3 : cT c P * B * cT c V * J * (V * A * P) = a • (cT c P * (B * K * A) * P) := by
    calc cT c P * B * cT c V * J * (V * A * P) = cT c P * B * (cT c V * J * V) * A * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hvjv]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [conj_transpose_frame_embedding, ← hB, emb0, ← hA, e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, smul_add]
  rw [t3, t2, t1]
  abel

theorem frame_embedding_unitary {c : S →+* S} {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) {x : Matrix n n S} (hx : cT c x * K * x = K) :
    cT c (emb0 V P x) * J * emb0 V P x = J := by
  rw [frame_embedding_form_defect h, hx]; simp

theorem IsFrame.map {S' : Type} [CommRing S'] {c : S →+* S} {c' : S' →+* S'} (f : S →+* S')
    (hf : ∀ s, f (c s) = c' (f s)) {J : Matrix m m S} {K : Matrix n n S} {a : S} {V : Matrix m n S}
    {P : Matrix n m S} (h : IsFrame c J K a V P) :
    IsFrame c' (J.map f) (K.map f) (f a) (V.map f) (P.map f) := by
  have hc : ∀ {p q : Type} (X : Matrix p q S), cT c' (X.map f) = (cT c X).map f := by
    intro p q X; ext i j; simp [cT, hf]
  have hm : ∀ {p q r : Type} [Fintype q] (X : Matrix p q S) (Y : Matrix q r S),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul (f := f)).symm
  have hs : ∀ {p q : Type} (X : Matrix p q S), f a • X.map f = (a • X).map f := by
    intro p q X; ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, h.pv]; simp [Matrix.map_one]
  · rw [hm, h.jv, hc, hm, hs]
  · rw [hc, hm, h.vj, hm, hs]

end Ring

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
