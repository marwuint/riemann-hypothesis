import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

def intSub (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by simpa using IntAt.coe P 1
  add_mem' := IntAt.add
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom (P : HeightOneSpectrum (𝓞 E)) : intSub P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by simpa using reduction_coe P 0
  map_add' a b := reduction_add a.2 b.2

theorem redHom_apply (P : HeightOneSpectrum (𝓞 E)) (a : intSub P) : redHom P a = redP P a.1 := rfl

variable [StarRing E]

theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem eN_mem (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt]
  intro j
  unfold Loc.eN
  split_ifs
  · simpa using IntAt.coe P 1
  · simpa using IntAt.coe P 0

theorem intAt_entry (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) (i j : ℕ) : IntAt P (Loc.atN (g (Loc.eN E N j)) i) := by
  have hg' : ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P := hg
  have hm : g (Loc.eN E N j) ∈ stdAt E N P := (hg' _).2 (eN_mem P N j)
  rw [mem_stdAt] at hm
  unfold Loc.atN
  split_ifs with h
  · exact hm _
  · simpa using IntAt.coe P 0

def blockD (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P) :=
  Matrix.of fun s t => ⟨Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1), intAt_entry P hg _ _⟩

theorem redP_det_block (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) :
    redP P (Matrix.det (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1))) =
      ((redHom P).mapMatrix (blockD P kj n hg)).det := by
  have h1 : (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1)) =
      (intSub P).subtype.mapMatrix (blockD P kj n hg) := by
    ext s t
    rfl
  rw [h1, ← RingHom.map_det, ← RingHom.map_det]
  rfl

end GlobalTheory.TwistRowType
