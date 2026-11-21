import Mathlib
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex

open MeasureTheory Matrix Finset ValuativeRel
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open scoped Classical

section Levels

variable {O : Type} [CommRing O] [IsLocalRing O]

abbrev red {m n : Type} (A : Matrix m n O) : Matrix m n (IsLocalRing.ResidueField O) :=
  A.map (IsLocalRing.residue O)

def princ (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Subgroup (GL n O) :=
  (Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)).ker

theorem isUnit_of_red {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n O)
    (h : IsUnit (red A)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  have e : (red A).det = IsLocalRing.residue O A.det := (RingHom.map_det _ _).symm
  rw [e] at h
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h.ne_zero

theorem red_mul {l m n : Type} [Fintype m] (A : Matrix l m O) (B : Matrix m n O) :
    red (A * B) = red A * red B := by
  exact Matrix.map_mul

theorem exists_mem_of_red {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n O)}
    (hJ : princ O n ≤ J) {k : GL n O} (hk : k ∈ J) {A : Matrix n n O}
    (h : red A = red (k : Matrix n n O)) : ∃ k' ∈ J, (k' : Matrix n n O) = A := by
  have hred1 : red (((k⁻¹ : GL n O) : Matrix n n O) * A) = 1 := by
    rw [red_mul, h, ← red_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    ext i j
    simp [red, Matrix.one_apply]
  have hu : IsUnit (((k⁻¹ : GL n O) : Matrix n n O) * A) := isUnit_of_red _ (by rw [hred1]; exact isUnit_one)
  have hup : hu.unit ∈ princ O n := by
    rw [princ, MonoidHom.mem_ker]
    ext1
    simpa using hred1
  refine ⟨k * hu.unit, J.mul_mem hk (hJ hup), ?_⟩
  simp [← Matrix.mul_assoc]

end Levels

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def resCard (F : Type) [Field F] [ValuativeRel F] : ℝ := (Nat.card 𝓀[F] : ℝ)

def unitIn (u : 𝒪[F]ˣ) : Fˣ := Units.map (𝒪[F].subtype : 𝒪[F] →* F) u

def entries {m n : Type} (A : Matrix m n 𝒪[F]) : m → n → F := fun i j => (A i j : F)

def groupSet {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝒪[F])) : Set (n → n → F) :=
  {x | ∃ k ∈ H, entries k.val = x}

variable [MeasurableSpace F]

def volAdd (ν : Measure F) (m n : Type) [Fintype m] [Fintype n] : Measure (m → n → F) :=
  Measure.pi fun _ : m => Measure.pi fun _ : n => ν

def volGroup (ν : Measure F) {n : Type} [Fintype n] [DecidableEq n] (H : Subgroup (GL n 𝒪[F])) : ℝ :=
  (volAdd ν n n).real (groupSet H)

def VolumeOfGL (ν : Measure F) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n],
    volGroup ν (⊤ : Subgroup (GL n 𝒪[F])) = qE (resCard F) 1 (Fintype.card n)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex
