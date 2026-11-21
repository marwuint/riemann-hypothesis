import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr4

section

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

theorem free_mul {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

theorem free_add {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

theorem free_sub {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x - y) :=
  fun i j => (hx i j).sub_right (hy i j)

theorem free_neg {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (-x) :=
  fun i j => (hx i j).neg_right

theorem free_smul {c : S} {x : SlopeTestRemainingChoices S A} (k : ℂ) (hx : FreeOf c x) : FreeOf c (k • x) :=
  fun i j => (hx i j).smul_right k

theorem free_pow {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (n : ℕ) : FreeOf c (x ^ n) :=
  fun i j => (hx i j).pow_right n

theorem free_star [StarRing A] {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (star x) := by
  intro i j
  have h := (hx j i).star_star
  rwa [Wd1.star_eU] at h

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext u v
  unfold io
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Wd1.eU_apply]
  split_ifs <;> simp

theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) :=
  fun i j => Wd1.eU_comm_of_ne hc i j k l

theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) : FreeOf2 c (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact free_add (free_mul (hM _ _) (hN _ _)) (free_mul (hM _ _) (hN _ _))

theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ :=
  fun i j => hM j i

theorem freeOf2_matrix_entries {c : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) (hz : FreeOf c z)
    (hw : FreeOf c w) : FreeOf2 c !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hw

theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]; exact free_one c
  · rw [Matrix.one_apply_ne h]; exact free_zero c

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rh0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rht0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j => free_io c (M i j)

end

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem free_l (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.l L Y) :=
  free_add (free_io c _) (free_mul (free_io c _) (h.2.2.2.2.2.2.2.2 Y))

theorem free_d (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.d L) :=
  free_mul (free_pow (free_io c _) _) h.2.2.2.2.2.2.1

theorem free_di (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.di L) :=
  free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io c _) _)

theorem free_m (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.m L Y) :=
  free_mul (free_mul (free_di L h) (free_star (free_l L h _))) (free_d L h)

theorem free_DD {f : FrameData S A} {c : S} (h : f.Free c) (Y Ya : ℂ) : FreeOf c (f.DD Y Ya) :=
  free_smul _ (free_sub (h.2.2.2.2.2.2.2.2 Y) (h.2.2.2.2.2.2.2.2 Ya))

theorem free_tz (L : LevelData A r) (c : S) : FreeOf c (tz L : SlopeTestRemainingChoices S A) := free_io c _

theorem plus_free (L : LevelData A r) {f : FrameData S A} {a c : S} (hc : c ≠ a) (h : f.Free c) (Ya : ℂ) :
    (f.plus L a Ya).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (hTT Ya))
  · exact fun Y => freeOf2_mul (hTT Y) (freeOf2_rmatrix hc _)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_l L h Ya)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_l L h Ya)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (free_add (free_sub (hee Y) (free_DD h Y Ya)) (free_tz L c))
      (free_neg (free_smul _ o)) z (free_mul (free_mul (hxi _) (hee Y)) (hx _)))

theorem minus_free (L : LevelData A r) {f : FrameData S A} {b c : S} (hc : c ≠ b) (h : f.Free c) (Yb : ℂ) :
    (f.minus L b Yb).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (freeOf2_transpose (hTT Yb)))
  · exact fun Y => freeOf2_mul (freeOf2_rmatrix_transpose hc _) (hTT Y)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_m L h Yb)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_m L h Yb)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (hee Y) z (free_neg (free_smul _ (free_mul (hxi _) (hxi _))))
      (free_add (free_sub (free_mul (free_mul (hxi _) (hee Y)) (hx _)) (free_DD h Y Yb)) (free_tz L c)))

theorem start_free (st : Start A) (c : S) : (st.frame : FrameData S A).Free c :=
  ⟨free_one c, fun _ => freeOf2_lift c _, free_one c, free_one c, fun _ => free_io c _, fun _ => free_io c _,
    free_one c, free_one c, fun _ => free_io c _⟩

end

end Formalism.FourierDecayAlt.P.Fr4

namespace Formalism.FourierDecayAlt.P

theorem frame_free_of_new_position : Formalism.FourierDecayAlt.Fr.FrameFree := by
  intro A S _ _ _ _ _ _ r L st w c
  induction w with
  | nil => intro _; exact Fr4.start_free st c
  | cons l w ih =>
    intro hc
    rw [List.map_cons, List.mem_cons, not_or] at hc
    have h := ih hc.2
    show (if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).Free c
    split_ifs
    · exact Fr4.plus_free L hc.1 h l.pt
    · exact Fr4.minus_free L hc.1 h l.pt

end Formalism.FourierDecayAlt.P
