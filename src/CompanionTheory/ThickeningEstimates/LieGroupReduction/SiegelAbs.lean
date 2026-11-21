import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelCore
import CompanionTheory.ThickeningEstimates.SiegelDomainEstimates.LeHeightOfIsTorusElt

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open CompanionTheory.ThKEst (rId)
open CompanionTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd rId_inf)

namespace CompanionTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (F E) in

def rIdU [IsTotallyReal F] (c : ℝ) : (AF F ⊗[F] E)ˣ where
  val := algebraMap (AF F) (AF F ⊗[F] E) (rId F c)
  inv := algebraMap (AF F) (AF F ⊗[F] E) (rId F (-c))
  val_inv := by rw [← map_mul, ← rId_add, add_neg_cancel, rId_zero', map_one]
  inv_val := by rw [← map_mul, ← rId_add, neg_add_cancel, rId_zero', map_one]

theorem val_rIdU [IsTotallyReal F] (c : ℝ) :
    (rIdU F E c : AF F ⊗[F] E) = algebraMap (AF F) (AF F ⊗[F] E) (rId F c) := rfl

theorem inv_rIdU [IsTotallyReal F] (c : ℝ) :
    (↑(rIdU F E c)⁻¹ : AF F ⊗[F] E) = algebraMap (AF F) (AF F ⊗[F] E) (rId F (-c)) := rfl

variable (σ) in
theorem sigRA_sigRA (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, sigma_sigma h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigRA_inclR (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR {a b : Type} (P : Matrix a b E) :
    (Formalism.UG.cT (σ : E →+* E) P).map (inclR (F := F) (AF F)) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (P.map (inclR (F := F) (AF F))) :=
  Matrix.ext fun i j => by simp [cT, sigRA_inclR]

structure PFr {R : Type} [CommRing R] (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R) (Xm Ym : Matrix (Fin n) (Fin r) R) :
    Prop where
  ss : ∀ x, s (s x) = x
  herm : cT s Jm = Jm
  xx : cT s Xm * Jm * Xm = 0
  yy : cT s Ym * Jm * Ym = 0
  xy : cT s Xm * Jm * Ym = 1

section PFr

variable {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R} {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem PFr.cc (hF : PFr s Jm Xm Ym) {a b : Type} (P : Matrix a b R) : cT s (cT s P) = P :=
  Matrix.ext fun _ _ => hF.ss _

theorem PFr.yx (hF : PFr s Jm Xm Ym) : cT s Ym * Jm * Xm = 1 := by
  have := congrArg (cT s) hF.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hF.cc, hF.herm, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

theorem pgram_unitary {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm) {a b : Type}
    (P : Matrix (Fin n) a R) (Q : Matrix (Fin n) b R) : cT s (g * P) * Jm * (g * Q) = cT s P * Jm * Q := by
  conv_rhs => rw [← hg]
  simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem PFr.inv_coef (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {B : Matrix (Fin r) (Fin r) R} (hB : g * Xm = Xm * B) : cT s (cT s Xm * Jm * (g * Ym)) * B = 1 := by
  have h2 : cT s B * (cT s Xm * Jm * (g * Ym)) = 1 := by
    rw [← hF.xy, ← pgram_unitary hg Xm Ym, hB, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  have := congrArg (cT s) h2
  rwa [Formalism.UG.cT_mul, hF.cc, Formalism.UG.cT_one] at this

def coefM (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R) (Xm Ym : Matrix (Fin n) (Fin r) R) (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin r) (Fin r) R :=
  cT s Ym * Jm * (g * Xm)

end PFr

theorem pfrA (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y) := by
  refine ⟨sigRA_sigRA σ h, ?_, ?_, ?_, ?_⟩
  · have e : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    unfold JR
    rw [← cT_map_inclR, e]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

theorem unitaryA_matHom (p : GAd σ J) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (matHom _ σ J p).1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J * (matHom _ σ J p).1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J :=
  (show ↥(HR (AF F) σ J) from p).2

variable (σ J X Y) in

def Bm (p : GAd σ J) : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
  coefM (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y)
    (matHom _ σ J p).1

section Bm

variable (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y))
include hF

theorem Bm_eq {p : GAd σ J} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (e : (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * B) : Bm σ J X Y p = B := by
  rw [Bm, coefM, e, ← Matrix.mul_assoc, hF.yx, Matrix.one_mul]

theorem mem_minPar_iff {p : GAd σ J} : p ∈ minPar σ J X ↔
    (Bm σ J X Y p).BlockTriangular id ∧ (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * Bm σ J X Y p := by
  constructor
  · rintro ⟨B, hB, e⟩
    rw [Bm_eq hF e]
    exact ⟨hB, e⟩
  · rintro ⟨hB, e⟩
    exact ⟨_, hB, e⟩

theorem Bm_mul {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) :
    Bm σ J X Y (p * q) = Bm σ J X Y p * Bm σ J X Y q := by
  have ep := ((mem_minPar_iff hF).1 hp).2
  have eq := ((mem_minPar_iff hF).1 hq).2
  apply Bm_eq hF
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, eq, ← Matrix.mul_assoc, ep, Matrix.mul_assoc]

theorem Bm_one : Bm σ J X Y (1 : GAd σ J) = 1 :=
  Bm_eq hF (by rw [map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])

end Bm

theorem diag_mul_bt {R : Type} [CommRing R] {B C : Matrix (Fin r) (Fin r) R} (hB : B.BlockTriangular id)
    (hC : C.BlockTriangular id) (i : Fin r) : (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hl | hl
    · rw [hB hl, zero_mul]
    · rw [hC hl, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem mul_mem_minimal_parabolic {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) :
    p * q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  obtain ⟨C, hC, e'⟩ := hq
  refine ⟨B * C, hB.mul hC, ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Matrix.mul_assoc]

theorem inv_mem_minimal_parabolic (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  obtain ⟨Q, h3⟩ : ∃ Q, Q * B = 1 := ⟨_, (pfrA h hJ hW).inv_coef (unitaryA_matHom p) e⟩
  have h4 : B * Q = 1 := mul_eq_one_comm.1 h3
  haveI : Invertible B := ⟨Q, h3, h4⟩
  have hinv : B⁻¹ = Q := Matrix.inv_eq_left_inv h3
  refine ⟨Q, by rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular hB, ?_⟩
  have e2 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  calc (matHom _ σ J p⁻¹).1 * GlobalTheory.SiegelSet.adMat F X = (matHom _ σ J p⁻¹).1 * (GlobalTheory.SiegelSet.adMat F X * (B * Q)) := by
        rw [h4, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X * Q := by
        rw [← Matrix.mul_assoc (GlobalTheory.SiegelSet.adMat F X), ← e]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.SiegelSet.adMat F X * Q := by rw [e2, Matrix.one_mul]

variable (σ J X Y) in

def uU (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J} (hp : p ∈ minPar σ J X)
    (hp' : p⁻¹ ∈ minPar σ J X) (i : Fin r) : (AF F ⊗[F] E)ˣ where
  val := Bm σ J X Y p i i
  inv := Bm σ J X Y p⁻¹ i i
  val_inv := by
    have hF := pfrA h hJ hW
    rw [← diag_mul_bt ((mem_minPar_iff hF).1 hp).1 ((mem_minPar_iff hF).1 hp').1, ← Bm_mul hF hp hp',
      mul_inv_cancel, Bm_one hF, Matrix.one_apply_eq]
  inv_val := by
    have hF := pfrA h hJ hW
    rw [← diag_mul_bt ((mem_minPar_iff hF).1 hp').1 ((mem_minPar_iff hF).1 hp).1, ← Bm_mul hF hp' hp,
      inv_mul_cancel, Bm_one hF, Matrix.one_apply_eq]

theorem val_uU (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (hp' : p⁻¹ ∈ minPar σ J X) (i : Fin r) :
    (uU σ J X Y h hJ hW hp hp' i : AF F ⊗[F] E) = Bm σ J X Y p i i := rfl

variable (σ J X Y) in

def uP (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (P : Subgroup (GAd σ J))
    (hP : ∀ p, p ∈ P ↔ p ∈ minPar σ J X) (p : P) (i : Fin r) : (AF F ⊗[F] E)ˣ :=
  uU σ J X Y h hJ hW ((hP _).1 p.2) ((hP _).1 (P.inv_mem p.2)) i

theorem val_uP (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (P : Subgroup (GAd σ J))
    (hP : ∀ p, p ∈ P ↔ p ∈ minPar σ J X) (p : P) (i : Fin r) :
    (uP σ J X Y h hJ hW P hP p i : AF F ⊗[F] E) = Bm σ J X Y p.1 i i := rfl

end CompanionTheory.ThKR

end
