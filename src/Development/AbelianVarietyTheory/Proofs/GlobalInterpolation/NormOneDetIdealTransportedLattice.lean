import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ScalarCharacterTwist
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LiesOverSpanOfNatCastMemHeightOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne

open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke

section Pull

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E')

theorem map_osmul (c : 𝓞 E) (a : E) : e (c • a) = RingOfIntegers.mapRingEquiv e c • e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def pull (I : Submodule (𝓞 E') E') : Submodule (𝓞 E) E where
  carrier := {x | e x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show e (a + b) ∈ I
    rw [map_add]; exact add_mem ha hb
  smul_mem' := fun c a ha => by
    show e (c • a) ∈ I
    rw [map_osmul]
    exact I.smul_mem _ ha

theorem mem_pull (I : Submodule (𝓞 E') E') (x : E) : x ∈ pull e I ↔ e x ∈ I := Iff.rfl

theorem pull_one : pull e 1 = 1 := by
  ext x
  rw [mem_pull, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.symm r, by rw [← e.symm_apply_apply x, ← hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem pull_norm (c : E → E) (c' : E' → E') (h : ∀ x, e (c x) = c' (e x)) {I : Submodule (𝓞 E') E'}
    (hI : ∃ J : Submodule (𝓞 E') E', (∀ x, x ∈ J ↔ c' x ∈ I) ∧ I * J = 1) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ c x ∈ pull e I) ∧ pull e I * J = 1 := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨pull e J, fun x => by rw [mem_pull, mem_pull, hJ, h], le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [← pull_one e, mem_pull, map_mul, ← hIJ]
    exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.one_le]
    have h1 : ∀ z ∈ I * J, e.symm z ∈ pull e I * pull e J := by
      intro z hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add]; exact add_mem ha hb
      rw [map_mul]
      exact Submodule.mul_mem_mul (by simpa [mem_pull] using ha) (by simpa [mem_pull] using hb)
    simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)

def pushP (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E') :=
  HeightOneSpectrum.comap (RingOfIntegers.mapRingEquiv e.symm : 𝓞 E' →+* 𝓞 E) (RingOfIntegers.mapRingEquiv e.symm).surjective P

end Pull

section Vp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Vp

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {χ : TaylorLogMetric.IdE D → ℂ}

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ (fun i => s.iE.symm (y i)) ∈ N := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      exact map_zero _
    | add a b _ _ ha hb =>
      convert N.add_mem ha hb using 1
      funext i
      exact map_add _ _ _
    | smul c a _ ha =>
      convert N.smul_mem (RingOfIntegers.mapRingEquiv s.iE.symm c) ha using 1
      funext i
      exact map_osmul s.iE.symm c (a i)
  · intro hy
    exact Submodule.subset_span ⟨_, hy, funext fun i => s.iE.apply_symm_apply _⟩

theorem detId_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = pull s.iE.symm (detI N) := by
  apply le_antisymm
  · rw [TaylorLogMetric.detId, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨A.map s.iE.symm, fun v hv => ?_, (s.iE.symm : D.host.E →+* X.E).map_det A⟩
    have h1 := (mem_lat s N _).1 (hA (fun i => s.iE (v i)) fun i _ => by
      have := hv i (Set.mem_univ _)
      rw [← pull_one s.iE] at this
      exact this)
    convert h1 using 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · have : detI N ≤ pull s.iE (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
      rw [detI, Submodule.span_le]
      rintro _ ⟨A, hA, rfl⟩
      refine Submodule.subset_span ⟨A.map s.iE, fun v hv => (mem_lat s N _).2 ?_, (s.iE : X.E →+* D.host.E).map_det A⟩
      have h1 := hA (fun i => s.iE.symm (v i)) fun i _ => by
        have := hv i (Set.mem_univ _)
        rw [← pull_one s.iE.symm] at this
        exact this
      convert h1 using 1
      funext i
      simp [Matrix.mulVec, dotProduct]
    intro y hy
    simpa [mem_pull] using this hy

variable {s}

theorem normOne_idealPreimageUnderRingEquiv (hs : s.Ok) {I : Submodule (𝓞 X.E) X.E} (h : NormOne I) : TaylorLogMetric.N1 D (pull s.iE.symm I) :=
  pull_norm s.iE.symm D.host.conj star (fun x => by rw [RingEquiv.symm_apply_eq, hs.2, s.iE.apply_symm_apply]) h

theorem normOne_detIdeal_transportedLattice (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  rw [detId_lat]
  exact normOne_idealPreimageUnderRingEquiv hs (normOne_detI hN)

end Chi

section Parts

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}

theorem T_mem (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ P.asIdeal := by
  rw [← hZ.primes.piT_norm u]
  exact Ideal.mul_mem_right _ _ (decoFin_mem_of_mem_divs hP)

end Parts

end GlobalTheory.CharValCompare
