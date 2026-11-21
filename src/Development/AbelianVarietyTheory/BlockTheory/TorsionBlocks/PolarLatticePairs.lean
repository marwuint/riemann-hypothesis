import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs

open NumberField IsDedekindDomain Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped Pointwise

theorem mul_entry_mem (D : D7) {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (hB : ∀ i j, B i j ∈ OhE D) (i j : Fin N) : (A * B) i j ∈ OhE D := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

def intPts (D : D7) (N : ℕ) : Subgroup (GA D N) where
  carrier := {g | IntG D (g : GL (Fin N) (AE D))}
  one_mem' := by
    intro i j
    constructor
    · simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
  mul_mem' := by
    intro g h hg hh i j
    constructor
    · rw [Subgroup.coe_mul, Units.val_mul]
      exact mul_entry_mem D (fun i j => (hg i j).1) (fun i j => (hh i j).1) i j
    · rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
      exact mul_entry_mem D (fun i j => (hh i j).2) (fun i j => (hg i j).2) i j
  inv_mem' := by
    intro g hg i j
    constructor
    · rw [Subgroup.coe_inv]; exact (hg i j).2
    · rw [Subgroup.coe_inv, inv_inv]; exact (hg i j).1

def idHat (D : D7) (𝔮 : Ideal (𝓞 D.host.E)) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ b ∈ 𝔮, ∃ s ∈ OhE D, y = inc D (b : D.host.E) * s}

theorem idHat_mul (D : D7) {𝔮 : Ideal (𝓞 D.host.E)} {y r : AE D} (hy : y ∈ idHat D 𝔮) (hr : r ∈ OhE D) :
    y * r ∈ idHat D 𝔮 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨b, hb, s, hs, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨b, hb, s * r, Subring.mul_mem _ hs hr, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | add x y _ _ h₁ h₂ => rw [add_mul]; exact AddSubgroup.add_mem _ h₁ h₂
  | neg x _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h

def BlockMod (D : D7) {N : ℕ} (𝔮 : Ideal (𝓞 D.host.E)) (I : Finset (Fin N))
    (A : Matrix (Fin N) (Fin N) (AE D)) : Prop :=
  ∀ i ∉ I, ∀ j ∈ I, A i j ∈ idHat D 𝔮

theorem BlockMod.mul (D : D7) {N : ℕ} {𝔮 : Ideal (𝓞 D.host.E)} {I : Finset (Fin N)}
    {A B : Matrix (Fin N) (Fin N) (AE D)} (hA : ∀ i j, A i j ∈ OhE D) (hB : ∀ i j, B i j ∈ OhE D)
    (h₁ : BlockMod D 𝔮 I A) (h₂ : BlockMod D 𝔮 I B) : BlockMod D 𝔮 I (A * B) := by
  intro i hi j hj
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun l _ => ?_
  by_cases hl : l ∈ I
  · exact idHat_mul D (h₁ i hi l hl) (hB l j)
  · rw [mul_comm]; exact idHat_mul D (h₂ l hl j hj) (hA i l)

theorem BlockMod.one (D : D7) {N : ℕ} (𝔮 : Ideal (𝓞 D.host.E)) (I : Finset (Fin N)) :
    BlockMod D 𝔮 I 1 := by
  intro i hi j hj
  have : i ≠ j := fun h => hi (h ▸ hj)
  rw [Matrix.one_apply_ne this]
  exact AddSubgroup.zero_mem _

def levelJ (D : D7) {N : ℕ} (𝔮 : Ideal (𝓞 D.host.E)) (I : Finset (Fin N)) : Subgroup (GA D N) where
  carrier := {h | h ∈ intPts D N ∧
    BlockMod D 𝔮 I ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) ∧
    BlockMod D 𝔮 I (((h : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))}
  one_mem' := ⟨one_mem _, by simpa using BlockMod.one D 𝔮 I, by simpa using BlockMod.one D 𝔮 I⟩
  mul_mem' := by
    rintro g h ⟨hg, g₁, g₂⟩ ⟨hh, h₁, h₂⟩
    refine ⟨mul_mem hg hh, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul]
      exact BlockMod.mul D (fun i j => (hg i j).1) (fun i j => (hh i j).1) g₁ h₁
    · rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
      exact BlockMod.mul D (fun i j => (hh i j).2) (fun i j => (hg i j).2) h₂ g₂
  inv_mem' := by
    rintro g ⟨hg, g₁, g₂⟩
    refine ⟨inv_mem hg, ?_, ?_⟩
    · rw [Subgroup.coe_inv]; exact g₂
    · rw [Subgroup.coe_inv, inv_inv]; exact g₁

abbrev RowSet (a d : ℕ) : Type := {s : Finset (Fin d) // s.card = a}

def coefLat (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ c ∈ cc, ∃ m ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    t = ((c : D.host.K) : D.host.E) * m}

def matIn (D : D7) (a d : ℕ) (A : Submodule (𝓞 D.host.E) D.host.E) :
    AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) where
  carrier := {z | ∀ i j, z i j ∈ A}
  zero_mem' := fun _ _ => A.zero_mem
  add_mem' := fun h₁ h₂ i j => A.add_mem (h₁ i j) (h₂ i j)
  neg_mem' := fun h i j => A.neg_mem (h i j)

def polarLat (D : D7) (cc : Ideal (𝓞 D.host.K)) (𝔮 : Ideal (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {t | ∀ b ∈ 𝔮, D.host.conj (b : D.host.E) * t ∈ 𝔮 • coefLat D cc}
  zero_mem' := fun b _ => by simp
  add_mem' := fun h₁ h₂ b hb => by rw [mul_add]; exact Submodule.add_mem _ (h₁ b hb) (h₂ b hb)
  smul_mem' := fun r t h b hb => by
    rw [mul_smul_comm]; exact Submodule.smul_mem _ r (h b hb)

abbrev lat0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (a d : ℕ) : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
  matIn D a d (coefLat D cc)

abbrev latQ (D : D7) (cc : Ideal (𝓞 D.host.K)) (a d : ℕ) (𝔮 : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
  matIn D a d (𝔮 • coefLat D cc)

abbrev latPolar (D : D7) (cc : Ideal (𝓞 D.host.K)) (a d : ℕ) (𝔮 : Ideal (𝓞 D.host.E)) :
    AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
  matIn D a d (polarLat D cc 𝔮)

def fourier (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (𝔮 : Ideal (𝓞 D.host.E))
    (Φ : lat0 D cc a d → ℂ) (y : Matrix (Fin d) (Fin a) D.host.E) : ℂ :=
  ((Ideal.absNorm 𝔮 : ℂ) ^ (a * d))⁻¹ *
    ∑ᶠ x : lat0 D cc a d ⧸ (latQ D cc a d 𝔮).addSubgroupOf (lat0 D cc a d),
      Φ x.out * (kap D (tor0 D cc δ)
        (pt D (tor0 D cc δ) δ ((x.out : lat0 D cc a d) : Matrix (Fin d) (Fin a) D.host.E))
        (pt D (tor0 D cc δ) δ y))⁻¹

def xiVec (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (𝔮 : Ideal (𝓞 D.host.E))
    (Φ : lat0 D cc a d → ℂ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  fun w => ∑ᶠ y : latPolar D cc a d 𝔮 ⧸ (latQ D cc a d 𝔮).addSubgroupOf (latPolar D cc a d 𝔮),
    fourier D cc δ 𝔮 Φ ((y.out : latPolar D cc a d 𝔮) : Matrix (Fin d) (Fin a) D.host.E) *
      Wd D (tor0 D cc δ)
        (pt D (tor0 D cc δ) δ ((y.out : latPolar D cc a d 𝔮) : Matrix (Fin d) (Fin a) D.host.E)) e0 w

def levelIdeal (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : S → ℕ) : Ideal (𝓞 D.host.E) :=
  ∏ P : S, (P : HeightOneSpectrum (𝓞 D.host.E)).asIdeal ^ c P

def withConj (D : D7) (𝔮 : Ideal (𝓞 D.host.E)) : Ideal (𝓞 D.host.E) := 𝔮 * ((D.host.conj : _) • 𝔮)

def UnrOutside (D : D7) {N : ℕ} (χ : HeckeU D N) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ u, IntU D u → (∀ k : ℕ, (u : AE D) - 1 ∈ idHat D (𝔪 ^ k)) → χ.f u = 1

def ModLeOneAll (x : ℂ) : Prop := ∃ h : x ∈ Qbar, ∀ σ : Qbar →+* ℂ, ‖σ ⟨x, h⟩‖ ≤ 1

structure PairDatum (D : D7) where

  cc : Ideal (𝓞 D.host.K)
  δ : ℂ
  crv : Crv D cc δ
  t0 : ℂ
  isT0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0

  a : ℕ
  d : ℕ
  a_le : a ≤ d
  d_even : Even d

  e0 : VC D a d → ℂ
  isOddE0 : oddE0 D cc δ t0 a d e0

  W : WeilO D cc δ a d e0

  n : D.what₂.Tau → ℕ
  weight : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)

  S : Finset (HeightOneSpectrum (𝓞 D.host.E))
  c : S → ℕ
  c_pos : ∀ P, 1 ≤ c P

  split : ∀ P ∈ S, ∀ P' ∈ S, (D.host.conj : _) • P.asIdeal ≠ P'.asIdeal

  splitK : ∀ P ∈ S, ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal →
    p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1

  addUnr : ∀ P ∈ S, ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal →
    Nat.Coprime (Ideal.absNorm cc) p ∧ ¬ (p : ℤ) ∣ NumberField.discr D.host.E

  unr : UnrOutside D W.chV (withConj D (levelIdeal D S c))
  unr' : UnrOutside D W.chV' (withConj D (levelIdeal D S c))

  Φ : S → lat0 D cc a d → ℂ
  Φ_inv : ∀ (P : S) (x x' : lat0 D cc a d),
    (x : Matrix (Fin d) (Fin a) D.host.E) - (x' : Matrix (Fin d) (Fin a) D.host.E) ∈
      latQ D cc a d ((P : HeightOneSpectrum (𝓞 D.host.E)).asIdeal ^ c P) → Φ P x = Φ P x'
  Φ_val : ∀ P x, ModLeOneAll (Φ P x)

  what₂ : RowSet a d

  fixK : ∀ k ∈ intPts D a,
    W.Om k 1 (xiVec D cc δ (levelIdeal D S c) (fun x => ∏ P, Φ P x) e0) =
      xiVec D cc δ (levelIdeal D S c) (fun x => ∏ P, Φ P x) e0

  eigenJ : ∀ j ∈ levelJ D (levelIdeal D S c) what₂.1, ∃ (ζ : ℂ) (m : ℕ), 0 < m ∧ ζ ^ m = 1 ∧
    W.Om 1 j (xiVec D cc δ (levelIdeal D S c) (fun x => ∏ P, Φ P x) e0) =
      ζ • xiVec D cc δ (levelIdeal D S c) (fun x => ∏ P, Φ P x) e0

namespace PairDatum

end PairDatum

end GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
