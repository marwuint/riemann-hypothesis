import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion

noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField Filter Topology MeasureTheory

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-(c * Real.log X / Real.log B)) + C * Real.exp (-(c * Real.sqrt (Real.log X)))

section RayClass

variable (K0 : Type) [Field K0] [NumberField K0]

def CoprimeTo (qq I : Ideal (𝓞 K0)) : Prop := I ≠ ⊥ ∧ I ⊔ qq = ⊤

def RayRel (qq I J : Ideal (𝓞 K0)) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I = Ideal.span {b} * J

def RayCls (qq : Ideal (𝓞 K0)) : Type :=
  Quot (fun I J : {I : Ideal (𝓞 K0) // CoprimeTo K0 qq I} => RayRel K0 qq I.1 J.1)

def grCard (qq : Ideal (𝓞 K0)) : ℕ := Nat.card (RayCls K0 qq)

def Bmod (qq : Ideal (𝓞 K0)) : ℝ := 4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

def piCC (qq I0 : Ideal (𝓞 K0)) (X : ℝ) : ℕ :=
  Set.ncard {P : Ideal (𝓞 K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
    (Ideal.absNorm P : ℝ) ≤ X}

def nDeg1 (qq I0 : Ideal (𝓞 K0)) (X h : ℝ) : ℕ :=
  Set.ncard {P : Ideal (𝓞 K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
    (Ideal.absNorm P).Prime ∧ X < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ X * (1 + h)}

def IsRealRayChar (qq : Ideal (𝓞 K0)) (th : Ideal (𝓞 K0) → ℤ) : Prop :=
  (∀ I, CoprimeTo K0 qq I → th I = 1 ∨ th I = -1) ∧
  (∀ I J, CoprimeTo K0 qq I → CoprimeTo K0 qq J → RayRel K0 qq I J → th I = th J) ∧
  (∀ I J, CoprimeTo K0 qq I → CoprimeTo K0 qq J → th (I * J) = th I * th J)

def SiegelZeroExceptionalCharacter (Comparison₂ : Ideal (𝓞 K0) → ℝ → (Ideal (𝓞 K0) → ℤ) → Prop) (C0 Cr cr cQ : ℝ) : Prop :=
  ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
    ∃ (be : ℝ) (th : Ideal (𝓞 K0) → ℤ),
      ((∀ I, th I = 0) ∨ (IsRealRayChar K0 qq th ∧ 1 / 2 ≤ be ∧ be < 1 ∧
        cQ / (Bmod K0 qq ^ 2 * Real.log (Bmod K0 qq)) ≤ 1 - be)) ∧
      Comparison₂ qq be th ∧
      ∀ I0, CoprimeTo K0 qq I0 → ∀ X : ℝ, Bmod K0 qq ^ C0 ≤ X →
        |(piCC K0 qq I0 X : ℝ) - (Li X - (th I0 : ℝ) * Li (X ^ be)) / (grCard K0 qq : ℝ)| ≤
          rhoErr Cr cr (Bmod K0 qq) X * ((Li X - (th I0 : ℝ) * Li (X ^ be)) / (grCard K0 qq : ℝ))

def Q4 (C0 Cr cr cQ : ℝ) : Prop := SiegelZeroExceptionalCharacter K0 (fun _ _ _ => True) C0 Cr cr cQ

def ShortIntervalLowerBound (cQ C0 Cr cr c1 c2 : ℝ) : Prop :=
  ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ → ∀ X : ℝ, Bmod K0 qq ^ C0 ≤ X →
    (∀ (be : ℝ) (th : ℤ), (th = -1 ∨ th = 0 ∨ th = 1) → 1 / 2 ≤ be → be < 1 →
      cQ / (Bmod K0 qq ^ 2 * Real.log (Bmod K0 qq)) ≤ 1 - be →
      c1 * Bmod K0 qq ^ (-5 : ℝ) * X / Real.log X ≤ Li X - (th : ℝ) * Li (X ^ be)) ∧
    (∀ I0, CoprimeTo K0 qq I0 → ∀ h : ℝ, rhoErr Cr cr (Bmod K0 qq) X ≤ h / 100 → h ≤ 1 →
      Bmod K0 qq ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
      c2 * h * Bmod K0 qq ^ (-6 : ℝ) * X / Real.log X ≤ (nDeg1 K0 qq I0 X h : ℝ))

end RayClass

def TieQ (c1 : ℝ) (qq : Ideal (𝓞 ℚ)) (be : ℝ) (th : Ideal (𝓞 ℚ) → ℤ) : Prop :=
  ∀ (N : ℕ) [NeZero N], Ideal.absNorm qq = N →
    ((∀ I, th I = 0) ∧ ∀ (χ : DirichletCharacter ℂ N) (b : ℝ),
      1 - c1 / Real.log (Bmod ℚ qq) ≤ b → b < 1 → DirichletCharacter.LFunction χ b ≠ 0) ∨
    (∃ χ1 : DirichletCharacter ℂ N, IsRealChar χ1 ∧
      (∀ I, CoprimeTo ℚ qq I → ((th I : ℤ) : ℂ) = χ1 ((Ideal.absNorm I : ℕ) : ZMod N)) ∧
      DirichletCharacter.LFunction χ1 be = 0 ∧
      ∀ (χ : DirichletCharacter ℂ N) (b : ℝ), 1 - c1 / Real.log (Bmod ℚ qq) ≤ b → b < 1 →
        DirichletCharacter.LFunction χ b = 0 → χ = χ1 ∧ b = be)

def NormOneMod (D : D7) (M g : ℕ) : Prop :=
  ∃ π ρ : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (ρ : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) - 1 = (M : D.host.E) * ρ ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (g : D.host.E)

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

abbrev ZPt : Type := Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ

def zOrd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def ArchimedeanSignatureMatching (D : D7) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir D.host.d) (2 * D.host.d) →
    ((classNumber D.host.K : ℕ) : ℂ) =
      ((Real.sqrt D.host.d : ℝ) : ℂ) * DirichletCharacter.LFunction χ 1 / (Real.pi : ℂ)

def adm6 (_D : D7) (C1 c : ℝ) : Prop :=
  (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset ZPt,
    (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧
      DirichletCharacter.LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) →
    ((∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤
      C1 * Q ^ ((1 : ℝ) / 4)) ∧
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ,
    DirichletCharacter.LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re →
    IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 1 ∧
      ∀ ρ' : ℂ, DirichletCharacter.LFunction χ ρ' = 0 →
        1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
  (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3))

def adm7 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖)

def adm8 (D : D7) (C0 Cr cr cQ c1 : ℝ) : Prop :=
  SiegelZeroExceptionalCharacter ℚ (TieQ c1) C0 Cr cr cQ ∧ Q4 D.host.K C0 Cr cr cQ

def adm11 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (zOrd χ ρ : ℝ) ≤ C * Real.log (N * (|t| + 2))

theorem factorsThrough_inv {N : ℕ} {χ : DirichletCharacter ℂ N} {d : ℕ}
    (h : χ.FactorsThrough d) : χ⁻¹.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive DirichletCharacter.conductor at *
  have hs : χ⁻¹.conductorSet = χ.conductorSet := by
    ext d
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.mem_conductorSet_iff]
    exact ⟨fun h' => by simpa using factorsThrough_inv h', factorsThrough_inv⟩
  rw [hs]
  exact h

theorem zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hprim := isPrimitive_inv hχ
  have hρ0 : ρ ≠ 0 := fun h => by
    rw [h] at h0
    simp at h0
  have h1ρ : (1 - ρ) ≠ 0 := fun h => by
    have e := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at e
    linarith
  have hg : DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have e := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ) ρ (Or.inl hρ0)
    rw [hz, eq_comm, div_eq_zero_iff] at e
    exact e.resolve_right hg
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹) (1 - ρ) (Or.inl h1ρ),
    hprim.completedLFunction_one_sub ρ, inv_inv, hc]
  simp

def Conclusion2 (_D : D7) (x eps C : ℝ) : Prop :=
  (∀ Q : ℝ, 1 ≤ Q →
    (∑ N ∈ Finset.range ⌊Q⌋₊, ({χ : DirichletCharacter ℂ (N + 1) |
      χ.IsPrimitive ∧ IsRealChar χ ∧ ¬ GoodFor Q χ}.ncard : ℝ)) ≤ C * Q ^ ((1 : ℝ) / 4)) ∧
  (∀ Q : ℝ, 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GoodFor Q χ →
      (∃ S : ℂ, TailSum χ (zz x) S ∧ ‖(x : ℂ) * S‖ ≤ x ^ eps) ∧
      ‖logDerivativeAtOne χ‖ ≤ C * Real.log x)

def GoodAll (Q : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M → GoodFor Q χ

def BoundsII (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M →
    ‖gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChoiceOfModulusAndDiscriminant (n : ℕ) (x eps C : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 x eps) < q ∧ (q : ℝ) ≤ X1 x eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 x eps) < d ∧ (d : ℝ) ≤ X2 x eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1) ∧

  GoodAll (8 * X1 x eps) (psDir q) (8 * q * d) ∧
  GoodAll (8 * X1 x eps) (fun a => chi8 a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (chDir d) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chDir d a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a * psDir q a) (8 * q * d) ∧

  BoundsII x eps C (psDir q) (8 * q * d) ∧ BoundsII x eps C (chDir d) (8 * q * d) ∧
  BoundsII x eps C (fun a => chDir d a * psDir q a) (8 * q * d) ∧

  Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PairAt (Y eps : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 Y eps) < q ∧ (q : ℝ) ≤ X1 Y eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 Y eps) < d ∧ (d : ℝ) ≤ X2 Y eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1)

def PropTwoSixBoxHypothesis (D : D7) (x eps : ℝ) : Prop :=
  (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ BoxE D Y eps) ∧ Real.log (NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PrimesAsPropTwoFive (D : D7) (x eps C : ℝ) : Prop :=
  (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ PairAt Y eps D.host.q D.host.d) ∧ PropTwoSixBoxHypothesis D x eps ∧
  BoundsII x eps C (psDir D.host.q) (8 * D.host.q * D.host.d) ∧ BoundsII x eps C (chDir D.host.d) (8 * D.host.q * D.host.d) ∧
  BoundsII x eps C (fun a => chDir D.host.d a * psDir D.host.q a) (8 * D.host.q * D.host.d)

def PropTwoSixThinScales (D : D7) (x eps c : ℝ) : Prop :=
  PropTwoSixBoxHypothesis D x eps →
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

def GofA (D : D7) (x eps C : ℝ) (g : ℕ) : Prop :=
  g.Prime ∧ NormOneMod D (NE D) g ∧ ∃ Y : ℝ, ((D.R.k : ℝ) * Real.exp (x ^ eps)) ^ 8 ≤ Y ∧
    Y ≤ Real.exp (x ^ eps) ^ C ∧ Y ≤ g ∧ (g : ℝ) ≤ 2 * Y

def PrimesAsPropTwoSeven (D : D7) (x eps C : ℝ) : Prop := ∀ i : Fin 2, GofA D x eps C (D.host.g i)

section Family

variable {eps : ℝ}

def FamilyAdmittedLemmaFour (Fm : FamP eps) : Prop := ∀ x > 1, ∀ i : Fm.Ix x, ArchimedeanSignatureMatching (Fm.D x i)
def FamilySixthHypothesis (Fm : FamP eps) : Prop :=
  ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm6 (Fm.D x i) C1 c
def adm7F (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm7 (Fm.D x i) C
def FamilyTemperatureAsymptotic (Fm : FamP eps) : Prop :=
  ∃ C0 Cr cr cQ c1 : ℝ, 0 < C0 ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cQ ∧ 0 < c1 ∧
    ∀ x > 1, ∀ i : Fm.Ix x, adm8 (Fm.D x i) C0 Cr cr cQ c1
def ComplementTwoFamily (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm11 (Fm.D x i) C

def FamilyPrimesAsPropTwoFive (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, PrimesAsPropTwoFive (Fm.D x i) x eps C
def FamilyPropTwoSixCongruenceForm (Fm : FamP eps) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, PropTwoSixThinScales (Fm.D x i) x eps c
def FamilyPrimesAsPropTwoSeven (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, PrimesAsPropTwoSeven (Fm.D x i) x eps C

end Family

end Formalism.MainNotions.ShortIntervalPrimes

end
