import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PhiRelFamScale
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt
open NumberField

theorem exists_compatible_roots {O X F : Type} [CommRing O] [StarRing O] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] [Module.Free ℤ O] [Field F] [IsAlgClosed F] {w : O} (hw : w + star w = 1) {s : X → X → Fˣ}
    (hs : IsScalarForm O s) : ∃ r : ℕ → X → X → Fˣ, (∀ n, IsScalarForm O (r n)) ∧
      (∀ n, 0 < n → ∀ y x, r n y x ^ n = s y x) ∧ ∀ n m, 0 < n → 0 < m → ∀ y x, r (n * m) y x ^ m = r n y x := by
  letI : DivisibleBy (Additive Fˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : F) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  letI : DivisibleBy (Additive Fˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨T, hT, h⟩ := Forms.exists_balForms_lift hw (AddMonoidHom.eval (1 : ℚ) : (ℚ →+ Additive Fˣ) →+ Additive Fˣ)
    (fun u => by
      obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
        (Int.castAddHom ℚ) Int.cast_injective (zmultiplesHom _ u)
      exact ⟨ρ, by simpa using DFunLike.congr_fun hρ 1⟩) hs.mem_balForms
  refine ⟨fun n y x => (T y x (n : ℚ)⁻¹).toMul, fun n => ⟨fun y x x' => by beta_reduce; rw [map_add]; rfl,
    fun y x => by beta_reduce; rw [hT.1 y x], fun a y x => by beta_reduce; rw [hT.2 a y x]⟩, fun n hn y x => ?_, fun n m hn hm y x => ?_⟩
  · have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    show (n • T y x (n : ℚ)⁻¹).toMul = _
    rw [← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ this]
    exact h y x
  · have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    show (m • T y x ((n * m : ℕ) : ℚ)⁻¹).toMul = (T y x (n : ℚ)⁻¹).toMul
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ this, _root_.mul_one]

theorem QkRel.qkExt_of {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ψ : PsiFam D} {hψ : ∀ χ, (ψ χ).IsGen}
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] {k : ℕ} {f : F →+* F'}
    {r : D.X → D.X → Fˣ} {r' : D.X → D.X → F'ˣ} (hr : ∀ y x, r' y x = Units.map f.toMonoidHom (r y x))
    {p : QkPt D F k} {q : QkPt D F' k} {p' : QkPt (withPsi D ψ hψ) F k} {q' : QkPt (withPsi D ψ hψ) F' k}
    (hp : QkRel r p p') (hq : QkRel r' q q') (h : QkExt f p' q') : QkExt f p q :=
  QkRel.qkExt (D := withPsi D ψ hψ) (fun y x => by rw [map_inv, hr]) hp.symm hq.symm h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem halfUnit_add_star (H : Host E) : letI := H.starRing; H.w0 + star H.w0 = 1 := by
  show H.w0 + H.bar H.w0 = 1
  rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]

section Tate

variable {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} [Module (𝓞 E) D₀.X] {w : 𝓞 E}
  {t : D₀.X → D₀.X → (FractionRing R)ˣ} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_tateIsoQ_of_roots (hB : D₀.TauBimult) : letI := H.starRing
    ∀ (hw : w + star w = 1) (ht : IsScalarForm (𝓞 E) t) (oa : D₀.OAct (𝓞 E)) (r : ℕ → D₀.X → D₀.X → Fˣ),
      (∀ n, 0 < n → IsRootForm (𝓞 E) n t (r n)) → (∀ n m, 0 < n → 0 < m → ∀ y x, r (n * m) y x ^ m = r n y x) →
      ∀ I : TateIsoQ D D₀ oa F, ∃ I' : TateIsoQ D (twist D₀ w t) (twistAct hw ht oa) F,
        I'.ζ = I.ζ ∧ ∀ n, 0 < n → ∀ a, QkRel (r n) (I.ev n a) (I'.ev n a) := by
  letI := H.starRing
  intro hw ht oa r hr hc I
  have hq := psiRel_rescale D₀ fun y => t y (w • y)
  have ex : ∀ n a, ∃ p : QkPt (twist D₀ w t) F n, 0 < n → QkRel (r n) (I.ev n a) p := fun n a => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨qkZero (tauBimult_twist hw ht hB) F 0, fun h => absurd h (lt_irrefl 0)⟩
    · exact ⟨_, fun _ => qkRel_qkScale hw ht hq (hr n hn) _⟩
  choose ev hev using ex
  exact ⟨{ ζ := I.ζ
           ζ_prim := I.ζ_prim
           ζ_pow := I.ζ_pow
           ev := ev
           add := fun n hn a b => (hev n a hn).qkAdd hw ht hq (hr n hn) (hev n b hn) (hev n _ hn) (I.add n hn a b)
           lin := fun n hn x a => (hev n a hn).qkAct hw ht hq (hr n hn) rfl (hev n _ hn) (I.lin n hn x a)
           ker := fun n hn a b => ((hev n a hn).equiv_iff hw ht hq (hr n hn) (hev n b hn)).trans (I.ker n hn a b)
           onto := fun n hn p' => by
             obtain ⟨p, rfl⟩ := (qkScaleEquiv hw ht hq (hr n hn) _).surjective p'
             obtain ⟨a, ha⟩ := I.onto n hn p
             exact ⟨a, (hev n a hn).equiv hw ht hq (hr n hn) (qkRel_qkScaleEquiv hw ht hq (hr n hn) p) ha⟩
           tower := fun n m hn hm a => by
             obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm a
             have e := qkRel_qkScale (D := D₀) (hψ := (twist D₀ w t).psi_gen) hw ht hq (hr n hn) q
             have e' := hev (n * m) a (Nat.mul_pos hn hm)
             exact ⟨_, h₁.trans e'.1.symm, e'.2.isNsmul e.2 (fun χ => by rw [h₁, hc n m hn hm]) h₂,
               e.equiv hw ht hq (hr n hn) (hev n a hn) h₃⟩
           isom := fun n hn a b => ((hev n a hn).weilQkIs_iff hw ht hq (hr n hn) (hev n b hn) _).2 (I.isom n hn a b) },
    rfl, fun n hn a => hev n a hn⟩

theorem exists_tateIsoQ_twist [IsAlgClosed F] (hB : D₀.TauBimult) : letI := H.starRing
    ∀ (hw : w + star w = 1) (ht : IsScalarForm (𝓞 E) t) (oa : D₀.OAct (𝓞 E)) (N : ℕ) (s : D₀.X → D₀.X → Fˣ),
      IsRootForm (𝓞 E) N t s → ∀ I : TateIsoQ D D₀ oa F,
      ∃ (r : ℕ → D₀.X → D₀.X → Fˣ) (I' : TateIsoQ D (twist D₀ w t) (twistAct hw ht oa) F),
        (∀ n, 0 < n → IsRootForm (𝓞 E) n t (r n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ y x, r (n * m) y x ^ m = r n y x) ∧
        (∀ n, 0 < n → n ∣ N → ∀ y x, r n y x = s y x ^ (N / n)) ∧
        I'.ζ = I.ζ ∧ ∀ n, 0 < n → ∀ a, QkRel (r n) (I.ev n a) (I'.ev n a) := by
  letI := H.starRing
  intro hw ht oa N s hs I
  have := Forms.projective_of_int (𝓞 E) D₀.X
  have : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨r, h₁, h₂, h₃⟩ := exists_compatible_roots hw hs.1
  have a₁ : ∀ n, 0 < n → IsRootForm (𝓞 E) n t fun y x => r n y x ^ N := fun n hn =>
    ⟨(h₁ n).pow N, fun y x => by rw [pow_right_comm, h₂ n hn, hs.2]⟩
  have a₂ : ∀ n m, 0 < n → 0 < m → ∀ y x, (r (n * m) y x ^ N) ^ m = r n y x ^ N := fun n m hn hm y x => by
    rw [pow_right_comm, h₃ n m hn hm]
  obtain ⟨I', hI⟩ := exists_tateIsoQ_of_roots hB hw ht oa (fun n y x => r n y x ^ N) a₁ a₂ I
  refine ⟨_, I', a₁, a₂, fun n hn hN y x => ?_, hI⟩
  rw [← h₂ n hn, ← pow_mul, Nat.mul_div_cancel' hN]

end Tate

section ThetaShiftProofs

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O']
  {b : O →+* O'} (a : ArcIn D l β O' b)

variable {ρ : a.D₀.X → a.D₀.X → O'ˣ}

variable (hρ : letI := H.starRing; IsScalarForm (𝓞 E) ρ)

end ThetaShiftProofs

end GlobalTheory.TauTwist
