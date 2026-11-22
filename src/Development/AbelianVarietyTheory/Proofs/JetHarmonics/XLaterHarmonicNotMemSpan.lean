import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarmonicChartValues
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TotalDegreeEqOfMemHarmA
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfFischSelf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NabUniqCompare

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem chartVal_eq [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal C k f P = GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues.chartVal Xo c C k f P := rfl

theorem pderiv_swap {σ R : Type} [CommRing R] (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem isHarmonic_iff_cmType {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) :
    IsHarmonic c P ↔ P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by
  have e : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ↔
      ∀ τ : E →+* ℂ, InPsi H τ → ∀ (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap,
      LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  rw [e]
  refine ⟨fun h τ _ => h τ, fun h τ => ?_⟩
  by_cases hτ : InPsi H τ
  · exact h τ hτ
  · have key : ∀ σ : E →+* ℂ, σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) →
        ∀ (i : Fin (Dw.mult σ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨σ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
      rintro σ rfl i i'
      rw [← h _ ((GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff τ).2 hτ) i' i]
      exact Finset.sum_congr rfl fun b _ => pderiv_swap _ _ _
    exact key τ (by ext x; simp)

def IsTopHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
    ∃ a : (E →+* ℂ) × ℕ → ℕ, RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P

theorem mem_harmA_iff {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) :
    P ∈ harmA c a n ↔ IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
      RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P ∧ ∀ m, IsIntegral ℤ (P.coeff m) := by
  rw [isHarmonic_iff_cmType]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

def colSumL {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S) :
    MvPolynomial (LtN Dw n) c.F →ₗ[c.F] S :=
  (MvPolynomial.basisMonomials (LtN Dw n) c.F).constr c.F fun m => ∏ b : Fin n, v b (colOf m b)

theorem colSumL_apply {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : colSumL c v P = colSum c v P := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, colSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (MvPolynomial.monomial m (P.coeff m) : MvPolynomial (LtN Dw n) c.F) =
      P.coeff m • MvPolynomial.basisMonomials (LtN Dw n) c.F m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, colSumL, Module.Basis.constr_basis, Algebra.smul_def]

def UniqueOn (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F), Q n P →
        sysVal Xo c nab y k F P = sysVal Xo c nab' y k F P

theorem UniqueOn.mono {Q Q' : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop} (h : UniqueOn Xo c Q)
    (hQ : ∀ n P, Q' n P → Q n P) : UniqueOn Xo c Q' :=
  fun nab nab' h1 h2 S _ _ y k n F P hP => h nab nab' h1 h2 S y k n F P (hQ n P hP)

theorem uniqueOn_span_iff (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) :
    (UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' | Q n P'}) ↔ UniqueOn Xo c Q := by
  refine ⟨fun h => h.mono Xo c fun n P hP => Submodule.subset_span hP, ?_⟩
  intro h _ nab nab' h1 h2 S _ _ y k n F P hP
  unfold sysVal
  rw [← colSumL_apply, ← colSumL_apply]
  refine LinearMap.eqOn_span ?_ hP
  intro P' hP'
  rw [colSumL_apply, colSumL_apply]
  exact h nab nab' h1 h2 S y k n F P' hP'

theorem span_harmA_eq (n : ℕ) :
    Submodule.span c.F {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n} =
      Submodule.span c.F {P | IsTopHarmonic c P} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro P ⟨a, ha⟩
    rw [mem_harmA_iff] at ha
    exact ⟨ha.1, ha.2.1, a, ha.2.2.1⟩
  · refine Submodule.span_le.2 ?_
    rintro P ⟨h1, h2, a, h3⟩
    obtain ⟨N, hN, hP, -⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P
      ⟨(isHarmonic_iff_cmType c P).1 h1, h2, h3⟩
    have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have := Submodule.smul_mem _ (N : c.F)⁻¹ (Submodule.subset_span
      (s := {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n}) ⟨a, hP⟩)
    rwa [inv_smul_smul₀ hN'] at this

theorem thExprUniqSt_iff_harmA : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun n P => ∃ a, P ∈ harmA c a n := by
  constructor
  · rintro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ y k n F P ⟨a, ha⟩
    letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F a P ha
  · intro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ _ y k n F a P ha
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F P ⟨a, ha⟩

theorem thExprUniqSt_iff_span : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l),
      UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' : MvPolynomial (LtN Dw n) c.F | IsTopHarmonic c P'} := by
  rw [thExprUniqSt_iff_harmA]
  refine forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => ?_
  rw [← uniqueOn_span_iff]
  simp only [span_harmA_eq]

theorem thExprUniqSt_iff_top : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun _ P => IsTopHarmonic c P := by
  rw [thExprUniqSt_iff_span]
  exact forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => uniqueOn_span_iff Xo c _

end GlobalTheory.NabUniqCompare
