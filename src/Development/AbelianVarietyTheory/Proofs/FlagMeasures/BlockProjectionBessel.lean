import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KfinCoefMulSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieri

variable {k r : ℕ}

def withRep (L : LocBessel k r) (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (hR : R.IsDS L.ε mu) :
    LocBessel k r :=
  { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }

theorem fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

def coefR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (R : Rep k r) (v v' : R.H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, R.σ g v'⟫_ℂ • ξ)

theorem herm_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om : ι → ℂ} {a g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ GG k r) (hg : g ∈ GG k r) (hom : ρ a *ᵥ om = om) (x : ι → ℂ) :
    herm Γ (ρ (a⁻¹ * g) *ᵥ x) om = herm Γ (ρ g *ᵥ x) om := by
  obtain ⟨-, -, -, hmul, hinv, -⟩ := hρ
  obtain ⟨hai, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
  have hm : a⁻¹ * g ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg
  have e : ρ g = ρ a * ρ (a⁻¹ * g) := by
    rw [← hmul a ha _ hm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold herm
  rw [e]
  conv_rhs => rw [← hom]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hinv a ha]

theorem one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_Sset_of_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g ∈ Sset k r z := by
  refine ⟨g, hg, 1, ⟨one_mem_UH, fun a i _ => ?_, fun i j _ _ _ => ?_⟩, (Matrix.mul_one g).symm⟩ <;>
    exact Matrix.one_apply

theorem mem_Sset_of_N (z : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g ∈ Sset k r z :=
  ⟨1, ⟨one_mem_UH, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, g, hg,
    (Matrix.one_mul g).symm⟩

theorem herm_cell {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om om' : ι → ℂ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hom : ∀ g ∈ Sset k r z, ρ g *ᵥ om = om) (hom' : ∀ g ∈ Sset k r z', ρ g *ᵥ om' = om')
    {a n γ n' a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ GG k r)
    (ha : a ∈ UWset k r z) (hn : n ∈ Nset k r) (ha' : a' ∈ UWset k r z') (hn' : n' ∈ Nset k r) :
    a⁻¹ * n⁻¹ * γ * n' * a' ∈ GG k r ∧
      herm Γ (ρ (a⁻¹ * n⁻¹ * γ * n' * a') *ᵥ om') om = herm Γ (ρ γ *ᵥ om') om := by
  have mul : ∀ {x y}, x ∈ GG k r → y ∈ GG k r → x * y ∈ GG k r := fun hx hy => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hx hy
  have hai := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha.1).1
  have hni := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hn.1).1
  have h1 := mul (mul hai hni) hγ
  have h2 := mul h1 hn'.1
  refine ⟨mul h2 ha'.1, ?_⟩
  rw [hρ.2.2.2.1 _ h2 _ ha'.1, hρ.2.2.2.1 _ h1 _ hn'.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hom' _ (mem_Sset_of_UW ha'), hom' _ (mem_Sset_of_N z' hn'), Matrix.mul_assoc,
    herm_inv hρ ha.1 (mul hni hγ) (hom _ (mem_Sset_of_UW ha)),
    herm_inv hρ hn.1 hγ (hom _ (mem_Sset_of_N z hn))]

end GlobalTheory.CellPieri

end
