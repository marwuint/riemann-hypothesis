import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalars
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoords
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalars
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumnsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryRestrictionScalarsBlockZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo_mat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P AI T n _ _ K r σ Q hσ hQ c hcr hcc hcoc hdR
  obtain ⟨ω, W, hW, hω, hcoef⟩ := _root_.GlobalTheory.PMon.coef_unr_continuous l r hσ.pos
  obtain ⟨ρ₀, p, hρc, hpK, hint, hc₀⟩ := _root_.GlobalTheory.PMon.exists_ratForm l n K r σ ω W hσ hW hω hcoef
  obtain ⟨c₀, hc₀c, hpc⟩ := hc₀ c hcr hcc
  have hcoc₀ := _root_.GlobalTheory.PMon.cocycle_rat_coords l n K r σ ρ₀ p c c₀ hint hpc hcoc
  obtain ⟨Q₀, hQ₀⟩ := _root_.GlobalTheory.PMon.period_resScalars l P n K r σ Q ρ₀ p hQ hpK hint
  have hsst : IsSst P (repOf ρ₀) :=
    _root_.GlobalTheory.PMon.isSst_of_periodMatrix l P AI T (n × Fin r) K (n × Fin r → ℚ_[l]) (Pi.basisFun ℚ_[l] _) (repOf ρ₀) Q₀
      (fun g => by rw [toMatrix_repOf]; exact hQ₀ g)
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.PMon.DRvec.ratCocycle_trivial l P n K r σ ρ₀ p c c₀ hpK hint hpc hdR
  obtain ⟨bd, hbd⟩ := _root_.GlobalTheory.CobColumn.coboundary_tmul_of_column l P K _ ρ₀ c₀ β hβ
  have hcontρ : ∀ v : n × Fin r → ℚ_[l], Continuous fun g => repOf ρ₀ g v := by
    intro v
    simp only [repOf_apply]
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hρc i j).mul continuous_const
  obtain ⟨bs, hbs⟩ := _root_.GlobalTheory.PMon.hyodo l P AI T K (n × Fin r → ℚ_[l]) (repOf ρ₀) hcontρ hsst c₀ hc₀c
    hcoc₀ ⟨bd, hbd⟩
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.coboundary_semistableTensor_columns l P K _ ρ₀ c₀ bs hbs
  exact _root_.GlobalTheory.PMon.coboundary_block_zero l P n K r hσ.pos σ ρ₀ p c c₀ β' hpK hint hpc hβ'

end GlobalTheory.PMon

end
