import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatPt

theorem isPtAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs ×
          GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp
  exact ⟨_root_.GlobalTheory.TwLatRat.lat_moved A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp, _root_.GlobalTheory.RatFrame.frame_rat A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp,
    _root_.GlobalTheory.TwV.funMoved_ptAd_rat A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp⟩

theorem xiPt_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi
  rcases lt_trichotomy i t.m2 with h | h | h
  · exact _root_.GlobalTheory.RatEntry.xiPt_rat A dtU a hP hTie i hi h
  · exact _root_.GlobalTheory.CplRat.xiPt_cpl_smul A dtU a hP hTie i hi h
  · exact _root_.GlobalTheory.TopRat.xiPt_top_smul A dtU a hP hTie i hi h

theorem ratLaw_of_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hAw
  intro i hi β β' x x' x₁ x₁' γ hγ γ' hγ' h₁ h₁' z
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.TwRat.ratUnitCol A dtU a hP hTie i (Nat.le_of_succ_le hi) γ hγ
  obtain ⟨g', hg'⟩ := _root_.GlobalTheory.TwRat.ratUnitCol A dtU a hP hTie (i + 1) hi γ' hγ'
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  have hq := isPtAd_rat A dtU a hP hTie i (Nat.le_of_succ_le hi) β x x₁ γ hγ h₁ g hg p hp
  have hq' := isPtAd_rat A dtU a hP hTie (i + 1) hi β' x' x₁' γ' hγ' h₁' g' hg' p' hp'
  have hE1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' := ⟨⟨_, hq⟩, ⟨_, hq'⟩⟩
  have hE0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  have a1 := hAw i hi β β' x₁ x₁' x₁ x₁' _ _ _ _ hq hq' hE1.1.choose_spec hE1.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  have a0 := hAw i hi β β' x x' x x' _ _ _ _ hp hp' hE0.1.choose_spec hE0.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  unfold xiAd
  rw [dif_pos hE1, dif_pos hE0, a1, a0, _root_.GlobalTheory.TwV.seamHom_inFr_stdG A dtU a hP hTie i hi γ γ' g g' hg hg' z]
  rw [xiPt_smul A dtU a hP hTie i hi β β' x x' p p' hp hp' g g']

end GlobalTheory.RatPt

end
