import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingIdentityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualBasesColProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpand
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMemIff

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem mainProof : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hrow hzero φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le_of_rowLen (hzero s N le_rfl)
  have hν : ∀ s, ν (e s) = fun r : Fin N => (nu s).rowLen r := fun s => funext fun r => (hrow s r).symm
  choose ι hι hdec b g c d Nc hNc h1 h2 h3 h4 h5 using fun s => _root_.GlobalTheory.WeylLatDualProof.dual_bases_colProd GlobalTheory.T.columnMinorProducts_fock_reproducing_identity N (nu s) (hY s)
  rw [_root_.GlobalTheory.WeylLatDualProof.integral_minors_iff_basis p Lt N nu hY ι b c d h1 h2 φ]
  have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) = fun y =>
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) :=
    funext fun y => _root_.GlobalTheory.WeylLatDualProof.phi_DeX_expand p Lt T e N nu hY ι b g c h1 h3 φ y
  rw [hfun, _root_.GlobalTheory.WeylCombInt.comb_mem_iff p Lt T e he N ν ι b g Nc hNc h4 (fun s => by rw [hν s]; exact h5 s)]

end GlobalTheory.WeylLatDualProof
