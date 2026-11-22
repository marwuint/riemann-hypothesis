import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappa

theorem fock_jets_moved : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt →
    ∀ f, IsVacO ψ θ S T sS sT (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f →
    ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt ∧ Θ ≠ 0 ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ Ls Lt hLs hLt f hf
  have hsS := GlobalTheory.FockPos.cart_one frS hS hcS
  have hsT := GlobalTheory.FockPos.cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := _root_.GlobalTheory.FockPos.vacuum_real_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := _root_.GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved ψ θ S T frS frT hS hT δ hC hδ Ls Lt hLs hLt f hf Φ hΦd hreal
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  refine ⟨Θ, hTh, ?_, fun k => ?_⟩
  · intro h0
    obtain ⟨w, hw, hfw⟩ := _root_.GlobalTheory.VacNonzeroReal.exists_finPart_zero_ne ψ θ S T _ _ _ _ f hf
    apply hfw
    have h1 : Φ (GlobalTheory.FockPos.zCo θ frS frT w) = 0 := by
      rw [hΦeq]
      exact congrFun h0 _
    rw [hreal w hw, h1, mul_zero]
  · have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := _root_.GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f
      (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
      GlobalTheory.FockPos.taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
        δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) {G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (hG : Differentiable ℂ G) (a : ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (fun z => a * G z) =
      a * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G := by
  rw [GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.ProdThetaConj.taylor_const_mul hG]
  ring

theorem intertwining_mem_ne_zero {D : D7} {δ t0 : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ)
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0) {N N' : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (he0 : Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : Formalism.MainNotions.StandardLatticesGL3.SD D L) (hL' : Formalism.MainNotions.StandardLatticesGL3.SD D L') {Θ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (hΘ : Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') (hΘ0 : Θ ≠ 0) :
    ∃ κ : ℂ, Θ = (fun z => κ * Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0 z) ∧
      Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0) := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') 0 = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK δ t0 hC ht) hn.symm
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D N, GlobalTheory.NormSum.VacInt.sd_std D N', rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') :=
    Or.inr ⟨L, L', hL, hL', rfl⟩
  have hne : ∃ z, Θ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΘ0 (funext h)
  have hS := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_ne_zero _ hΘ hne
  have hI := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Iop_mem_ThSp _ hS he0.1
  have hI0 : Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0 ≠ 0 := by
    intro h0
    obtain ⟨-, -, hself, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK δ hC N N'
    obtain ⟨μ, hμ⟩ := htrip _ _ _ hK1 hK2 hK1 e0 he0.1 he0ne
    have h1 := hμ.2.2.2.2.2.2.2.2.2
    have hμ8 := hμ.2.2.2.2.2.2.2.2.1
    rw [h0, GlobalTheory.NormSum.VacMove.iop_zero, hself _ hK1 e0 he0.1] at h1
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      norm_num at hμ8
    apply he0ne
    funext z
    have := congrFun h1 z
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hμ0
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG D.host.ccK δ hC N N' _ hK2).1 Θ hΘ _ hI hI0
  exact ⟨c, hc, hI.1⟩

end GlobalTheory.MovedKappa
