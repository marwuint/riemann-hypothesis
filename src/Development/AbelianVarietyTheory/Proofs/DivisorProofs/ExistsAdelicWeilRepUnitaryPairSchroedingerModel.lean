import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepHermitianPairRationalSchrodinger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger

theorem exists_isWeil : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n d : ℕ) (X : Spc D.host.F D.host.E n) (Y : Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∀ χX χW : Chr D.host.F D.host.E, GlobalTheory.LFun.IsHecke D.host.F D.host.E χX → GlobalTheory.LFun.IsHecke D.host.F D.host.E χW →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d →
        ∃ om, Mo.IsWeil B.ψ χX χW om := by
  intro D B hB n d X Y r s r' s' hX hY Mo hMo χX χW hcX hcW rX rW
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.WeilSchrodingerHerm.main D B hB n X r s hX
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := _root_.GlobalTheory.WeilSchrodingerSkew.main D B hB d Y r' s' hY
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := hspOf D X.Jᵀ h1 h2 X.L hX.lat h3 (fun _ => (r, s))
  let S := hspOf D (-D.host.xi0 • Y.J⁻¹) h4 h5 L hL h6 (fun _ => (s', r'))
  have eA : X.J = T.gramᵀ := by rw [gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [gram_hspOf]
    have e1 : (-D.host.xi0 • Y.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Y.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Y.J = -Y.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • (-D.host.xi0 • Y.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [incM]
  exact _root_.GlobalTheory.WeilSchrodinger.exists_isUWeilPair_hsp D B.ψ (_root_.GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D B.ψ hB.std) S T χW χX hcW hcX (_root_.GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow D χW d rW) (_root_.GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow D χX n rX) X.J Y.J (-1) eA eB
    (Fin n × Fin d) Mo.co hMo.rat

end GlobalTheory.WeilSchrodinger

end
