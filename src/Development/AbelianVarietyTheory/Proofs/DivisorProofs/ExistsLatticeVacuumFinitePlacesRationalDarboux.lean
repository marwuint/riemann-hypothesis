import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumOfHeisenbergLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticAddSelfExpansionHalfIdempotentStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LatVac

theorem exists_isVac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ M : Model σ X Y, (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ φ : (Fin n × Fin d → Fv F v) → ℂ, M.IsVac B.ψ v φ := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY M hrat v
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨hAt, hSt⟩ := GlobalTheory.LatVac.latAtV_at_stable X Y v
  obtain ⟨hO, hC⟩ := _root_.GlobalTheory.LatOpenCpt.main σ B X Y r s r' s' hX hY M hrat v
  have hint := GlobalTheory.T.standardAddChar_symplectic_local_lattice_eq_one σ B X Y r s r' s' hB hX hY v θ
  have h2 : GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (GlobalTheory.AdelicU.evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  let cc : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ)
  have hc0 : cc 0 = 1 := by simp [cc, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hcc : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      cc (γ + γ') = cc γ * cc γ' * B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') := by
    intro γ hγ γ' hγ'
    have e := GlobalTheory.T.traceSymplectic_add_self_expansion_half_idempotent σ B X Y r s r' s' hB hX hY (θ : E) hθ γ γ'
    have h1 := hint 1 (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
    rw [one_mul] at h1
    simp only [cc]
    rw [e]
    set a := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ
    set b := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ'
    set c := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ'
    set f := GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ'
    have : ⅟(2 : AF F) * (a + b + 2 * c + f) = ⅟(2 : AF F) * a + ⅟(2 : AF F) * b + ⅟(2 : AF F) * f + c := by
      have h22 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
      linear_combination c * h22
    rw [this, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, mul_one]
  have hc2 : ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, cc (GlobalTheory.LatVac.liftV v 2 • γ) = 1 := by
    intro γ hγ
    simp only [cc]
    rw [GlobalTheory.LatVac.symp_smul_smul, ← mul_assoc, ← mul_assoc]
    refine hint _ ?_ γ hγ γ hγ
    rw [map_mul, map_mul, GlobalTheory.LatVac.evFin_liftV, h2]
    simpa using (v.adicCompletionIntegers F).natCast_mem 2
  obtain ⟨φ, hφ, hφ0, hact⟩ := _root_.GlobalTheory.HeisLatVac.exists_vac_of_lattice M.co B.ψ v hB.std.1 (_root_.GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ hAt hSt hO hC
    cc hc0 hcc hc2
  exact ⟨φ, hφ, hφ0, θ, hθ, hact⟩

end GlobalTheory.LatVac
