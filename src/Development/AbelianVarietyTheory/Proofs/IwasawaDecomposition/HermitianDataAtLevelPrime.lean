import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hI hP l Z H F hS hC
  have hseen := _root_.GlobalTheory.Mem.Col2.HAt.seenCl_atT I hI hP l Z H F hS hC
  have hdisc := GlobalTheory.T.dual_mod_class_lattice_equiv_quotient I hI hP l Z H F hS hC
  have hlvc := _root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hI hP l Z H F hS hC
  have hstab := _root_.GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied I hI hP l Z H F hS hC
  choose upG hup using _root_.GlobalTheory.Mem.Col2.HAt.UpMove.up_move I hI hP l Z H F hS hC
  choose dnG hdn using _root_.GlobalTheory.Mem.Col2.HAt.dn_move_exists I hI hP l Z H F hS hC
  choose dilG hdil using _root_.GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side I hI hP l Z H F hS hC
  choose lattice₂ levP clsP hcar hlat using _root_.GlobalTheory.Mem.Col2.HAt.clsP_hermitian I hI hP l Z H F hS hC
  let A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u) := fun u =>
    mkAtT (F u).atT (F u).lv (hC.eV u) (hC.fv u) (hseen u) (hdisc u) (upG u) (fun i hi v c y h => (hup u i v c y hi h).1)
      (dnG u) (fun i hi v c g h => (hdn u i v c g hi h).1) (dilG u) (fun i hi v a c => (hdil u i v a c hi).1)
      (lattice₂ u) (levP u) (clsP u) (F u).til (hlat u)
  have hT : CarT H F A := by
    refine ⟨fun _ => rfl, fun _ => rfl, hcar, hlat, ?_, ?_, ?_, ?_, ?_⟩
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prkH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i h1 h2 v c z z' h
      refine ((hlvc u i h1 h2 v c).1 (toLd i (le_of_succ_m h2) c z) z' h).trans (prH_eq (F u).atT (F u).lv (le_of_succ_m h2) v c z).symm
    · intro u
      exact ((crdN (I.rec7 l Z) _ le_rfl).apply_symm_apply _).symm
    · intro u c
      exact (reGL_lin _ (rankN (I.rec7 l Z) _ le_rfl) _).symm
  refine ⟨A, hT, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hstab A hT⟩
  · intro u v c y h
    exact (hup u 0 v c y (Nat.zero_le _) h).2
  · intro u i h1 hm v c y h
    cases i with
    | zero => omega
    | succ i => exact (hup u (i + 1) v c y hm h).2 hm
  · intro u v c g h
    exact (hdn u 0 v c g (Nat.zero_le _) h).2
  · intro u i h1 hm v c g h
    cases i with
    | zero => omega
    | succ i => exact (hdn u (i + 1) v c g hm h).2 hm
  · intro u v a c
    exact (hdil u 0 v a c (Nat.zero_le _)).2
  · intro u i h1 hm v a c
    cases i with
    | zero => omega
    | succ i => exact (hdil u (i + 1) v a c hm).2 hm
