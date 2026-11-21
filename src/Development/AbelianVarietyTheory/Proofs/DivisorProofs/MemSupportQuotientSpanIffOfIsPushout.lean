import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientIff
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.SupportBC

theorem mem_support_quotient_span_iff_of_isPushout :
    ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'),
      IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'),
      ((letI := qa'.hom.toAlgebra;
        p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra;
        PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first
  | exact @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | (apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff ..)

end GlobalTheory.SupportBC
