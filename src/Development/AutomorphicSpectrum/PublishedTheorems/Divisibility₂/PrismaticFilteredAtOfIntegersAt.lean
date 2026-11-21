import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SettingInhabited
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.CompanionTheory.Published

end GlobalTheory.CompanionTheory.Published

namespace GlobalTheory.CompanionTheory.Ar.Prism

open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich

section Proofs

open GlobalTheory.Dieudonne GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

omit [IsAdicComplete (span {(p : O)}) O] in

theorem frobenius_ofPadic_eq (c : ℤ_[p]) :
    (WittVector.frobenius (ofPadic p O c) : Ainf p O) = ofPadic p O c := by
  ext n
  rw [coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem exists_padic_of_eigen [IsDomain (PreTilt O p)] {ε : PreTilt O p}
    (hε : IsPrimitiveRoot (root ε).untilt p) {a : Ainf p O}
    (h : WittVector.frobenius a = WittVector.frobenius (xi ε) * a) :
    ∃ c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  let : Algebra ℤ_[p] (Ainf p O) := (ofPadic p O).toAlgebra
  have hs : ∀ (c : ℤ_[p]) (x : Ainf p O), c • x = ofPadic p O c * x := fun _ _ => rfl
  have : IsAdicComplete (span {(p : Ainf p O)}) (Ainf p O) := WittVector.isAdicCompleteIdealSpanP
  let N : Submodule ℤ_[p] (Ainf p O) :=
    { carrier := {a | WittVector.frobenius a = WittVector.frobenius (xi ε) * a}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb, mul_add]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [hs, map_mul, frobenius_ofPadic_eq, ha]; ring }
  let m : N := ⟨Sandwich.mu ε, frobenius_mu ε⟩
  suffices hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] N m) by
    obtain ⟨c, hc⟩ := hsurj ⟨a, h⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  refine TateFree.surjective_of_mod _ (fun y hy => ?_) (fun y => ?_)
  · refine Subtype.ext (IsHausdorff.haus' (I := span {(p : Ainf p O)}) _ fun n => ?_)
    obtain ⟨z, hz⟩ := hy n
    rw [SModEq.zero, ← hz, Ideal.span_singleton_pow, Submodule.coe_smul, hs, map_pow, map_natCast,
      ← smul_eq_mul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · obtain ⟨c, b, hc, hb⟩ := GlobalTheory.DieudonneTest.eigen_step hε y.2
    refine ⟨c, ⟨b, hb⟩, Subtype.ext ?_⟩
    change ofPadic p O p * b = y - ofPadic p O c * Sandwich.mu ε
    rw [map_natCast, map_intCast, hc]; ring

end Proofs

end GlobalTheory.CompanionTheory.Ar.Prism
