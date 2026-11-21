import Mathlib
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.InfiniteQAtOfIs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.GeoInhab
open GlobalTheory.FinPl (SplitPt latV idAt intAt Lat Pl)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt qOf)
open GlobalTheory.SymBridge (IsOrd zPos xPos IsCompl)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsUnif)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem int_dense {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  have pe : ∀ x, q.pr (q.e * x) = q.pr x := fun x => by rw [← q.sec_pr, q.pr_sec]
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pe, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pe]

theorem xi_unit (hu : q.UnitAA) : valuation k (ofSplit q).xi = 1 := by
  have he := (DblInhab.sec_mem_intAt q 1).2 (map_one _).le
  obtain ⟨h1, h2⟩ := hu.1 _ he
  have h3 := DblInhab.pr_le_one q h1
  have h4 := DblInhab.pr_le_one q h2
  rw [map_mul, q.pr_sec, mul_one] at h3 h4
  change valuation k ((q.pr.comp (incA D)) _) ≤ 1 at h4
  rw [map_inv₀, map_inv₀] at h4
  exact le_antisymm h3 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Witness.xi_ne (ofSplit q))))).1 h4)

theorem exists_char (hu : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ ψk, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  have hx := Witness.xi_ne (ofSplit q)
  have hv := xi_unit q hu
  have h1 : q.IsChar ψ (ψk.mulShift (ofSplit q).xi⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, hk]
    change psiE ψ (incA D D.host.xi0 * q.sec _) = _
    rw [mul_comm (incA D _), ← DblInhab.sec_mul_pr]
    change psiE ψ (q.sec (_ * (ofSplit q).xi)) = _
    rw [mul_comm, mul_inv_cancel_left₀ hx]
  have h2 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ _ hψ h1 hu
  refine ⟨ψk, hk, fun x => (Iff.trans ⟨fun h y hy => ?_, fun h y hy => ?_⟩ (h2 x))⟩
  · exact h _ (by simpa [hv] using hy)
  · have := h ((ofSplit q).xi * y) (by simpa [hv] using hy)
    rwa [AddChar.mulShift_apply, inv_mul_cancel_left₀ hx] at this

end Place

variable {D : D7}

end GlobalTheory.QTw.GeoInhab
end
