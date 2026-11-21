import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.PassOp

open Formalism.MainNotions.N.PlaceLabelTeichmuller

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem prod_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (L : List ι) (hL : L.Nodup) :
    (L.map fun i => plc i (a i)).prod = tens (fun j => if j ∈ L then a j else 1) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]
    exact tens_one.symm
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, plc, tens_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hL.1]
    · simp [Function.update_of_ne hj, hj]

end Tensor

local instance factGk (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroGk (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem tw_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).1)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    (L : List (Part D.naut.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, D.naut.tw (D.naut.tw p.π D.naut.etaT) D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ::
      twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)), tw_eta D hT hAN (hL p List.mem_cons_self)]

theorem goodPar_iff_goodSig (D : D7) (Sig : List (Part D.naut.CG)) (σ' : D.ntypes.Par)
    (h1 : ∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) :
    D.ntypes.goodPar σ' ↔ goodSig D.nd D.naut Sig := by
  unfold NTypes.goodPar NTypes.goodTuple goodSig
  simp only [D.ntypes.labPar_def, h1]

end GlobalTheory.PassOp

end
