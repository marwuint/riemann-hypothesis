import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixglobA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemOfStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegWLocalFunctionsThetaPureTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaSecond

noncomputable section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TopFlip

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)

theorem pureT_smul {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {s ξ ξ' : ∀ i, N i}
    (h : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ) (h' : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ') {c : ι → ℂ} (hc : (Function.mulSupport c).Finite)
    (e : ∀ i, ξ' i = c i • ξ i) : GlobalTheory.SmallThetaModules.pureT s ξ' = (∏ᶠ i, c i) • GlobalTheory.SmallThetaModules.pureT s ξ := by
  apply Subtype.ext
  rw [Submodule.coe_smul, GlobalTheory.SmallThetaModules.coe_pureT h, GlobalTheory.SmallThetaModules.coe_pureT h']
  funext l
  simp only [GlobalTheory.SmallThetaModules.evFam, Pi.smul_apply, smul_eq_mul, e, map_smul]
  exact finprod_mul_distrib hc (GlobalTheory.SmallThetaModules.mulSupport_fin h l)

variable {D : D7}

end GlobalTheory.TopFlip

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem pureT_loc (hL : L.Is μ₀) {t : T} {i j : ℕ} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} {om om' R Rf} (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf) (hti : IsTied t i j e Bs Γ X)
    {φ φ'} (h : IsFinPart Γ.M X.T φ) (h' : IsFinPart Γ.M' X.T φ') {c : Pl D.host.E → ℂ}
    (hc : ∀ w ∈ locPl G t, Rf.p _ (φ (w.under (𝓞 D.host.F))) = c w • Rf.p' _ (φ' (w.under (𝓞 D.host.F)))) :
    (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p v (φ v)) =
      (∏ w ∈ locPl G t, c w) • GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (φ' v) := by
  classical
  let c' : Pl D.host.F → ℂ := fun v => ∏ w ∈ locPl G t with w.under (𝓞 D.host.F) = v, c w
  have h1 : ∀ v, v ∉ X.T → c' v = 1 := fun v hv => Finset.prod_eq_one fun w hw => by
    obtain ⟨a, b⟩ := Finset.mem_filter.1 hw
    exact absurd ((hti.2.2.1 v).2 ⟨w, a, b⟩) hv
  have hs : Function.mulSupport c' ⊆ X.T := fun v hv => by_contra fun h => hv (h1 v h)
  rw [pureT_smul (s := GlobalTheory.TripleAssembly.vacIm Γ Rf) (ξ := fun v => Rf.p' v (φ' v)) (ξ' := fun v => Rf.p v (φ v)) (c := c') (X.T.finite_toSet.subset fun v hv => by_contra fun hn => hv (by
      exact (congrArg (Rf.p' v) (h'.2 v hn)).trans (hm.fin.sph v hn).1.symm))
    (X.T.finite_toSet.subset fun v hv => by_contra fun hn => hv (congrArg (Rf.p v) (h.2 v hn))) (X.T.finite_toSet.subset hs) fun v => ?_,
    finprod_eq_prod_of_mulSupport_subset _ hs,
    Finset.prod_fiberwise_of_maps_to fun w hw => (hti.2.2.1 _).2 ⟨w, hw, rfl⟩]
  by_cases hv : v ∈ X.T
  · obtain ⟨w, hw, rfl⟩ := (hti.2.2.1 v).1 hv
    have : c' (w.under (𝓞 D.host.F)) = c w := Finset.prod_eq_single_of_mem w (Finset.mem_filter.2 ⟨hw, rfl⟩)
      fun w' hw' hne => absurd (Good.under_injOn hL G t (Finset.mem_filter.1 hw').1 hw (Finset.mem_filter.1 hw').2) hne
    rw [this, hc w hw]
  · rw [h1 v hv, one_smul, h.2 v hv, h'.2 v hv, (hm.fin.sph v hv).1]

end GlobalTheory.TopFlip

end
