import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChtTrueYEta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EvlTrueIncTInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FibLatPreSubSpanSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def IsHTLatOf {ct : At S κ p} (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (B : ct.Mdl) (L : Lat B) : Prop :=
  (∃ n, 3 ≤ n ∧ hm.IsHTBlowup B (ct.Xn n)) ∧ ∀ y : ct.Pt B,
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing
    hm.omPat y = (GlobalTheory.HTSheaf.fibLat (ct.isGrpPullback_htToMdl y) L.N).toAddSubgroup

end GlobalTheory.LocM
