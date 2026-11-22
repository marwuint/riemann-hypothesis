import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGeneric

theorem mem_of_dense_of_maximal {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {x : X}
    (hx : ∀ y, y ⤳ x → x ⤳ y) {U : Set X} (hU : IsOpen U) (hd : Dense U) : x ∈ U := by
  obtain ⟨o, ho, hne, hs⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨y, hyo, hyU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have e := hx ξ (hξ.specializes mem_irreducibleComponent)
  exact (e.trans (hξ.specializes (hs hyo))).mem_open hU hyU

end GlobalTheory.TraitGeneric
