import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
import ReciprocityTheory.SemistableReduction.AlgAll

noncomputable section

namespace GlobalTheory.TrivOrderTieCompare

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isClopen_comp (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have hZ : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  obtain ⟨z, hz⟩ := hZ.nonempty
  have h1 : (Z : Set (Xo.XF c)) ⊆ connectedComponent z :=
    hZ.isConnected.isPreconnected.subset_connectedComponent hz
  have h2 : IsIrreducible (connectedComponent z) :=
    ⟨⟨z, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth (strK (Xo := Xo) (c := c)) z⟩
  rw [Set.Subset.antisymm h1 (Z.2.2 h2 h1)]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace z⟩

variable [Fintype (Comp Xo c)]

end GlobalTheory.TrivOrderTieCompare
