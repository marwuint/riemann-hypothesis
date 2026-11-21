import Formalism.AdmissibleDesigns.SelmerInequalityOfInputs
import Formalism.AdmissibleDesigns.TheoremN5OfNormalizedItems
import Formalism.AdmissibleDesigns.DesignNormalizedOfAdmitted

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.St

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Places

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem col_not_row (l : Col i dc) : colIdx i dc l ∉ rowsN i dc := by
  intro h
  simp only [rowsN, colIdx, Finset.mem_image] at h
  obtain ⟨v, hv, hvi⟩ := h
  have hl : (l : HeightOneSpectrum (𝓞 D.host.E)) ∈ dc.col := l.2
  have hvl : v = l := idx_inj i dc (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
    (Finset.mem_union_left _ (Finset.mem_union_right _ hl)) hvi
  subst hvl
  exact Finset.disjoint_left.1 dc.disj hv hl

theorem row_not_q (w : ℕ) (hw : w ∈ rowsN i dc) : w ∉ qsN i dc := by
  intro hq
  simp only [rowsN, qsN, Finset.mem_image] at hw hq
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨u, hu, huv⟩ := hq
  have huv' : u = v := idx_inj i dc (Finset.mem_union_right _ hu)
    (Finset.mem_union_left _ (Finset.mem_union_left _ hv)) huv
  subst huv'
  exact D.nd.SQ_l i u (Or.inr hu) ((dc.cover u).1 (Or.inl hv))

end Places

end Formalism.MainNotions.N.K.St

end
