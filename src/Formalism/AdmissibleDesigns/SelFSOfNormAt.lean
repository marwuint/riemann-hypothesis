import Formalism.AdmissibleDesigns.FirstBlockColumnCondition
import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
import Formalism.AdmissibleDesigns.ToH1Cocycles

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StB

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Rho2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem selFS_of_normAt (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc))
      (rowsN i dc) (FS i r π dc g0 eB e₁ s Dd hD hc 0) (QS.Io i) := by
  letI := fun w => modS i r π dc g0 eB e₁ s Dd hD hc w
  haveI := fun w => KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w
  letI := fun w => modS' i r π dc g0 eB e₁ s Dd hD hc w
  haveI := fun w => KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w
  exact Bk.tieSel1_K i dc Dd (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc) hD hN

end Rho2

end Formalism.MainNotions.N.K.StB

end
