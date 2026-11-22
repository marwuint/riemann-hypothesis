import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ApolarMonomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NatToBEquivariant
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

variable (D) in

def sideEmb (σ : PsiT D × Bool) : D.host.E →+* ℂ :=
  if σ.2 then conjEmb (DV.tauEmb D (D.eTau.symm σ.1)) else DV.tauEmb D (D.eTau.symm σ.1)

section Fields

attribute [local irreducible] RayEv.kapGt RayEv.kapB RayEv.resB RayEv.incT RayEv.LieGt RayEv.LieB RayEv.LieT At.dat sideEmb

variable (ct : At S κ p) (y : ct.Pt ct.Xm) (σ : PsiT D × Bool)

end Fields

end GlobalTheory.LocM
