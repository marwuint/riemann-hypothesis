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

open Classical in

def evlTrue (ct : At S κ p) : EvlSt ct :=
  letI : Fintype (PsiT D) := Fintype.ofEquiv _ D.eTau
  { LieGt := fun y σ => RayEv.LieGt (ct.dat y) (sideEmb D σ)
    LieB := fun y σ => RayEv.LieB (ct.dat y) (sideEmb D σ)
    LieT := fun y σ => RayEv.LieT (ct.dat y) (sideEmb D σ)
    lgAdd := fun _ _ => inferInstance
    lbAdd := fun _ _ => inferInstance
    ltAdd := fun _ _ => inferInstance
    resB := fun y σ => (RayEv.resB (ct.dat y) (sideEmb D σ)).toAddMonoidHom
    incT := fun y σ => (RayEv.incT (ct.dat y) (sideEmb D σ)).toAddMonoidHom
    kapGt := fun y σ => RayEv.kapGt (ct.dat y) (sideEmb D σ)
    kapB := fun y σ => RayEv.kapB (ct.dat y) (sideEmb D σ)
    Harm := fun y => RayEv.HarmAt (ct.dat y) (sideEmb D)
    SecP := fun y => RayEv.SecAt (ct.dat y)
    evA := fun _ Q s => Q.evA s
    evGt := fun _ Q s => Q.evGt s }

section Fields

attribute [local irreducible] RayEv.kapGt RayEv.kapB RayEv.resB RayEv.incT RayEv.LieGt RayEv.LieB RayEv.LieT At.dat sideEmb

variable (ct : At S κ p) (y : ct.Pt ct.Xm) (σ : PsiT D × Bool)

theorem evlTrue_resB (u : RayEv.LieGt (ct.dat y) (sideEmb D σ)) :
    (evlTrue ct).resB y σ u = RayEv.resB (ct.dat y) (sideEmb D σ) u := rfl

theorem evlTrue_incT (u : RayEv.LieT (ct.dat y) (sideEmb D σ)) :
    (evlTrue ct).incT y σ u = RayEv.incT (ct.dat y) (sideEmb D σ) u := rfl

theorem evlTrue_kapGt : (evlTrue ct).kapGt y σ = RayEv.kapGt (ct.dat y) (sideEmb D σ) := rfl

theorem evlTrue_kapB : (evlTrue ct).kapB y σ = RayEv.kapB (ct.dat y) (sideEmb D σ) := rfl

end Fields

end GlobalTheory.LocM
