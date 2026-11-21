import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

def RealSide.ofPins {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (p : GlobalTheory.Mem.R3.Pins R F cG)
    (h : GlobalTheory.Mem.R3.Holds R F) (g : GlobalTheory.RealGeo.InGeo geo) (f : Finite T) (hh : HostHyp D) (s : ∀ j, FWT.VStd D j)
    (z : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) : RealSide D :=
  { Γ := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, core := C, R := R, F := F, cG := cG, geo := geo,
    char := RealDat3.characterisation_of_weak p.char h.aux.ex, phs := p.phs, guard := p.keep.guard, valKs := p.keep.valKs,
    idem := by obtain ⟨_, _, _, h2, _⟩ := p.keep.grp; exact h2
    unif := h.prim.unif, integral := h.aux.integral, inGeo := g, finT := f, host := hh, std := s, size := z }

end GlobalTheory.TwInputs

end
