import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.GalLoc.PsiLvl

def PsiRead (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i true ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
        (D.ntw.emb0 i ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0))

theorem exists_theta_of_eq {D₀ : D7} {L : LocAll (lay0 D₀)} {D' : D7} (h : D' = withLoc L)
    (θ0 : ∀ kk : Fin 2, Multiplicative (ZMod ((withLoc L).host.g kk)) →* (↥(withLoc L).LL0)ˣ)
    (h0 : PsiRead (withLoc L) θ0) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ, HEq θ θ0 ∧ PsiRead D' θ := by
  subst h
  exact ⟨θ0, HEq.rfl, h0⟩

end GlobalTheory.GalLoc.PsiLvl
