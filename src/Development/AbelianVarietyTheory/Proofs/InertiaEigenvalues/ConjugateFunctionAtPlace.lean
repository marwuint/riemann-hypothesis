import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumKeepingLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)

theorem GlobalTheory.PlaceRead.evaluates_of_lunif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : Formalism.L2.Pj.CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl

