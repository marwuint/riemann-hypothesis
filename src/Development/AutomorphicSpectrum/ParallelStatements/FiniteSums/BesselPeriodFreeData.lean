import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.UnfDefs
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi
  Formalism.IndefR.Mult MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData

variable {D : D7}

def rho (D : D7) (j : ℕ) : ℕ := (D.R.m - 1 - j) / 2

def HasZ (D : D7) (j : ℕ) : Prop := (D.R.m - 1 - j) % 2 = 1

structure SlopeTestRemainingChoices (V : HSp D) where
  e : ℕ → Fin V.rank → D.host.E
  ev : ℕ → Fin V.rank → D.host.E
  z : Fin V.rank → D.host.E

def Rgrp (V : HSp D) (j : ℕ) (A : SlopeTestRemainingChoices V) : Subgroup (GA D V) :=
  Subgroup.closure {g | (∀ i < rho D j, ∃ a : ℕ → AE D,
      subOne V g *ᵥ ratV (A.e i) = ∑ l ∈ Finset.range i, a l • ratV (A.e l)) ∧
    (HasZ D j → ∃ a : ℕ → AE D, subOne V g *ᵥ ratV A.z = ∑ l ∈ Finset.range (rho D j), a l • ratV (A.e l))}

def xZero (V : HSp D) (j : ℕ) (A : SlopeTestRemainingChoices V) : Mx D V.rank (rho D j) :=
  fun r i => incA D (if Odd (j + 1) then D.host.xi0⁻¹ * A.e i r else if i.1 < rho D (j + 1) then A.e i r else A.z r)

def parPi (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : SPar :=
  Finset.univ.image fun i : Fin D.R.k => ((D.hcW u τ).u i, true)

abbrev Ginf (D : D7) (j : ℕ) : Type := GinfC (D.sp.Y j)

structure RealData (D : D7) (u : D.what₂.Word) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  η : (AE D)ˣ →* Circle
  aux : ∀ j, SlopeTestRemainingChoices (D.sp.Y j)
  s : ∀ j, D.what₂.Tau → Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) ℂ
  B : ∀ j, D.what₂.Tau → Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) ℂ
  npos : ℕ → D.what₂.Tau → ℕ
  Mπ : DSModel (D.sp.X 0) (parPi D u)
  Mσ : DSModel (D.sp.Y D.R.m) (parB (tparRec D) D.R.m)
  ν : ∀ j, Measure (Ginf D j)
  μR : ∀ j, Measure ((Rgrp (D.sp.Y j) j (aux j)).subgroupOf (GinfC (D.sp.Y j)))
  β : ∀ j, Ginf D j → ℝ

variable {u : D.what₂.Word}

structure RealVec (R : RealData D u) where
  v : ⨂[ℂ] τ, R.Mπ.H τ
  P : ∀ j, MvPolynomial (FVar D (D.sp.Y (j + 1)).rank (D.sp.Y j).rank) ℂ
  vt : ⨂[ℂ] τ, R.Mσ.H τ

structure FreeData (R : RealData D u) where
  Y : ℕ → HSp D
  X0 : HSp D
  ι : X0.V →ₗ[D.host.E] (Y 0).V
  aux : ∀ j, SlopeTestRemainingChoices (Y j)
  κ : ∀ j, D.what₂.Tau → Matrix (Fin (Y j).rank) (Fin (D.sp.Y j).rank) ℂ
  κ' : ∀ j, D.what₂.Tau → Matrix (Fin (D.sp.Y j).rank) (Fin (Y j).rank) ℂ
  κX : D.what₂.Tau → Matrix (Fin X0.rank) (Fin (D.sp.X 0).rank) ℂ
  κX' : D.what₂.Tau → Matrix (Fin (D.sp.X 0).rank) (Fin X0.rank) ℂ
  tr : ∀ j, Ginf D j →* GinfC (Y j)
  μ : ℕ → (AE D)ˣ →* Circle
  om : ∀ j, GA D (Y j) × GA D (Y (j + 1)) →* Module.End ℂ (WO (Y j) (Y (j + 1)) → ℂ)
  vac : ∀ j, WO (Y j) (Y (j + 1)) → ℂ
  ph : MultilinearMap ℂ (fun τ => R.Mπ.H τ) (GA D X0 → ℂ)
  Ft : MultilinearMap ℂ (fun τ => R.Mσ.H τ) (GA D (Y D.R.m) → ℂ)
  bes : BesDat X0 (Y 0) ι
  emb : GA D X0 →* GA D (Y 0)
  μ0 : Measure (GA D X0)
  𝓕0 : Set (GA D X0)
  μN : Measure (NFlag (Y 0) bes.e)
  𝓕N : Set (NFlag (Y 0) bes.e)
  νf : ∀ j, Measure (GfC (Y j))
  μRf : ∀ j, Measure ((Rgrp (Y j) j (aux j)).subgroupOf (GfC (Y j)))
  βf : ∀ j, GfC (Y j) → ℝ
  𝓕Y : ∀ j, Set (GA D (Y j))
  𝓕R : ∀ j, Set (GA D (Y j))
  μL : ∀ j, Measure (Mx D (Y (j + 1)).rank (rho D j))
  𝓕L : ∀ j, Set (Mx D (Y (j + 1)).rank (rho D j))

namespace FreeData

end FreeData

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData

end
