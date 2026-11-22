import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev l2 {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (φ₁ φ₂ : X → ℂ) : ℂ := Lift.pet μ 𝓕 φ₁ φ₂

abbrev Upq (W : HSp D) (ρ : D.what₂.Tau) : Type := UpqT (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2

abbrev Frames (W : HSp D) : Type :=
  ∀ ρ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D ρ)).1 ⊕ Fin (W.sig (tauE D ρ)).2) (Fin W.rank) ℂ

def IsFrames (W : HSp D) (A : Frames W) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * A ρ = gramAt D W ρ

def conjFrame {p q n : ℕ} (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q * b * A : Matrix (Fin n) (Fin n) ℂ)

def realMat (W : HSp D) (A : Frames W) (ρ : D.what₂.Tau) (b : Upq W ρ) : Matrix (Fin W.rank) (Fin W.rank) ℂ :=
  conjFrame (gramAt D W ρ) (A ρ) (UpqT.mat b)

def realElt (θ : Datum.InfFam D) (W : HSp D) (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : GA D W :=
  ((Finset.univ : Finset D.what₂.Tau).toList.map fun ρ => atTau θ W ρ (g ρ)).prod

abbrev FinCos (W : HSp D) (K : Subgroup (GA D W)) : Type := GfC W ⧸ K.subgroupOf (GfC W)

def FinCos.rep {W : HSp D} {K : Subgroup (GA D W)} (c : FinCos W K) : GA D W := (c.out : GfC W)

open Classical in

def quadSign (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ :=
  if (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 then 1 else -1

def quadTerm (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : ℕ) : ℝ :=
  quadSign D v ^ i / (Ideal.absNorm v.asIdeal : ℝ) ^ i

def dLoc (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ := ∏ i ∈ Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D v i)⁻¹

def dOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ℝ :=
  ∏' p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D p.1.1 p.2.1)⁻¹

def eulerOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ) : ℂ :=
  ∏' p : {w : HeightOneSpectrum (𝓞 D.host.E) // OffS D S w} × Fin D.R.r, (1 - x p.1.1 p.2)⁻¹

variable (D) in

def degAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ :=
  ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

abbrev levV (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    Subgroup (GL (Fin (Vc D i).rank) (Lev.EAf D)) := lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)

abbrev petW (i : Fin D.R.m) (F₁ F₂ : GA D (Wc D i) → ℂ) : ℂ := l2 (R.νW i) (R.fdW i) F₁ F₂

def upLift (i : Fin D.R.m) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (F : GA D (Wc D i) → ℂ) (h : GA D (Vc D i)) : ℂ :=
  petW R i (fun g => Datum.thetaKO ω h g φ) F

def IsLiftData (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  R.Char F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io

variable (D) in

def DeltaNorm : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) =
    ∏ ρ : D.what₂.Tau, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℂ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℂ))

variable (D) in

def MassLower : Prop :=
  ∀ i : Fin D.R.m, (Vc D i).IsPosDef → 1 / ((NumberField.Units.torsionOrder D.host.E : ℝ) ^ D.R.nV * (D.R.nV.factorial : ℝ)) ≤
    GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i))

end GlobalTheory.AdelicScalar

end
