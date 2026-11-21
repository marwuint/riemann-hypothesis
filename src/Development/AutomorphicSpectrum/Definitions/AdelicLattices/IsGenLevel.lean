import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.DownChainSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup GlobalTheory.CompanionTheory.Sep
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.UnitaryDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Place

variable {r n : ℕ}

structure IsAdapted (ε : Fin r → Bool) (ε' : Fin n → Bool) (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  rank : r + 1 = n
  orth : ιᴴ * ι = 1
  perp : ιᴴ *ᵥ z = 0
  unit : star z ⬝ᵥ z = 1
  form : Formalism.REAL.Jm ε' * ι = ι * Formalism.REAL.Jm ε
  formz : Formalism.REAL.Jm ε' *ᵥ z = z

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

end Place

section Adelic

variable {D : D7} (θ : InfFam D) {Y V : HSp D} {SY SV : D.what₂.Tau → SPar}

variable (d : HermitianOrthogonalExtensionData Y V 1 1)

def zVec : Fin V.rank → D.host.E := fun i => d.a i 0

def latV (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  d.lat Λ fun _ => 1

def iotaAt (MY : DSModel Y SY) (MV : DSModel V SV) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin Y.rank) ℂ :=
  MV.fr τ * (frameMat V Y d.ι).map (tauE D τ) * (MY.fr τ)⁻¹

def zAt (MV : DSModel V SV) (τ : D.what₂.Tau) : Fin V.rank → ℂ := MV.fr τ *ᵥ fun i => tauE D τ (zVec d i)

structure Std (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) (MY : DSModel Y SY) (MV : DSModel V SV) : Prop where
  fam : IsInfFam θ
  sigY : Y.SigOK
  sigV : V.SigOK
  sdY : IsSelfDualC Y Λ
  sdV : IsSelfDualC V (latV d Λ)
  adapted : ∀ τ, IsAdapted (MY.ε τ) (MV.ε τ) (iotaAt d MY MV τ) (zAt d MV τ)

structure RowOK (MY : DSModel Y SY) (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) (g : ℕ) (J : Set (GA D Y))
    (χ : GA D Y → ℂ) (w : MY.Vec) (u : GA D Y → ℂ) : Prop where
  val : ∃ t : MMap MY, IsMultMap θ MY J χ t ∧ u = t w
  ne : u ≠ 0
  bdd : ∃ N : ℝ, ∀ x, ‖u x‖ ≤ N
  pos : 1 ≤ g
  lev : ∀ k ∈ Lev.levA Y (congLev D.sp.cm Y.gram Λ (Ideal.span {(g : 𝓞 D.host.E)})), ∀ x, u (x * k) = u x

end Adelic

end GlobalTheory.CompanionTheory.UnitaryDecomposition

end
