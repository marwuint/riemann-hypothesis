import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

open GlobalTheory.ChainOnto (Com PiLocalization₂)

def RapidVal (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    ∀ G ∈ MultT θ M J χ, ∀ v, RapidDec V (G v)

def ValMove (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    (∀ G ∈ MultT θ M J χ, ∀ v, ∀ k ∈ J, rTrans k (G v) = χ k • G v) ∧
    ∀ a ∈ GinfC V, ∀ v, ∃ w, ∀ G ∈ MultT θ M J χ, rTrans a (G v) = G w

def PerSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (f : GA D B.V → ℂ), IsContAut B.V f →
    ∀ (I : Type) (s : Finset I) (a : I → ℂ) (φ : I → GA D B.A → ℂ), (∀ i ∈ s, IsContAut B.A (φ i)) →
      B.per ψ (∑ i ∈ s, a i • φ i) f = ∑ i ∈ s, a i * B.per ψ (φ i) f

def LiftSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is →
    ∀ k : KerDat S T, k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧
      (∀ φ, IsContAut S φ → IsContAut T (k.lift ψ θ x y P φ)) ∧
      ∀ (I : Type) (s : Finset I) (a : I → ℂ) (φ : I → GA D S → ℂ), (∀ i ∈ s, IsContAut S (φ i)) →
        k.lift ψ θ x y P (∑ i ∈ s, a i • φ i) = ∑ i ∈ s, a i • k.lift ψ θ x y P (φ i)

namespace Dat

end Dat

def CenFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is →
    ∀ k : KerDat S T, k.Is ψ θ x y → ∀ χ : GA D S → ℂ, ∃ W : Submodule ℂ (PolF D T.rank S.rank), FiniteDimensional ℂ W ∧
      ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f →
        (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → k.om (z, 1) f = χ z • f) →
        ∃ P ∈ W, f = pureTensorO ψ θ S T x.s y.s x.B y.B k.vac P

end GlobalTheory.SeeSaw

end
