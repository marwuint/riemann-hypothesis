import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev InvFam (V : HSp D) : Type := D.what₂.Tau → Module.End D.host.E V.V

def thAt (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (LinearMap.toMatrix V.frame V.frame s).map (tauE D τ)

def KAt (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ g * thAt V τ s = thAt V τ s * g}

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

theorem infMat_one (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem infMat_mul (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

def Kinf (θ : InfFam D) (V : HSp D) (s : InvFam V) : Subgroup (GA D V) where
  carrier := {g | g ∈ GinfC V ∧ ∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (thAt V τ (s τ))}
  one_mem' := ⟨one_mem _, fun τ => by rw [infMat_one]; exact Commute.one_left _⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem hg.1 hh.1, fun τ => by
    rw [infMat_mul]; exact (hg.2 τ).mul_left (hh.2 τ)⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun τ => by
    let u : (Matrix (Fin V.rank) (Fin V.rank) ℂ)ˣ :=
      ⟨infMat D.sp.cm.sig V.gram (θ τ) g, infMat D.sp.cm.sig V.gram (θ τ) g⁻¹,
        by rw [← infMat_mul, mul_inv_cancel, infMat_one], by rw [← infMat_mul, inv_mul_cancel, infMat_one]⟩
    exact Commute.units_inv_left (u := u) (hg.2 τ)⟩

abbrev WC (V W : HSp D) : Type := Matrix (Fin V.rank) (Fin W.rank) ℂ

def wAt (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) : WC V W :=
  x.map fun a => θ τ (infPart D a)

def actC (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : WC V W) : WC V W :=
  if V.rank ≤ W.rank then g.map (starRingEnd ℂ) * x * h.transpose
  else g * x * (h.map (starRingEnd ℂ)).transpose

def hC (V W : HSp D) (τ : D.what₂.Tau) (x y : WC V W) : ℂ :=
  if V.rank ≤ W.rank then
    ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * gramAt D V τ k i * gramAt D W τ j l * y k l
  else
    ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * gramAt D V τ i k * gramAt D W τ l j * y k l

def symplC (V W : HSp D) (τ : D.what₂.Tau) (x y : WC V W) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hC V W τ y x).re

def jAt (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V)
    (x : WC V W) : WC V W :=
  Complex.I • actC V W (thAt V τ s) (thAt W τ s') x

def IsRealLine (V W : HSp D) (L : ℝ →+ WA V W) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

def dHeis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  fun w => deriv (fun t : ℝ => Heisenberg₂ ψ V W (L t) f w) 0

def IsJPair (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) (L L' : ℝ →+ WA V W) : Prop :=
  IsRealLine V W L ∧ IsRealLine V W L' ∧
    ∀ t τ, wAt θ V W τ (L' t) = jAt V W τ (s τ) (s' τ) (wAt θ V W τ (L t))

def cre (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  dHeis ψ V W L f - Complex.I • dHeis ψ V W L' f

def ann (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  dHeis ψ V W L f + Complex.I • dHeis ψ V W L' f

def IsVacuum (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W)
    (f : WA V W → ℂ) : Prop :=
  IsThetaFun ψ V W f ∧ ∀ L L', IsJPair θ V W s s' L L' → ann ψ V W L L' f = 0

inductive IsFockMon (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    (WA V W → ℂ) → Prop
  | vac (f : WA V W → ℂ) : IsVacuum ψ θ V W s s' f → IsFockMon ψ θ V W s s' f
  | cre (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : IsJPair θ V W s s' L L' → IsFockMon ψ θ V W s s' f →
      IsFockMon ψ θ V W s s' (cre ψ V W L L' f)

def polFun (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    Submodule ℂ (WA V W → ℂ) :=
  Submodule.span ℂ {f | IsFockMon ψ θ V W s s' f}

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

end
