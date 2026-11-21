import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped TensorProduct NNReal Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def blocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def blockIdx (n : ℕ) (i : Fin (n + n)) : ℕ := if (i : ℕ) < n then 0 else 1

variable (D : D7)

def skewJ (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E := blocks 0 1 (-1) 0

abbrev UA {k : ℕ} (T : Matrix (Fin k) (Fin k) D.host.E) : Type := AdelicU.GAd D.sp.cm.sig T

abbrev GG (n : ℕ) : Type := UA D (skewJ D n)

variable {D}

def mat {k : ℕ} {T : Matrix (Fin k) (Fin k) D.host.E} (g : UA D T) : Matrix (Fin k) (Fin k) (AE D) :=
  (AdelicU.matHom (AF D.host.F) D.sp.cm.sig T g).1

def mmul {k l r : ℕ} (x : Mx D k l) (y : Mx D l r) : Mx D k r := HMul.hMul x y

def adj {k l : ℕ} (x : Mx D k l) : Mx D l k := Formalism.UG.cT (cA D) x

variable (D)

def siegel (n : ℕ) : Subgroup (GG D n) where
  carrier := {g | (mat g).BlockTriangular (blockIdx n)}
  one_mem' := by
    change (mat (1 : GG D n)).BlockTriangular _
    rw [mat, map_one]; exact Matrix.blockTriangular_one
  mul_mem' := fun {g h} hg hh => by
    change (mat (g * h)).BlockTriangular _
    rw [mat, map_mul]; exact Matrix.BlockTriangular.mul hg hh
  inv_mem' := fun {g} hg => by
    change (mat g⁻¹).BlockTriangular _
    rw [mat, map_inv, Matrix.coe_units_inv]
    letI := (AdelicU.matHom (AF D.host.F) D.sp.cm.sig (skewJ D n) g).invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

abbrev rat {k : ℕ} (T : Matrix (Fin k) (Fin k) D.host.E) : Subgroup (UA D T) := AdelicU.ratPts D.sp.cm.sig T

def Cosets (n : ℕ) : Type := Quotient (QuotientGroup.rightRel ((siegel D n).subgroupOf (rat D (skewJ D n))))

variable {D}

def Cosets.rep {n : ℕ} (c : Cosets D n) : GG D n := (Quotient.out c : rat D (skewJ D n))

def absDet {n : ℕ} (a : GL (Fin n) (AE D)) : ℝ≥0 :=
  Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a)

section Space

variable {m n : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E)

def wittIdx : ℕ :=
  sSup {r | ∃ W : Submodule D.host.E (Fin m → D.host.E),
    (∀ x ∈ W, ∀ y ∈ W, hE D.sp.cm.sig T x y = 0) ∧ Module.finrank D.host.E W = r}

def gramQ (x y : Mx D m n) : Mx D n n :=
  mmul (mmul (adj x) (T.map (incA D))) y

def trA (z : AE D) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) z

def quadTr (b : Mx D n n) (x : Mx D m n) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (Matrix.trace (mmul b (gramQ T x x)))

def pairing (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) : ℂ := ψ (trA (Matrix.trace (gramQ T x y)))

end Space

abbrev Sch (θ : InfFam D) (m n : ℕ) : Type := ModerateGrowthSchwartz.schwartzA θ m n

abbrev Rep (θ : InfFam D) (n : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E) : Type :=
  GG D n × UA D T →* Module.End ℂ (Sch θ m n)

section Weil

variable {θ : InfFam D} {m n : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E}

structure IsWeil (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : Rep θ n T) : Prop where

  levi : ∀ (g : GG D n) (a : GL (Fin n) (AE D)), mat g = blocks a.1 0 0 (adj (a⁻¹).1) → ∀ (Φ : Sch θ m n) (x : Mx D m n),
    (ω (g, 1) Φ).1 x = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * ((((absDet a : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) *
      Φ.1 (mmul x a.1)

  unip : ∀ (g : GG D n) (b : Mx D n n), mat g = blocks 1 b 0 1 → ∀ (Φ : Sch θ m n) (x : Mx D m n),
    (ω (g, 1) Φ).1 x = ψ (quadTr T b x) * Φ.1 x

  weyl : ∀ g : GG D n, mat g = blocks 0 1 (-1) 0 → ∀ μ : Measure (Mx D m n), SelfDual μ (pairing T ψ) →
    ∀ (Φ : Sch θ m n) (x : Mx D m n), (ω (g, 1) Φ).1 x = ∫ y, Φ.1 y * pairing T ψ x y ∂μ

  lin : ∀ (h : UA D T) (Φ : Sch θ m n) (x : Mx D m n), (ω (1, h) Φ).1 x = Φ.1 (mmul (mat h⁻¹) x)

def s0 (m n : ℕ) : ℂ := (m : ℂ) / 2 - (n : ℂ) / 2

def sect (α : GG D n → ℝ≥0) (ω : Rep θ n T) (Φ : Sch θ m n) (s : ℂ) (g : GG D n) : ℂ :=
  ((α g : ℝ) : ℂ) ^ (s - s0 m n) * (ω (g, 1) Φ).1 0

def eisTerm (α : GG D n → ℝ≥0) (ω : Rep θ n T) (Φ : Sch θ m n) (g : GG D n) (s : ℂ) (γ : Cosets D n) : ℂ :=
  sect α ω Φ s (γ.rep * g)

end Weil

end GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

end
