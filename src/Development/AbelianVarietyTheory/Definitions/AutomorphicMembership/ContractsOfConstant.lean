import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic

namespace GlobalTheory.Cartier

namespace CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] (k : Type) [Field k] [Algebra k X.functionField]
  (D : CartierDiv X) (V : Set X.functionField)

def IsBasePoint (x : X) : Prop := ∀ f ∈ V, ¬ D.GeneratesAt x f

structure BasePointFree : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  exists_generatesAt : ∀ x, ∃ f ∈ V, D.GeneratesAt x f

def VanishesOn (f : X.functionField) (Z : Set X) : Prop := ∀ x ∈ Z, D.VanishesAt x f

def ratioField : IntermediateField k X.functionField :=
  IntermediateField.adjoin k {r | ∃ f ∈ V, ∃ g ∈ V, g ≠ 0 ∧ r = f / g}

structure Birational : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  exists_ne_zero : ∃ f ∈ V, f ≠ 0

  ratioField_eq : ratioField k V = ⊤

def SameImage (y y' : X) : Prop :=
  ∀ (n : ℕ) (b : Fin n → X.functionField), (∀ i, b i ∈ V) →
    ∀ (d : ℕ) (g : MvPolynomial (Fin n) k), g.IsHomogeneous d →
      ((d • D).GeneratesAt y (aeval b g) ↔ (d • D).GeneratesAt y' (aeval b g))

def Contracts (C : Set X) : Prop :=
  ∀ y ∈ C, ∀ y' ∈ C, ¬ D.IsBasePoint V y → ¬ D.IsBasePoint V y' → D.SameImage k V y y'

structure NoContract (bd : Set X) : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  not_contracts : ∀ C : Set X, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
    Disjoint C bd → ¬ D.Contracts k V C

variable {k D V}

end CartierDiv

namespace Presents

end Presents

end GlobalTheory.Cartier
