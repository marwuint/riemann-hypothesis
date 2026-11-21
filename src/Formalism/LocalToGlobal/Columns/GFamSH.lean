import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteDimensionalForms
import Formalism.LocalToGlobal.Columns.GFamS

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFamS

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFamS K)

@[reducible] def toCSD (h : F.Ok) : CSD K := F.toCSDOf h F.sec

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.sec b)

abbrev rep (c : F.Cl) : F.D c.1 := (F.sec c.1).rep c.2

def valAt (φ : F.Forms) (c : F.Cl) : F.V := ((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) (F.rep c)

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

def pairAt (v : InfinitePlace K) (x y : F.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (F.bV.repr x i)) * v.embedding (F.gramV i j) * v.embedding (F.bV.repr y j)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

variable {F} in
theorem Rat.mem (R : F.Rat) (b : F.β) : (F.mem b).Rat := ⟨R.pair_rat, R.act_rat b, R.pos⟩

variable {F}

variable (F)

variable {F}

variable (F)

theorem valAt_add (φ ψ : F.Forms) (c : F.Cl) : F.valAt (φ + ψ) c = F.valAt φ c + F.valAt ψ c := rfl

theorem valAt_smul (a : K) (φ : F.Forms) (c : F.Cl) : F.valAt (a • φ) c = a • F.valAt φ c := rfl

def evRep (h : F.Ok) : F.Forms →ₗ[K] (F.Cl → F.V) := (F.toCSD h).Forms.subtype ∘ₗ (F.res h).toLinearMap

theorem evRep_apply (h : F.Ok) (φ : F.Forms) (c : F.Cl) : F.evRep h φ c = F.valAt φ c := rfl

variable {F}

end GFamS

namespace GFamS

end GFamS

end Formalism.L2.Col
