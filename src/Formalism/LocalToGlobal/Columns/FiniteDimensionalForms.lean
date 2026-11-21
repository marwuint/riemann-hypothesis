import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

namespace GFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] (F : GFam K)

abbrev outSec : ∀ b, (F.mem b).Sec := fun b => (F.mem b).outSec

abbrev rep (c : F.Cl) : F.D c.1 := (F.mem c.1).outSec.rep c.2

def valAt (φ : F.Forms) (c : F.Cl) : F.V := ((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) (F.rep c)

def res (h : F.Ok) : F.Forms ≃ₗ[K] (F.toCSD h).Forms := F.resOf h F.outSec

def gramV : Matrix F.ιV F.ιV K := Matrix.of fun i j => F.pair (F.bV i) (F.bV j)

def pairAt (v : InfinitePlace K) (x y : F.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (F.bV.repr x i)) * v.embedding (F.gramV i j) * v.embedding (F.bV.repr y j)

def ipAt (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) : ℂ :=
  letI : Fintype F.Cl := h.fintypeCl
  ∑ c : F.Cl, (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ * F.pairAt v (F.valAt φ c) (F.valAt ψ c)

structure Rat : Prop where
  pair_rat : ∀ i j, F.gramV i j ∈ cmMax K
  act_rat : ∀ (b : F.β) (g : F.G b) i j, F.bV.repr (F.ρ b g (F.bV j)) i ∈ cmMax K
  pos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef

abbrev hDim (h : F.Ok) : ℕ := (F.toCSD h).dim

def hB (h : F.Ok) : Basis (Fin (F.hDim h)) K F.Forms := (F.toCSD h).basis.map (F.res h).symm

variable {F} in
theorem Rat.mem (R : F.Rat) (b : F.β) : (F.mem b).Rat := ⟨R.pair_rat, R.act_rat b, R.pos⟩

variable {F}

variable (F)

variable {F}

variable (F)

theorem pairAt_add_left (v : InfinitePlace K) (x x' y : F.V) :
    F.pairAt v (x + x') y = F.pairAt v x y + F.pairAt v x' y := by
  simp only [pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (v : InfinitePlace K) (x y y' : F.V) :
    F.pairAt v x (y + y') = F.pairAt v x y + F.pairAt v x y' := by
  simp only [pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (v : InfinitePlace K) (a : K) (x y : F.V) :
    F.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * F.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (v : InfinitePlace K) (a : K) (x y : F.V) :
    F.pairAt v x (a • y) = v.embedding a * F.pairAt v x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem valAt_add (φ ψ : F.Forms) (c : F.Cl) : F.valAt (φ + ψ) c = F.valAt φ c + F.valAt ψ c := rfl

theorem valAt_smul (a : K) (φ : F.Forms) (c : F.Cl) : F.valAt (a • φ) c = a • F.valAt φ c := rfl

theorem isSesq_ipAt (h : F.Ok) : IsSesq (fun v (φ ψ : F.Forms) => F.ipAt h v φ ψ) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [ipAt, valAt_add, pairAt_add_left, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, valAt_add, pairAt_add_right, mul_add, Finset.sum_add_distrib]
  · simp only [ipAt, valAt_smul, pairAt_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · simp only [ipAt, valAt_smul, pairAt_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

def evRep (h : F.Ok) : F.Forms →ₗ[K] (F.Cl → F.V) := (F.toCSD h).Forms.subtype ∘ₗ (F.res h).toLinearMap

theorem evRep_apply (h : F.Ok) (φ : F.Forms) (c : F.Cl) : F.evRep h φ c = F.valAt φ c := rfl

theorem evRep_injective (h : F.Ok) : Function.Injective (F.evRep h) :=
  (Submodule.injective_subtype _).comp (F.res h).injective

theorem posAt_ipAt (h : F.Ok) (hpos : ∀ v : InfinitePlace K, (F.gramV.map v.embedding).PosDef)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K F.Forms) :
    PosAt b (fun v (φ ψ : F.Forms) => F.ipAt h v φ ψ) := by
  classical
  intro v
  let _ : Fintype F.Cl := h.fintypeCl
  let P : F.Cl → Matrix F.ιV ι ℂ := fun c => Matrix.of fun i a => v.embedding (F.bV.repr (F.evRep h (b a) c) i)
  have hgram : gramOf b (fun (φ ψ : F.Forms) => F.ipAt h v φ ψ) =
      ∑ c, (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ • ((P c)ᴴ * F.gramV.map v.embedding * P c) := by
    ext a a'
    simp only [gramOf, Matrix.of_apply, ipAt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp only [pairAt, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply,
      Matrix.map_apply, evRep_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine thl_posDef_sum _ (fun c => ?_) _ (hpos v) P fun x hx => ?_
  · have : (0 : ℝ) < (((F.toCSD h).wt c : ℕ) : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (F.toCSD h).wt_pos c)
    have h2 : ((((F.toCSD h).wt c : ℕ) : ℝ)⁻¹ : ℂ) = (((F.toCSD h).wt c : ℕ) : ℂ)⁻¹ := by push_cast; rfl
    rw [← h2]
    exact_mod_cast this
  · let Bb : Basis (Σ _ : F.Cl, F.ιV) K (F.Cl → F.V) := Pi.basis fun _ => F.bV
    obtain ⟨g, hg⟩ := (F.evRep h).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (F.evRep_injective h))
    have h1 : (LinearMap.toMatrix Bb b g).map v.embedding * (LinearMap.toMatrix b Bb (F.evRep h)).map v.embedding = 1 := by
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
      simp
    have h2 : (LinearMap.toMatrix b Bb (F.evRep h)).map v.embedding *ᵥ x = 0 := by
      funext ⟨c, i⟩
      have := congrFun (hx c) i
      simpa [Matrix.mulVec, dotProduct, P, LinearMap.toMatrix_apply, Bb, Pi.basis_repr] using this
    have h3 := congrArg ((LinearMap.toMatrix Bb b g).map v.embedding).mulVec h2
    simpa [Matrix.mulVec_mulVec, h1] using h3

variable {F}

end GFam

namespace GFam

end GFam

namespace GSD

end GSD

section FormFam

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} {β : Type} [Fintype β] [DecidableEq β]

open Classical in

@[reducible] def formFam (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : β → LevFam X.E X.K n SG) : GFam X.K where
  β := β
  V := C.V
  ιV := VVIdx C.lam
  bV := C.bV
  pair := C.pair
  G b := FormG (Λ b)
  D _ := DecoSet X.E n ST SG
  actD b := formAct (Λ b)
  ρ b := formRho C (Λ b)
  Nab _ := C.Nab
  Del _ := C.Del

variable (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : β → LevFam X.E X.K n SG)

end FormFam

end Formalism.L2.Col
