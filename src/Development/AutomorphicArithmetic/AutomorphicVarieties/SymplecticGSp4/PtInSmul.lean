module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EiiUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H] (f : R →+* K)

private theorem ptIn_rep (r : H →* M4 R) (g : H) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem ptIn_smul (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp

private theorem ptIn_adj (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem ptIn_gsp {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (f.mapMatrix X) := by
  unfold IsGSp at *
  rw [ptIn_adj, ← map_mul, h, ptIn_smul, map_one]

private theorem ptIn_prj (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R,
      Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ptIn_smul, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem ptIn_ord {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r : H →* M4 R} (h : Ord I ps s₀ r) :
    Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ptIn_rep, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · intro g i j hij
    simp only [ptIn_rep, ptIn_prj]
    rw [← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [ptIn_rep, ptIn_prj]
    have hsub : f.mapMatrix (r s - ps i s • 1) =
        f.mapMatrix (r s) - f (ps i s) • (1 : M4 K) := by
      rw [map_sub, ptIn_smul, map_one]
    rw [← hsub, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

private theorem ptIn_span (r : H →* M4 R) {X : M4 R} (h : X ∈ Submodule.span R (Set.range r)) :
    f.mapMatrix X ∈ Submodule.span K (Set.range (mapRep f r)) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add (f := f.mapMatrix)]
    exact add_mem hx hy
  | smul a x _ hx => rw [ptIn_smul]; exact Submodule.smul_mem _ _ hx

end Gen

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptIn :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (K : Type) [CommRing K] [Algebra c.O K] (r : G ℚ Ω →* M4 K), D.PtIn K r → D.Mult r ∧ D.UnrT r 1 ∧ D.Nrm r ∧ D.eqL (r.comp (D.Gp l).subtype) ∧ (∀ p ∈ D.Sb, D.eqP p (r.comp (D.Gp p).subtype)) ∧ (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) ∧ ∀ (K' : Type) [CommRing K'] [Algebra c.O K'] (f : K →ₐ[c.O] K'), D.PtIn K' (mapRep (f : K →+* K') r) := by
  intro Ω _ _ _ l _ c D hD K _ _ r hr
  obtain ⟨R, _, _, _, ρ, y, hpt, rfl⟩ := hr
  have he : D.IsEq ρ := (ptMap D hD R ρ).1 hpt
  have hy : ∀ a : c.O, (y : R →+* K) (algebraMap c.O R a) = algebraMap c.O K a := fun a => y.commutes a
  have hm : D.Mult (mapRep (y : R →+* K) ρ.hom) := fun g => by
    have h := ptIn_gsp (y : R →+* K) (he.mult g)
    rwa [hy] at h
  have hh : D.hEl (mapRep (y : R →+* K) ρ.hom) = (y : R →+* K).mapMatrix (D.hEl ρ.hom) := by
    unfold Raw.hEl
    rw [map_add (f := _), ptIn_smul, hy, ptIn_rep, ptIn_rep]
  refine ⟨hm, fun A hA g hg hg1 => ?_, ⟨fun i j hij => ?_, ?_, ?_⟩, ⟨fun g => hm g, ?_⟩, fun p hp => ⟨fun g => hm g, fun g hg => ?_⟩,
    fun i => ?_, fun K' _ _ f => ⟨R, inferInstance, inferInstance, inferInstance, ρ, f.comp y, hpt, rfl⟩⟩
  · rw [ptIn_rep, he.unr A hA g hg hg1, map_one]
  · rw [mapRep_apply, he.nrm.1 i j hij, map_zero]
  · rw [hh, RingHom.mapMatrix_apply, Matrix.map_apply, he.nrm.2.1, map_zero]
  · rw [hh, RingHom.mapMatrix_apply, Matrix.map_apply, he.nrm.2.2, map_zero]
  · have h := ptIn_ord (y : R →+* K) he.atL.2
    simp only [hy] at h
    exact h
  · have h : ρ.hom g = 1 := (he.atP p hp).2 g hg
    show (y : R →+* K).mapMatrix (ρ.hom g) = 1
    rw [h, map_one]
  · have h := ptIn_span (y : R →+* K) ρ.hom (eii D hD R ρ he.mult he.nrm i)
    rwa [RingHom.mapMatrix_apply, Matrix.map_single, map_one] at h
