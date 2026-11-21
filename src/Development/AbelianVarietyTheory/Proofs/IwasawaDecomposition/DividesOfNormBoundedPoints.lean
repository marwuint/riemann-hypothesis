import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

theorem mk_le_of_finiteType {D : Type} [CommRing D] (σ : D →+* R) (hσ : σ.FiniteType)
    (h : Cardinal.mk D ≤ Cardinal.continuum) : Cardinal.mk R ≤ Cardinal.continuum := by
  letI := σ.toAlgebra
  have : Algebra.FiniteType D R := hσ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le h ((Cardinal.lt_aleph0_of_finite _).le.trans Cardinal.aleph0_le_continuum)) Cardinal.aleph0_le_continuum

theorem natCast_mem {D : Type} [CommRing D] [IsDomain D] [CharZero D] (σ : D →+* R) (hσ : σ.Flat) {n : ℕ} (hn : n ≠ 0) :
    (n : R) ∈ nonZeroDivisors R := by
  letI := σ.toAlgebra
  have : Module.Flat D R := hσ
  have hr : (n : D) ∈ nonZeroDivisors D := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hn)
  have reg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hr
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => reg ?_
  change (n : D) • x = (n : D) • 0
  rw [Algebra.smul_def, smul_zero]
  have e : algebraMap D R (n : D) = (n : R) := map_natCast _ n
  rw [e, mul_comm, hx]

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_opn (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : ∀ x' : Z.X, x' ⤳ x → x' = x) :
    x ∈ Z.opn := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.toPre.s
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have ho := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hc
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  have e := hx _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  obtain ⟨y, hy, hyo⟩ := Z.dense.inter_open_nonempty _ ho ⟨_, mem_irreducibleComponent⟩
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  exact (hg.specializes hy).mem_open hopen hyo

theorem exists_base (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : Z.i.c.V W →+* Γ(Z.X, U), σ.Flat ∧ σ.FiniteType := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have := Z.flat
  let σ : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.toPre.s)).hom
  have e : spMap σ = hU.fromSpec ≫ Z.toPre.s := Spec.map_preimage _
  have h1 : Flat (spMap σ) := by rw [e]; infer_instance
  have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
  exact ⟨σ, (HasRingHomProperty.Spec_iff (P := @Flat)).1 h1, (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2⟩

end Model

end GlobalTheory.HTLine.Dvd
