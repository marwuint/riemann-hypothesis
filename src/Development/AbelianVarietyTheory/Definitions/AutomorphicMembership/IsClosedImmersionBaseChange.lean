import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardLiesOverEqIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open GlobalTheory.CechPic (cls tens dual)

namespace GlobalTheory.ShFam.Pad

abbrev FibCrv (p : ℕ) (X : Scheme.{0}) : Type :=
  {C : Closeds X // IsIrreducible (C : Set X) ∧ topologicalKrullDim (C : Set X) = 1 ∧
    ∀ x ∈ C, (p : X.residueField x) = 0}

namespace FibCrv

variable {p : ℕ} {X : Scheme.{0}} (c : FibCrv p X)

abbrev sch : Scheme.{0} := (Scheme.IdealSheafData.vanishingIdeal c.1).subscheme

abbrev ι : c.sch ⟶ X := redι c.1

instance isIntegral : IsIntegral c.sch := isIntegral_red c.2.1

theorem natCast_eq_zero : (p : Γ(c.sch, ⊤)) = 0 := by
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  refine absurd hy ((c.sch.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) y trivial _).1 ?_)
  rw [map_natCast, ← map_natCast (c.ι.residueFieldMap y).hom, c.2.2.2 _ ((range_redι c.1).le ⟨y, rfl⟩), map_zero]

instance algebra : Algebra (ZMod p) Γ(c.sch, ⊤) := ZMod.algebra' _ (ringChar _) (ringChar.dvd c.natCast_eq_zero)

variable [Fact p.Prime] {L M N H : LB X}

def deg (L : LB X) : ℤ := interNumRed (ZMod p) (⊤ : Closeds c.sch) ![L.pull c.ι]

abbrev str : c.sch ⟶ Sp (ZMod p) := strHom (ZMod p) c.sch

variable [IsProper c.str]

end FibCrv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev Crv (z : admitted Y i₀) : Type := FibCrv p z.Z.X

def cov (z : admitted Y i₀) : ℕ := levDeg z.Z.dvd (Xo i₀.l) i₀.c (Xo z.Z.i.l) z.Z.i.c

theorem cov_pos (z : admitted Y i₀) : 0 < cov z := levDeg_pos _ _ _ _ _

theorem natCast_mem_nonunits {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hp)
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_comap] at h'
    simpa using h'

theorem natCast_eq_zero_iff (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : LocM.Mdl Y i₀) (x : Z.X) :
    (p : Z.X.residueField x) = 0 ↔ ¬ Z.inQ x := by
  refine ⟨fun h (k : CharZero _) => hp.ne_zero (Nat.cast_eq_zero.1 h), fun h => ?_⟩
  let φ : Z.i.c.V W →+* Z.X.residueField x :=
    ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv ≫ Z.s.appTop ≫ Z.X.Γevaluation x).hom
  have hq : (ringChar (Z.X.residueField x)).Prime :=
    (CharP.char_is_prime_or_zero (Z.X.residueField x) _).resolve_right fun k =>
      h ((CharP.ringChar_zero_iff_CharZero _).1 k)
  by_contra hne
  have hc : (ringChar (Z.X.residueField x)).Coprime p :=
    hq.coprime_iff_not_dvd.2 fun k => hne ((ringChar.spec _ _).2 k)
  have := (GlobalTheory.CoeffRings.isUnit_of_coprime _ (natCast_mem_nonunits Z.i.c hp.ne_zero hW) hc).map φ
  rw [map_natCast, ringChar.Nat.cast_ringChar] at this
  exact not_isUnit_zero this

variable [Fact p.Prime]

variable {z : admitted Y i₀}

def degLine (L : FinLB z.Z.X) (c : Crv z) : ℤ := FibCrv.deg c L.lb

variable (z) (c : Crv z)

def degStep (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : ℤ :=
  match h : letterOf Dw st with
  | some x => degLine (z.line b st x h).L c
  | none => 0

def degRoot (τ : E →+* ℂ) (i : ℕ) : ℝ :=
  if i < Dw.p then (degStep z c true (.inl (τ, i)) : ℝ)
  else -(degStep z c true (.inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) : ℝ)

section Line

open ProjSpace

variable (p) {O : Type} [CommRing O] (φ : O →+* ZMod p)

instance isClosedImmersion_baseChange (N : ℕ) : IsClosedImmersion (baseChange N φ) :=
  MorphismProperty.of_isPullback (isPullback_baseChange N φ).flip
    (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective φ))

end Line

end GlobalTheory.ShFam.Pad
