import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.EqOneOfHeckeEigNeBot
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMonHomIdPow
import Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemOfMemHeckeLevel
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W2

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh
open GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.HeckeCorr
open scoped TensorProduct

section Side

variable {Γ : Type} [Group Γ]

theorem mem_heckeLevel_inv {K : Subgroup Γ} {h u : Γ} : u ∈ heckeLevel K h⁻¹ ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := by
  refine ⟨fun hu => ⟨heckeLevel_le K h⁻¹ hu, by simpa using conj_mem_of_mem_heckeLevel hu⟩, fun hu => ⟨hu.1, ?_⟩⟩
  exact ⟨h * u * h⁻¹, hu.2, by simp [MulAut.conj_apply, _root_.mul_assoc]⟩

end Side

section Corr

variable {G₀ : GDatum} {gb : GBase G₀ ℂ}

structure Corr {N N' : ℕ} (X : GenModel gb N) (X' : GenModel gb N') where

  q1 : X'.X ⟶ X.X

  q2 : X'.X ⟶ X.X
  firstProjection_structure : q1 ≫ X.s = X'.s
  secondProjection_structure : q2 ≫ X.s = X'.s

  φ1 : X'.univ.A.left ⟶ X.univ.A.left

  φ2 : X'.univ.A.left ⟶ X.univ.A.left
  φ1_w : φ1 ≫ X.univ.A.hom = X'.univ.A.hom ≫ q1
  φ2_w : φ2 ≫ X.univ.A.hom = X'.univ.A.hom ≫ q2

namespace Corr

variable {N N' : ℕ} {X : GenModel gb N} {X' : GenModel gb N'} (C : Corr X X') (k : ℕ)

def c1 : Z X' k ⟶ Z X k := GlobalTheory.KS.powMap C.q1 C.φ1 C.φ1_w k

def c2 : Z X' k ⟶ Z X k := GlobalTheory.KS.powMap C.q2 C.φ2 C.φ2_w k

theorem firstLeg_overComplex : C.c1 k ≫ zs X k = zs X' k := by
  rw [zs, zs, c1, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, C.firstProjection_structure]

theorem secondLeg_overComplex : C.c2 k ≫ zs X k = zs X' k := by
  rw [zs, zs, c2, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, C.secondProjection_structure]

def op [IsFinite (C.c1 k)] [Etale (C.c1 k)] (a b : ℕ) : hodgeH (zs X k) a b →ₗ[ℂ] hodgeH (zs X k) a b :=
  corrOp (C.c1 k) (C.c2 k) (C.firstLeg_overComplex k) (C.secondLeg_overComplex k) a b

end Corr

end Corr

section Wit

variable {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

abbrev GTIsoAt {gb : GBase G₀ R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k]
    (t : Sp k ⟶ S) : Type :=
  GTateIso G₀ k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG R}

def GActsAt {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} {o' : GObj gb N' s} {o'' : GObj gb N s} {k : Type} [Field k]
    {t : Sp k ⟶ S} (I' : GTIsoAt o' t) (I'' : GTIsoAt o'' t) (ψ : o'.A ⟶ o''.A) (m : ℤ) (h : G.GAf) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
    I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, m • L.actG h (inAf D x) = inAf D y + n • v

def latMonoid : Submonoid G.GAf where
  carrier := {h | ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D}
  one_mem' := fun v hv => by rw [map_one]; exact hv
  mul_mem' := fun {a b} ha hb v hv => by rw [map_mul, Module.End.mul_apply]; exact ha _ (hb v hv)

theorem smul_mem_laHat {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a', x, ha', rfl⟩ := hu
    refine AddSubgroup.subset_closure ⟨a * a', x, fun w => ?_, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
    rw [map_mul]
    exact mul_mem (ha w) (ha' w)
  | zero => rw [smul_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => rw [smul_add]; exact add_mem hu hu'
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

def scalarAf (G : HTGroup p) (a : (AfP p)ˣ) : G.GAf :=
  ⟨(Units.map (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)).toMonoidHom a, a * a), by
    show algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a * (starT G.star (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((a : AfP p) * a)
    have e : algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a = (a : AfP p) ⊗ₜ[ℚ] (1 : G.C) := rfl
    rw [map_mul, e, starT_tmul, map_one, MulOpposite.unop_one]⟩

theorem actG_scalarAf (a : (AfP p)ˣ) (v : AfP p ⊗[ℚ] VQ D) : L.actG (scalarAf G a) v = (a : AfP p) • v := by
  show actOn L.rep (AfP p) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) a) v = _
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

theorem scalarAf_comm (a : (AfP p)ˣ) (u : G.GAf) : scalarAf G a * u = u * scalarAf G a :=
  Subtype.ext (Prod.ext (Units.ext (Algebra.commutes (a : AfP p) _)) (mul_comm _ _))

def natUnit (p : ℕ) (c : ℕ) (hc : c ≠ 0) : (AfP p)ˣ :=
  Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 (c : ℚ) (Nat.cast_ne_zero.2 hc))

theorem actG_natScalar (c : ℕ) (hc : c ≠ 0) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG (scalarAf G (natUnit p c hc)) v = c • v := by
  rw [actG_scalarAf]
  show algebraMap ℚ (AfP p) (c : ℚ) • v = _
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

end Wit

section Op

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ} {N : ℕ}

theorem relIndex_KN_ne_zero {N N' : ℕ} (hN : 0 < N) (hN' : 0 < N') : (L.KN N').relIndex (L.KN N) ≠ 0 := by
  obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  obtain ⟨K', hK'⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N' hN'
  haveI : CompactSpace (L.KN N) := isCompact_iff_compactSpace.1 (hK ▸ K.compact)
  have ho : IsOpen ((L.KN N').subgroupOf (L.KN N) : Set (L.KN N)) :=
    (show IsOpen (L.KN N' : Set G.GAf) from hK' ▸ K'.K.isOpen).preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

theorem KN_mul_le (N k' : ℕ) : L.KN (N * k') ≤ L.KN N := by
  have key : ∀ g, L.CongOne (N * k') g → L.CongOne N g := fun g hg v hv => by
    obtain ⟨w, hw, e⟩ := hg v hv
    exact ⟨k' • w, nsmul_mem hw k', by rw [e, mul_smul]⟩
  exact fun g hg => ⟨key _ hg.1, key _ hg.2⟩

variable {L}

end Op

section Away

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

def awayGrp (G : HTGroup p) (S : Finset ℕ) : Subgroup G.GAf :=
  ⨅ (v : AwayP p) (_ : ∃ q ∈ S, q.Prime ∧ (q : ℤ) ∈ v.1.asIdeal), (ubcMap (AfP.eval v)).ker

variable (L : Link D G)

def awaySupp (N : ℕ) (S : Finset ℕ) : Set G.GAf :=
  {g | ∃ h ∈ awayGrp G S, h ∈ latMonoid L ∧ g ∈ DoubleCoset.doubleCoset h⁻¹ (L.KN N : Set G.GAf) (L.KN N)}

def heckeAway (N : ℕ) (S : Finset ℕ) : Submodule ℂ (G.GAf → ℂ) :=
  Formalism.UG.Hecke ℂ (L.KN N) ⊓
    { carrier := {f | ∀ g, f g ≠ 0 → g ∈ awaySupp L N S}
      zero_mem' := fun _ h => (h rfl).elim
      add_mem' := fun {f f'} hf hf' g hg => by
        by_cases h : f g = 0
        · exact hf' g fun h' => hg (by simp [h, h'])
        · exact hf g h
      smul_mem' := fun c f hf g hg => hf g fun h => hg (by simp [h]) }

theorem mem_heckeAway {N : ℕ} {S : Finset ℕ} {f : G.GAf → ℂ} :
    f ∈ heckeAway L N S ↔ f ∈ Formalism.UG.Hecke ℂ (L.KN N) ∧ ∀ g, f g ≠ 0 → g ∈ awaySupp L N S := Iff.rfl

end Away

end GlobalTheory.W2
