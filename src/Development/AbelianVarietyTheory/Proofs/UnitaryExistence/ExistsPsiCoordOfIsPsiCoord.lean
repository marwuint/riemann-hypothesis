import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

namespace GlobalTheory.PeriodFormCompare

variable {R : Type} [CommRing R] [IsDomain R]

theorem generic_val (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) = algebraMap R (FractionRing R) r := by
  have e : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [e]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (jK R).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

theorem psiCoord_iff (D : DegPre R) (χ : D.X) (r : R) :
    PsiCoord D χ r ↔ ∃ x, IsPsiCoord D χ x ∧ x.val = algebraMap R (FractionRing R) r := by
  constructor
  · rintro ⟨j, hj, h, e⟩
    exact ⟨_, ⟨j, h, hj, rfl⟩, (congrArg _ e.symm).trans (generic_val r)⟩
  · rintro ⟨_, ⟨j, h, hj, rfl⟩, e⟩
    refine ⟨j, hj, h, ?_⟩
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
      ((generic_val r).trans e.symm)

theorem isPsiCoord_toUnitK {D : DegPre R} {χ : D.X} {r : R} (h : PsiCoord D χ r) (h0 : r ≠ 0) :
    IsPsiCoord D χ (toUnitK r h0) := by
  obtain ⟨x, hx, e⟩ := (psiCoord_iff D χ r).1 h
  have : x = toUnitK r h0 := Units.ext e
  exact this ▸ hx

theorem exists_psiCoord_iff [IsLocalRing R] (D : DegPre R) (χ : D.X) :
    (∃ r, PsiCoord D χ r) ↔ D.PsiIn χ ⊤ := by
  constructor
  · rintro ⟨r, hr⟩
    exact (PeriodFormEdge.psiIn_iff hr ⊤).2 trivial
  · intro hI
    obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D χ
    have h := PsiCoordLocal.generic_le D χ j hj
    obtain ⟨s, -, e⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
    exact ⟨r, j, hj, h, e⟩

theorem exists_psiCoord_of_isPsiCoord [IsLocalRing R] {D : DegPre R} {χ : D.X} (hI : D.PsiIn χ ⊤)
    {x : (FractionRing R)ˣ} (hx : IsPsiCoord D χ x) :
    ∃ r, PsiCoord D χ r ∧ x.val = algebraMap R (FractionRing R) r := by
  obtain ⟨r, hr⟩ := (exists_psiCoord_iff D χ).2 hI
  obtain ⟨y, hy, e⟩ := (psiCoord_iff D χ r).1 hr
  obtain ⟨u, hu⟩ := hx.unique hy
  have : x.val = algebraMap R (FractionRing R) (u * r) := by
    rw [hu, map_mul, ← e]; rfl
  exact ⟨u * r, (psiCoord_iff D χ _).2 ⟨x, hx, this⟩, this⟩

theorem psiIn_top {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) : D.toPre.PsiIn χ ⊤ := by
  by_cases h : χ = 0
  · subst h; exact (PsiZero.main R D.toPre).1 D.tau_bimult
  · exact (PsiZero.main R D.toPre).2 χ I ⊤ le_top (D.psi_pos χ h)

end GlobalTheory.PeriodFormCompare
