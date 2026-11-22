import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {q : Y ⟶ X} {q' : Y' ⟶ X'} {pm : Y' ⟶ Y}

def PtOver (w : LB.Iso L' (L.pull F)) (pm : Y' ⟶ Y) (k : ℤ)
    (s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)))
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : L.ι) (j : L'.ι), F (q' (r z)) ∈ L.U i → q' (r z) ∈ L'.U j →
    gs (r ≫ pm) z _ (s.f fun _ => i) = (gw w (r ≫ q') z i j ^ k).val * gs r z _ (s'.f fun _ => j)

theorem PtOver.comp {Y'' : Scheme.{0}} {q'' : Y'' ⟶ X'} {pn : Y'' ⟶ Y'} (hq : pn ≫ q' = q'') {w : LB.Iso L' (L.pull F)}
    {k : ℤ} {s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k))}
    {s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k))} (H : PtOver w pm k s' s)
    {s'' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q'') (fun _ => k))}
    (hs : ∀ (j : Fin 1 → L'.ι) (e : (LB.LinComb L' (K := Fin 1) (fun _ => q'') (fun _ => k)).U j ≤
      pn ⁻¹ᵁ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U j), (pn.appLE _ _ e).hom (s'.f j) = s''.f j) :
    PtOver w (pn ≫ pm) k s'' s := by
  subst hq
  intro Z r z i j hi hj
  have e : (LB.LinComb L' (K := Fin 1) (fun _ => pn ≫ q') (fun _ => k)).U (fun _ => j) ≤
      pn ⁻¹ᵁ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j :=
    fun y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  rw [← hs _ e, gs_appLE pn _ _ e r z (Set.mem_iInter.2 fun _ => hj), ← Category.assoc, ← Category.assoc]
  exact H Z (r ≫ pn) z i j hi hj

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

variable {Xo : Moduli D l} {c : Coeff l}

section Rule

def fnRule (g : Γ(Xo.XF c, ⊤)) : Rul Xo c := fun _ y => fnAt (basePt y) g

theorem fnAt_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (y : Sp S ⟶ X) (g : Γ(X, ⊤)) :
    fnAt (spMap ψ ≫ y) g = ψ (fnAt y g) := by
  have e := congrArg (fun k => k.hom (y.appTop.hom g)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

theorem basePt_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {ψ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap ψ y z) : basePt z = spMap ψ.toRingHom ≫ basePt y := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
  · rw [Category.assoc, basePt, basePt, pullback.lift_snd, pullback.lift_snd,
      GlobalTheory.Frames.FramedBaseChange.spMap_comp_spMap]
    exact congrArg spMap ψ.comp_algebraMap.symm

theorem fnRule_mem (g : Γ(Xo.XF c, ⊤)) : fnRule g ∈ sec Xo c 0 0 := by
  refine ⟨fun p q ψ y z h => ?_, fun p t y y' h => ?_⟩
  · change fnAt (basePt z) g = ψ (fnAt (basePt y) g)
    rw [basePt_frMap h, fnAt_comp]
    rfl
  · have e : basePt y' = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
      · rw [basePt, basePt, pullback.lift_snd, pullback.lift_snd]
    have e' : wchar (ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
    change fnAt (basePt y') g = _ * fnAt (basePt y) g
    rw [e, e', _root_.one_mul]

theorem evR_fnRule (g : Γ(Xo.XF c, ⊤)) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (fnRule g) y = fnAt (basePt y) g := by
  have h := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c S y
  unfold evR evalAt
  rw [dif_pos h, basePt_frMap h.choose_spec.choose_spec.choose_spec, fnAt_comp]
  rfl

end Rule

theorem fnRule_injective : Function.Injective (fnRule (Xo := Xo) (c := c)) := by
  intro g g' h
  refine fn_ext fun z _ => ?_
  obtain ⟨p, j, y, ⟨hj, h1, h2⟩, z, rfl⟩ :=
    GlobalTheory.Frames.exists_openChart_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c z
  have e : basePt y = j := pullback.hom_ext (by rw [basePt, pullback.lift_fst, h1]) (by rw [basePt, pullback.lift_snd, h2])
  have e' : fnAt j g = fnAt j g' := e ▸ congrFun (congrFun h p) y
  have e'' : j.appTop.hom g = j.appTop.hom g' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of p.R)).hom).1 e'
  refine (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ?_
  refine (gs_stalkMap j z ⊤ trivial g).symm.trans (Eq.trans ?_ (gs_stalkMap j z ⊤ trivial g'))
  rw [gs_eq j z ⊤ trivial, gs_eq j z ⊤ trivial]
  exact congrArg _ e''

end GlobalTheory.LevelCoverCompare
