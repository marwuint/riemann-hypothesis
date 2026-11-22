import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationDirectSummand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemOfSummandReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemHomOfFiltrationEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftEqComapSystemFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePresentedBySystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_hodgeDeRham (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) :
    AbelianSchemeLifts := by
  intro R _ _ I hI R₀ _ π hπ hk g A₀ _ A' _ i' h' hA hg
  haveI : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ π hπ
  obtain ⟨-, -, -, -, -, -, hA₀, hg₀⟩ := _root_.GlobalTheory.LiftSys.abelianLift_facts hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  have hG : Good A₀.hom := _root_.GlobalTheory.LiftSys.good_of_isAbelianScheme hC hH R₀ A₀ g hA₀ hg₀
  have hR : RhoBC hI hk A₀.hom := _root_.GlobalTheory.LiftSys.rhoBC_of_abelianLift hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨ad1, ad2, ad3⟩ := _root_.GlobalTheory.LiftSys.admissible_classification hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨S', ⟨P'⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom A'.left A'.hom i' h'.1 hA.smooth
  obtain ⟨hF', hc'⟩ := _root_.GlobalTheory.LiftSys.full_and_isCompl hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg S' P'
  have core1 := _root_.GlobalTheory.LiftSys.summand_of_full R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc'
  have ksup := _root_.GlobalTheory.LiftSys.Sys.mem_K_sup_iff R R₀ I hI π hπ hk A₀.left A₀.hom S' hR hF'
  have fil : ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom →
      ∀ S : Sys I π A₀.hom, S.Presents X.hom i → schemeFil (divided₂ hI) A₀ X i h.w =
        ((S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator := fun X i h hX S P ↦
    congrArg Submodule.dualAnnihilator
      (GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys hC R R₀ I hI π hπ hk A₀ hA₀.proper hA₀.geomConnected X i h hX S P)
  refine ⟨⟨fun X i h hX ↦ ?_, fun F hF ↦ ?_⟩, fun X Y i j h k hX hY e ↦ ?_⟩
  · obtain ⟨S, ⟨P⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨hc, hs⟩ := core1 S
    obtain ⟨F, hF, e⟩ := ad1 (S.K hI) hc fun c ↦ by rw [hs]; exact ksup c
    exact ⟨F, hF, (fil X i h hX S P).trans e⟩
  · obtain ⟨K, hc, hs, e⟩ := ad2 F hF
    obtain ⟨S, rfl⟩ := _root_.GlobalTheory.LiftSys.exists_sys_of_summand R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc' K hc
      (Submodule.ext fun c ↦ (hs c).trans (ksup c).symm)
    obtain ⟨X, s, i, h1, h2, ⟨P⟩⟩ := GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem R R₀ I hI π hπ hk A₀.left A₀.hom S
    obtain ⟨h, hX⟩ := _root_.GlobalTheory.LiftSys.presents_isLift R R₀ I hI π hπ hk A₀.left A₀.hom S X s i h1 h2 P
    exact ⟨Over.mk s, i, h, hX, (fil (Over.mk s) i h hX S P).trans e⟩
  · obtain ⟨S, ⟨P⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨T, ⟨Q⟩⟩ := _root_.GlobalTheory.LiftSys.exists_sys_presents R R₀ I hI π hπ hk A₀.left A₀.hom Y.left Y.hom j k hY
    have hK : T.K hI = S.K hI := ad3 _ _ (core1 T).1 (core1 S).1
      ((fil Y j k hY T Q).symm.trans (e.symm.trans (fil X i h hX S P)))
    have hT : T.Full hI := (_root_.GlobalTheory.LiftSys.K_inf_eq_and_full R R₀ I hI π hπ hk A₀.left A₀.hom hG.const S' T).2 hF'
    obtain ⟨f, hf, hij⟩ := _root_.GlobalTheory.LiftSys.Glue.presents_hom R R₀ I hI π hπ hk A₀.left A₀.hom T S X.left X.hom i Y.left Y.hom j h Q P
      (_root_.GlobalTheory.LiftSys.sysHom_of_K_eq R R₀ I hI π hπ hk A₀.left A₀.hom hG hR T S hT hK)
    haveI := hX
    have hn : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
    haveI : IsIso (Over.homMk f hf : X ⟶ Y) :=
      GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hn X Y A₀ A₀ i j h k inferInstance
        (Over.homMk f hf) (𝟙 A₀) (by simpa using hij) inferInstance
    exact ⟨asIso (Over.homMk f hf : X ⟶ Y), hij⟩

end GlobalTheory.LiftSys
