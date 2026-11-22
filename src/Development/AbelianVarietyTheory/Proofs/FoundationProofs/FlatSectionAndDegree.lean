import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisBaseChangeLocalAlgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisLocalizationAtPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem eigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : EigStable T c := by
  intro R R' _ _ g j x τ m v v' hv hv'
  obtain ⟨t, ⟨n⟩⟩ := exists_sab x T
  obtain ⟨t', ⟨n'⟩⟩ := exists_sab (spMap g) t
  obtain ⟨n'', e''⟩ := TraitDataOfIntrinsic.map_comp n' n rfl
  choose w hw using fun i => exists_lift n.cart (v i)
  choose w' hw' _ using fun i => existsUnique_isVecOver n'.cart.1 (w i)
  have hb := ((fibre_iff n.cart hw).2 n.act _).2 hv
  refine ((fibre_iff n''.cart (v := w') fun i => ?_).2 n''.act _).1 (_root_.GlobalTheory.FlatRow.isEigBasis_of_local E H R' t' _ m w' fun q _ => ?_)
  · change _ ≫ n''.φ = _
    rw [e'', ← Category.assoc, hw' i, Category.assoc, hw, hv']
  let p := q.comap g
  let gp : Localization.AtPrime p →+* Localization.AtPrime q := Localization.localRingHom p q g rfl
  have hg : gp.comp (algebraMap R _) = (algebraMap R' _).comp g :=
    RingHom.ext fun z => Localization.localRingHom_to_map p q g rfl z
  obtain ⟨tq, ⟨nq⟩⟩ := exists_sab (spMap (algebraMap R' (Localization.AtPrime q))) t'
  obtain ⟨tp, ⟨np⟩⟩ := exists_sab (spMap (algebraMap R (Localization.AtPrime p))) t
  obtain ⟨k, ek⟩ := TraitDataOfIntrinsic.map_comp nq n' rfl
  obtain ⟨k', ek'⟩ := TraitDataOfIntrinsic.map_cancel (g := spMap gp) k np
    (by rw [spMap_comp_spMap, spMap_comp_spMap, hg])
  choose wq hq _ using fun i => existsUnique_isVecOver nq.cart.1 (w' i)
  choose wp hp _ using fun i => existsUnique_isVecOver np.cart.1 (w i)
  refine ⟨tq, nq, wq, hq, ?_⟩
  have h₁ := _root_.GlobalTheory.EigBasisPrime.isEigBasis_atPrime E H R p t tp np _ m w wp hb hp
  have h₂ := _root_.GlobalTheory.EigBasisLocal.isEigBasis_baseChange E H l c _ _ ((algebraMap R _).comp j) gp tp tq k' τ m wp wq h₁ fun i =>
    EllComp.isVecOver_cancel np.cart.1 k'.cart.1 (hp i)
      (by rw [← ek', ek, hg]; exact EllComp.isVecOver_comp (hw' i) (hq i))
  rwa [← RingHom.comp_assoc, hg] at h₂

variable {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

theorem isIso_fst (Y : Model Xo c (RingHom.id c.F)) : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  infer_instance

theorem isNormal_genFibre (Y : Model Xo c (RingHom.id c.F)) : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := by
  intro x
  have := isIso_fst Y
  let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end GlobalTheory.FlatRow
