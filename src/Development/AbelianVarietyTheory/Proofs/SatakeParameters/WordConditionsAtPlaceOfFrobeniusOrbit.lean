import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWord
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordParams
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbit
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordBase_of_jumpIn : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i w hw C hG r ρ π ε κ hR hA h2 hq hd hI
  have hU : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) :=
    _root_.GlobalTheory.bridge_field_le_unramified D.nbr i w hw h2 hq hd
  have hF : Formalism.MainNotions.LocalSituation.fontCore ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) := hA _ _
  obtain ⟨g, hg, hread⟩ := _root_.GlobalTheory.HTW.Rec.reads_orbit_invFrob D (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ h2 hq hd
    (D.nbr i w hw).j_dense hU
  refine ⟨g, hg, _root_.GlobalTheory.bridge_degW D.nbr i w hw, ?_, _root_.GlobalTheory.HTW.Rec.recWord_wordNum L C₀ (liftIdx D i) ε g _ hR hg⟩
  exact
    { unram := hU
      split := fun ft => GlobalTheory.splits_of_conjugates_mem _ _ _
        (GlobalTheory.good_conjugates_mem _ _ _ 1 hG) ft
      t1 := _root_.GlobalTheory.HTW.Rec.fits_of_isSubOfSums L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hI hread
      t2 := _root_.GlobalTheory.HTW.Rec.fits_lowCount_of_matRep L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hU hI hread }

end GlobalTheory.HTW.Rec
