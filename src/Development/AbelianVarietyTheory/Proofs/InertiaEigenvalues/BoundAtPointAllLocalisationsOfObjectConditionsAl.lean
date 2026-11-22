import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocalisationBoundAtPoint

theorem boundAtPoint_all_localisations_of_objectConditions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.IntegralityFromMetric D := by
  intro hGAR hBK hLTD hLEC D h51 i r ρ π dc lenRow e' cB hR hA hl0 hl1
  have a51 := h51 i hl0 hl1 r ρ π dc lenRow e' cB hR hA
  obtain ⟨G1, G2, G3, G4, G5, G5x, G6, BK, TB, ROW, LIFT, Cont, SS, Decomp, Eps, Comparison₂, Shape, Font, H2, CFT⟩ := hA
  have TB78 : EmbeddingTypes.admTB i r π dc cB := fun w hw _ C hC => TB w hw C hC
  exact _root_.GlobalTheory.SelmerBoundAtPoint.main hGAR hLTD hLEC D i r ρ π dc lenRow e' cB G1 G2 G3 G4 G5 G5x G6 BK
    (_root_.GlobalTheory.BKaRows.bkaAll_of_hypotheses hBK hLTD hLEC D i) Cont Decomp Font (_root_.GlobalTheory.finAll_of_localTateDuality hLTD D i) Comparison₂ a51
    (GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc) ROW LIFT TB78 hl0 hl1

end GlobalTheory.LocalisationBoundAtPoint
