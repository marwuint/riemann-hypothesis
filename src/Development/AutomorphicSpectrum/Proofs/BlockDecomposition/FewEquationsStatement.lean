import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialPullbackGivesUnitCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsLocalIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DependencyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftMinimalGenerators

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem fewEq : FewEqSt := by
  have gen := GlobalTheory.T.cocycle_units_trivialize_modulo_ideal
  have data := _root_.GlobalTheory.CompanionTheory.FewEq.exists_local_of_triv
  have mingens := _root_.GlobalTheory.CompanionTheory.FewEq.exists_minimal_generators
  have flat := _root_.GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent
  have dep := _root_.GlobalTheory.CompanionTheory.FewEq.depSt
  have fibre := _root_.GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre
  have cocycle := GlobalTheory.T.unit_cocycle_lift_modulo_maximal
  have finish := _root_.GlobalTheory.CompanionTheory.FewEq.exists_correction
  intro R _ _ _ X s n hsm hpr hF M hM I hI hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  obtain ⟨r, t, ht, hmin⟩ := mingens R I
  have hsep : X.IsSeparated := by
    have : IsSeparated (s ≫ terminal.from (Sp R)) := inferInstance
    rw [Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)] at this
    exact ⟨this⟩
  haveI : Flat s := inferInstance

  let A := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : A → X.Opens := fun a => a.1.2
  let j : A → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hA : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  have hAA : ∀ a b, IsAffineOpen (V a ⊓ V b) := fun a b => (hA a).inf (hA b)
  have hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d) := fun a b d => (hAA a b).inf (hA d)
  have hV : ⨆ a, V a = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  have hsq : I * I ≤ IsLocalRing.maximalIdeal R * I := Ideal.mul_mono_left hIm
  suffices hrn : r ≤ n by
    refine ⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i.1 < r
      · simp only [h, dif_pos]
        rw [← ht]
        exact Ideal.subset_span ⟨_, rfl⟩
      · simp only [h, dif_neg, not_false_eq_true]
        exact zero_mem _
    · rw [← ht, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩
      simp
  by_contra hrn
  obtain ⟨u, z, hz, hc⟩ := data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)

  let w : ∀ a, Γ(X, V a) := fun a => z a * (2 - u a * z a)
  have hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := fun a => by
    have h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := by
      refine Ideal.map_mono hsq ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (hz a) (hz a)
    have : u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1)) := by simp only [w]; ring
    rw [this]
    exact neg_mem h2
  obtain ⟨b, hb1, hb2⟩ := cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc
  have hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d) := fun i a c d =>
    flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i
  obtain ⟨e, β, ⟨l, hl⟩, he⟩ := fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3
  obtain ⟨J, y, z', hIJ, hy1, hy2⟩ := finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he
  exact hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))

end GlobalTheory.CompanionTheory.FewEq
