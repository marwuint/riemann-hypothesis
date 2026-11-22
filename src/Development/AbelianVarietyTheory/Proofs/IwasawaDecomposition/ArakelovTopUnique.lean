import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfIntersectionShiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundlesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ArUniq

theorem isSelfInter_pow (hC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (hX : IsArithVar p D) {L : HermLB p} {a : ℝ} (ha : L.IsSelfInter a) (m : ℕ) :
    (L.pow m).IsSelfInter ((m : ℝ) ^ (D + 1) * a) := by
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, e⟩ := hΦ.1 fun _ => (m : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (_root_.GlobalTheory.ArInt.isometric_comb_unit_pow k X p L m) hH, e.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

def Reads (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (t : ℝ) :
    Prop :=
  A.Induced M L k cf ∧ ∃ a : ℝ, (haveI := M.ar.isIntegral; L.IsSelfInter a) ∧
    t = (a / (((k : ℕ) : ℝ) * (A.n : ℕ)) ^ (Y.dim + 1) + ((Y.dim : ℝ) + 1) * A.deg * ∑ᶠ v, cf v) /
      (Module.finrank ℚ F : ℝ)

variable {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 F) → ℝ} {t : ℝ}

theorem Reads.pull (hB : GlobalTheory.Published.ArBirational) (h : Reads A M L k cf t) (N : TrueGeo.Model Y) (π : N.X ⟶ M.X)
    (hπ : π ≫ M.p = N.p) (hj : N.j ≫ π = M.j) (hU : ∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) :
    Reads A N (L.pull π hπ) k cf t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  obtain ⟨U, hU, hU'⟩ := hU
  have := M.ar.isIntegral
  have := N.ar.isIntegral
  exact ⟨_root_.GlobalTheory.TrueGeo.InducedPull.induced_pull F C Y A M N π hπ hj L k cf hI, a,
    hB _ M.X N.X M.p N.p Y.dim M.ar N.ar (_root_.GlobalTheory.ModelCharts.genSmooth_model F Y M) (_root_.GlobalTheory.ModelCharts.genSmooth_model F Y N) π hπ U hU hU' L a ha, ht⟩

theorem Reads.pow (hE : GlobalTheory.Published.ArCalc) (h : Reads A M L k cf t) (m : ℕ+) :
    Reads A M (L.pow m) (k * m) cf t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  have := M.ar.isIntegral
  refine ⟨_root_.GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A M L k m cf hI, _, isSelfInter_pow hE M.ar ha m, ?_⟩
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [ht, PNat.mul_coe, Nat.cast_mul]
  congr 2
  rw [mul_right_comm, mul_pow _ ((m : ℕ) : ℝ)]
  field_simp

theorem Reads.scale (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree) (h : Reads A M L k cf t) {b : 𝓞 F} (hb : b ≠ 0) :
    ∃ L' : HermLB M.p, Reads A M L' k (fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  have hc : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖ := fun σ => by simp
  obtain ⟨hf, r, hr, -⟩ := id hI
  refine ⟨_, _root_.GlobalTheory.TrueGeo.IndScale.induced_shift F C Y A M L k cf b hb hc hI, _,
    GlobalTheory.T.self_intersection_shift hC hD F Y M L _ r hr (fun σ => Real.log ‖σ b‖) hc a ha, ?_⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F (algebraMap (𝓞 F) F b) (by simpa using hb)
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [finsum_add_distrib hf (h₁.subset fun v hv h0 => hv (by simp only [h0, zero_div]))]
  simp only [div_eq_mul_inv (Real.log _)]
  rw [← finsum_mul' _ _ h₁, eq_neg_of_add_eq_zero_right h₂, ht, Y.inter_const_nsmul, Adl.deg]
  simp only [RingHom.comp_apply]
  congr 1
  push_cast
  field_simp
  ring

theorem Reads.eq (hC : GlobalTheory.Published.ArCalc) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {L' : HermLB M.p} {t' : ℝ}
    (h : Reads A M L k cf t) (h' : Reads A M L' k cf t') : t = t' := by
  obtain ⟨hI, a, ⟨H, hH, rfl⟩, rfl⟩ := h
  obtain ⟨hI', a', ha', rfl⟩ := h'
  have := M.ar.isIntegral
  have e := HermLB.IsSelfInter.unique M.ar ⟨H, (hC.arIso _ M.X M.p Y.dim M.ar).1 L L' H
    (_root_.GlobalTheory.HermIsom.isometric_of_ratIsom _ M.X M.p L L' (GlobalTheory.T.ratIsom_of_induced_hermitian_bundles F C Y A M hN L L' k cf hI hI')) hH, rfl⟩ ha'
  rw [e]

end GlobalTheory.TrueGeo.ArUniq
