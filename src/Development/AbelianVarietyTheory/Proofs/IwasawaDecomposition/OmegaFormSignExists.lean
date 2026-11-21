import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

theorem isRoots_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {r n N : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (ε : ℤˣ) (hN : l.M ∣ N)
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (h : IsRoots l L ((ε : ℤ) • mk) N Y) :
    IsRoots l L mk l.M fun q => (ε : ℤ) • Y q := by
  intro q b
  obtain ⟨⟨a, ha, h1, h2⟩, j, hj⟩ := h q b
  obtain ⟨m, rfl⟩ := hN
  refine ⟨⟨a, ha, h1, ?_⟩, j, fun s hs => ?_⟩
  · have h3 := zsmul_mem h2 (ε : ℤ)
    rw [smul_sub, LinearMap.smul_apply, smul_comm (l.M : E)⁻¹, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul] at h3
    exact h3
  · obtain ⟨u, hu, e⟩ := hj s hs
    refine ⟨(ε : ℤ) • m • u, zsmul_mem (nsmul_mem hu m) _, ?_⟩
    show s • (ε : ℤ) • Y q b = _
    rw [smul_comm s, e, smul_comm (2 * l.M), smul_smul (2 * l.M), mul_assoc]

variable {D : D7}

theorem lat_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) :
    LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, h', -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatIsom V (T.Q.Dw ((i : ℕ) + 1)).EF
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
    rintro V hr rfl h h'
    exact ⟨h, h'⟩
  exact key _ hr hV h h'

theorem latR_range {E : Type} [Field E] [NumberField E] {m r : ℕ} (hr : m = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    GlobalTheory.AdTh.latR hr (LinearMap.range (LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι)) = LinearMap.range ι := by
  subst hr
  unfold GlobalTheory.AdTh.latR
  rw [← LinearMap.range_comp]
  rfl

theorem splitOffBad_one (V : HSp D) : SplitOffBad V 0 1 := by
  refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩,
    fun _ h => absurd h (Finset.notMem_empty _), fun i j => ?_⟩
  rw [show Formalism.L2.Theta.mt V 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]

theorem isFinOf_finR (S T : HSp D) {r : ℕ} (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) :
    GlobalTheory.AdTh.colsR hr (y.submatrix id (Fin.cast hr))ᵀ = y ∧
      GlobalTheory.AdTh.IsFinOf S T (y.submatrix id (Fin.cast hr))ᵀ (finR S hr y) := by
  subst hr
  exact ⟨rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

theorem mem_std_star (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ} (v : Fin n → D.host.E)
    (h : v ∈ Formalism.L2.Pj.stdLat D.host.E n) : (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  intro j _
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j trivial)
  exact Submodule.mem_one.2 ⟨H.bar a, (H.bar_eq a).trans (congrArg star ha)⟩

theorem smul_eq_zero_of_smul_rep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (q : LevQ Dw l) (s : 𝓞 E) (z : Dw.La) (hz : s • (cSep l • levRep q) = l.M • z) :
    s • q = 0 := by
  have hrep : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  rw [← hrep, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hM : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))
  have e : s • levRep q = (l.M : 𝓞 E) • z - (cSep l - 1) • s • levRep q := by
    rw [Nat.cast_smul_eq_nsmul, ← hz, sub_smul, one_smul, smul_comm s, sub_sub_cancel]
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul hM trivial) (Submodule.smul_mem_smul (LevelPairing.cSep_spec _).2 trivial)

end GlobalTheory.OneMapRef.FinDatum
