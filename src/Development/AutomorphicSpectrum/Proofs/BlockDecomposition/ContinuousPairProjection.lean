import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FinConv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocGLMemKglob
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinTestTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC GlobalTheory.CompanionTheory.FinLevelTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem exists_lift (Y : ∀ w : Pl E, GLw n w) (hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w n) :
    ∃ x : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) x = Y w := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun w => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem eventually_mem_KGL (g : GL (Fin n) (Af E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem coe_pair_compact_subgroup (a b : ℕ) (w : Pl E) : (K2 a b w : Set (GLw a w × GLw b w)) =
    (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w b : Set (GLw b w)) := Subgroup.coe_prod _ _

theorem mem_prod_Kf {x : Gf E a b} :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ w : Pl E, atHom a b w x ∈ K2 a b w := by
  simp only [Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap, forall_and]
  rfl

theorem isRestrW (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (atHom (E := E) a b) (K2 a b) := by
  have hset : {x : Gf E a b | ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
      (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
    Set.ext fun x => (mem_prod_Kf (x := x)).symm.trans Subgroup.mem_prod
  refine ⟨fun w => w.elim, continuous_atHom, fun w => ?_, fun w => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  · exact Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.fst (H w))
      (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.snd (H w))
  · filter_upwards [eventually_mem_KGL x.1, eventually_mem_KGL x.2] with w h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun w => (y w).1) (hy.mono fun w h => h.1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun w => (y w).2) (hy.mono fun w h => h.2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun w => Prod.ext (h₁ w) (h₂ w)⟩
  · rw [hset]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← hset]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf

theorem eventually_eq_indicator {φ : Fam E a b} (h : IsTestP φ) :
    ∀ᶠ w : Pl E in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact h.2

theorem hasCompactSupport_loc {φ : Fam E a b} (h : IsTestP φ) (w : Pl E) : HasCompactSupport (φ w) := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact (h.1 w).1

theorem factors_ne_zero {S : Set (Pl E)} {φ₁ φ₂ : Fam E a b} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) {y : Gf E a b}
    (hy : finFn S φ₁ φ₂ y ≠ 0) (w : Pl E) (hw : w ∈ S) :
    φ₁ w (atW w y) ≠ 0 ∧ (IsSplitAt w → φ₂ w (atW w (thP E a b y)) ≠ 0) := by
  set g : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg
  have hone : ∀ᶠ w in cofinite, g w = 1 := by
    filter_upwards [eventually_eq_indicator h₁, eventually_eq_indicator h₂, (isRestrW a b).eventually_mem y,
      (isRestrW a b).eventually_mem (thP E a b y)] with w e₁ e₂ m₁ m₂
    have m₁' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₁
    have m₂' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₂
    simp only [hg]
    rw [e₁, e₂, Set.indicator_of_mem m₁', Set.indicator_of_mem m₂']
    simp
  have hfin : (S ∩ Function.mulSupport g).Finite :=
    (eventually_cofinite.1 hone).subset fun w hw => hw.2
  have hz : g w ≠ 0 := by
    intro h0
    apply hy
    change ∏ᶠ w ∈ S, g w = 0
    rw [finprod_mem_eq_prod g hfin]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 ⟨hw, by simp [Function.mem_mulSupport, h0]⟩) h0
  refine ⟨left_ne_zero_of_mul hz, fun hs => ?_⟩
  have hz' := right_ne_zero_of_mul hz
  rwa [if_pos hs] at hz'

end GlobalTheory.CompanionTheory.FinTestTw

end
