import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSplitIdemIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {X : ThetaX D} {T : ThetaTied D X}

def Rel (C : SplittingKernelQuotients.Core T) (ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ))
    (om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Prop :=
  ∀ (A B : HSp D) (hr : A.rank < B.rank),
    (∀ Φ, ev A B Φ ∘ kap A B = C.eUp A B hr.le Φ) ∧ (∀ Φ, ev B A Φ ∘ kapT A B = C.eDn A B hr Φ) ∧
    ∀ χA χB hs g h, om A B χA χB (g, h) = C.omUp A B hr.le χA χB hs (g, h) ∧
      om B A χB χA (h, g) = C.omDn A B hr χA χB hs (g, h)

def Twist (C : SplittingKernelQuotients.Core T) : Prop :=
  ∀ (A B : HSp D) (hr : A.rank < B.rank) χA χB χA' χB' hs hs' (g : GA D A) (h : GA D B), ∃ cg ch : Circle,
    HeisenbergWeilMatrices.IsTildeVal D (T.eChr χB' / T.eChr χB) (HeisenbergWeilMatrices.detA A g) cg ∧
    HeisenbergWeilMatrices.IsTildeVal D (T.eChr χA' / T.eChr χA) (HeisenbergWeilMatrices.detA B h) ch ∧
    C.om A B hr.le χA' χB' hs' (g, h) = ((cg⁻¹ * ch : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h)

section FromRel

variable {C : SplittingKernelQuotients.Core T} {ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ)}
  {om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))}

theorem Rel.up (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    C.eUp A B hr.le (om A B χA χB (g, h) Φ) = C.om A B hr.le χA χB hs (g, h) (C.eUp A B hr.le Φ) := by
  rw [((R A B hr).2.2 χA χB hs g h).1]
  simp [SplittingKernelQuotients.Core.omUp, LinearEquiv.conj_apply]

theorem Rel.dn (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    C.eDn A B hr (om B A χB χA (h, g) Φ) = C.om A B hr.le χA χB hs (g, h) (C.eDn A B hr Φ) := by
  rw [((R A B hr).2.2 χA χB hs g h).2]
  simp [SplittingKernelQuotients.Core.omDn, LinearEquiv.conj_apply]

theorem Rel.smul (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB χA' χB' hs hs' g h} {c : ℂ}
    (H : C.om A B hr.le χA' χB' hs' (g, h) = c • C.om A B hr.le χA χB hs (g, h)) :
    om A B χA' χB' (g, h) = c • om A B χA χB (g, h) ∧ om B A χB' χA' (h, g) = c • om B A χB χA (h, g) := by
  constructor
  · refine LinearMap.ext fun Φ => (C.eUp A B hr.le).injective ?_
    rw [R.up hr hs', H, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, R.up hr hs]
  · refine LinearMap.ext fun Φ => (C.eDn A B hr).injective ?_
    rw [R.dn hr hs', H, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, R.dn hr hs]

theorem tilde_val {χ : (AE D)ˣ →* Circle} (h0 : ResEta D χ 0) (V : HSp D) (g : GA D V) {x : (AE D)ˣ}
    (hx : IsDetRoot V g x) : HeisenbergWeilMatrices.IsTildeVal D χ (HeisenbergWeilMatrices.detA V g) (χ x) := by
  refine ⟨⟨x, (isDetRoot_iff V g x).1 hx⟩, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x y hx ((isDetRoot_iff V g y).2 hy)
  obtain ⟨η, hη⟩ := h0.1
  rw [map_mul, h0.2 η hη, pow_zero, mul_one]

theorem tilde_one {χ : (AE D)ˣ →* Circle} {u c} (h : HeisenbergWeilMatrices.IsTildeVal D (χ / χ) u c) : c = 1 := by
  obtain ⟨x, hx⟩ := h.1
  rw [← h.2 x hx, div_self', MonoidHom.one_apply]

theorem tilde_mul {χ ν : X.Chr} {V : HSp D} {g : GA D V} {x c} (hx : IsDetRoot V g x)
    (h : HeisenbergWeilMatrices.IsTildeVal D (T.eChr (χ * ν) / T.eChr χ) (HeisenbergWeilMatrices.detA V g) c) : c = T.eChr ν x := by
  rw [map_mul, mul_div_cancel_left] at h
  exact (h.2 x ((isDetRoot_iff V g x).1 hx)).symm

theorem Twist.target (H : Twist C) (A B : HSp D) (hr : A.rank < B.rank) (χA χB ν hs hs' g h x) (hx : IsDetRoot A g x) :
    C.om A B hr.le χA (χB * ν) hs' (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h) := by
  obtain ⟨cg, ch, h1, h2, h3⟩ := H A B hr χA χB χA (χB * ν) hs hs' g h
  rwa [tilde_one h2, tilde_mul hx h1, mul_one] at h3

theorem Rel.twist (R : Rel C ev om) : TwRule T om → Twist C := by
  intro H A B hr χA χB χA' χB' hs hs' g h
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D A g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D B h
  have z : ∀ {χ χ' : X.Chr} {n}, ResEta D (T.eChr χ) n → ResEta D (T.eChr χ') n → ResEta D (T.eChr (χ' / χ)) 0 :=
    fun {χ χ' n} h h' => by
      rw [div_eq_mul_inv, map_mul, map_inv]
      exact resEta_parity (resEta_mul h' (resEta_inv h)) (by omega)
  have hA := z hs.resA hs'.resA
  have hB := z hs.resB hs'.resB
  have e1 := H.twW_up A B χA' χB (χB' / χB) hr hs'.resA hs.resB hB g h x hx
  have e2 := H.twV_up A B χA χB (χA' / χA) hr hs.resA hs.resB hA g h y hy
  rw [mul_div_cancel] at e1 e2
  refine ⟨_, _, map_div T.eChr _ _ ▸ tilde_val hB A g hx, map_div T.eChr _ _ ▸ tilde_val hA B h hy, ?_⟩
  refine LinearMap.ext fun f => ?_
  obtain ⟨Φ, rfl⟩ := (C.eUp A B hr.le).surjective f
  rw [LinearMap.smul_apply, ← R.up hr hs, ← R.up hr hs', e1, e2, smul_smul, LinearMap.smul_apply, map_smul,
    Circle.coe_mul, map_div, map_div]

end FromRel

end GlobalTheory.WeilTieCompare

end
