import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil
open GlobalTheory.AdelicU (splitProj compFin splitEquiv splitEquivIn splitHom isCMExt_host)
open GlobalTheory.EmbChart (tensAt atPlace idem)
open GlobalTheory.StepData (LatFrame reGL)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocFrame

section Inst

variable {F : Type} [Field F] [NumberField F]

scoped instance relFv (v : HeightOneSpectrum (𝓞 F)) : ValuativeRel (Fv F v) := GlobalTheory.LocalData.complRel v

scoped instance locFieldFv (v : HeightOneSpectrum (𝓞 F)) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

scoped instance borelFv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩

def locChar (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) :
    AddChar (Fv F v) Circle where
  toFun x := ⟨ψ (atPlace v (a * x)), mem_sphere_zero_iff_norm.2 (hψ _)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' x y := Circle.ext (by
    change ψ _ = ψ _ * ψ _
    rw [mul_add, map_add, AddChar.map_add_eq_mul])

end Inst

section Bases

variable {k ι Y : Type} [Field k] [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

def vec (β : LatFrame k ι Y) (i : ι) : Y → k := fun y => β.bas.val y (β.ord i)

def cols (β : LatFrame k ι Y) : Matrix Y ι k := β.bas.val.submatrix id β.ord

def what₂ (β : LatFrame k ι Y) : Matrix ι Y k := (β.bas⁻¹).val.submatrix β.ord id

omit [Fintype ι] [DecidableEq ι] in
theorem cols_apply (β : LatFrame k ι Y) (y : Y) (i : ι) : cols β y i = vec β i y := rfl

omit [Fintype ι] in
theorem rows_mul_cols (β : LatFrame k ι Y) : what₂ β * cols β = 1 := by
  rw [what₂, cols, ← submatrix_mul _ _ _ _ _ Function.bijective_id, Units.inv_mul, submatrix_one_equiv]

end Bases

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def piW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D →+* Fv D.host.F v :=
  (splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)

theorem chart_piW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : GlobalTheory.SplitHecke.Chart (idem τ) v (piW τ) :=
  GlobalTheory.EmbChart.chart_idem τ

theorem piW_incA (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : D.host.E) : piW τ (incA D x) = τ x := by
  change splitProj τ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one, GlobalTheory.AdelicU.splitProj_tmul, one_mul]

theorem hermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => congrFun (congrFun (gram_conjTranspose V) i) j, gram_det_ne V⟩

section Loc

variable (V : HSp D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {ι : Type} [Fintype ι] [DecidableEq ι]
  (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

def locPt : GL ι (Fv D.host.F v) ≃* GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v :=
  β.conj.trans (splitEquiv (isCMExt_host D) (hermND V) τ).symm.toMulEquiv

def locGL : GL ι (Fv D.host.F v) →* GA D V :=
  (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v).comp (locPt V τ β).toMonoidHom

end Loc

section Rep

variable (V : HSp D)

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {ι : Type} [Fintype ι] [DecidableEq ι]
  (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

def locReg : Representation ℂ (GL ι (Fv D.host.F v)) (GA D V → ℂ) :=
  (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ).comp (locGL V τ β)

end Rep

section Position

open GlobalTheory.RootEx

variable {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
  (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [ν.IsAddHaarMeasure]
  {ψ : AddChar k Circle} {σ}

end Position

end GlobalTheory.LocFrame

end
