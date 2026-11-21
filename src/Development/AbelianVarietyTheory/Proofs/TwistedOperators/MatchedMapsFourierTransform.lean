import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

theorem mem_of_pure {A : Type} [AddCommGroup A] [Module ℂ A] {ι : Type} [Fintype ι] {B : ι → Type}
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (S : Submodule ℂ (A ⊗[ℂ] (⨂[ℂ] i, B i)))
    (h : ∀ x φ, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ ∈ S) : ∀ t, t ∈ S := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r φ => rw [TensorProduct.tmul_smul]; exact S.smul_mem r (h x φ)
    | add y z hy hz => rw [TensorProduct.tmul_add]; exact S.add_mem hy hz
  | add s t hs ht => exact S.add_mem hs ht

theorem mem_of_tprod {ι : Type} [Fintype ι] {B : ι → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
    (S : Submodule ℂ (⨂[ℂ] i, B i)) (h : ∀ φ, PiTensorProduct.tprod ℂ φ ∈ S) : ∀ y, y ∈ S := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r φ => exact S.smul_mem r (h φ)
  | add y z hy hz => exact S.add_mem hy hz

def ext (M : Model σ Y W) (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ :=
  fun v => if h : v ∈ T then ((φ ⟨v, h⟩ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v

variable (M : Model σ Y W) (T : Finset (Pl F))

theorem ext_of_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) :
    ext M T φ v.1 = (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  simp [ext, v.2]

theorem ext_of_not_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl F) (hv : v ∉ T) :
    ext M T φ v = M.vac v := by
  simp [ext, hv]

theorem ext_mem_SB {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (v : Pl F) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact (hM.vac v).1

theorem ext_vac (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = M.vac v := by
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact ext_of_not_mem M T φ v hv

theorem ext_std {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hM.std] with v h1 h2
  rw [h1, h2]

theorem ext_update [DecidableEq T] (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T)
    (z : ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ext M T (Function.update φ v z) = Function.update (ext M T φ) v.1 (z : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  funext w
  by_cases hw : w ∈ T
  · by_cases hwv : w = v.1
    · subst hwv
      rw [ext_of_mem M T _ v, Function.update_self, Function.update_self]
    · have hne : (⟨w, hw⟩ : T) ≠ v := fun e => hwv (congrArg Subtype.val e)
      rw [ext_of_mem M T _ ⟨w, hw⟩, Function.update_of_ne hwv, Function.update_of_ne hne, ext_of_mem M T _ ⟨w, hw⟩]
  · have hwv : w ≠ v.1 := fun e => hw (e ▸ v.2)
    rw [ext_of_not_mem M T _ w hw, Function.update_of_ne hwv, ext_of_not_mem M T _ w hw]

end GlobalTheory.HoweGlobal.Transfer

end

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (T : Finset (Pl F))

theorem rest_ext {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ)

theorem acts_ext [DecidableEq T] {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hM φ)) ?_
  rw [ext_of_mem]
  exact h

theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w) (hM : M.IsGood ψ)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hM φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobal.Transfer

end
