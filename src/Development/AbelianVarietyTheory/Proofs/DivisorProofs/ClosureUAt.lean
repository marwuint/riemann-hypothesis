import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Adelic

variable (σ : E →ₐ[F] E) {n : ℕ} (X : Spc F E n)

end Adelic

def cv (σ : E →ₐ[F] E) (v : Pl F) : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ

def liftE (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E :=
  TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id

instance isModTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

end GlobalTheory.HoweLocal
