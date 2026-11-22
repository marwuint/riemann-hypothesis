import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeRec

theorem pull_iso_of_cls_eq {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls τ) : Nonempty (pull I k v σ ≅ pull I k v τ) := by
  have h1 : σ.cl = τ.cl := by
    have := (Sigma.mk.inj_iff.1 h).2
    exact eq_of_heq this
  obtain ⟨φ⟩ := GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h1
  exact ⟨Rep.mkIso (Representation.Equiv.mk φ.toLinearEquiv fun g =>
    φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g))⟩

end GlobalTheory.TypeRec

end
