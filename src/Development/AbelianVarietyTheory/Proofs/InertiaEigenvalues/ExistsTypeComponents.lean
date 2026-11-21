import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec

theorem exists_isComp_of_rowDepth {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h : GlobalTheory.HeightCounting.RowDepth D rep) : ∃ cp, IsComp I rep cp := by
  have : ∀ σ k v, ∃ c : GlobalTheory.GoodTypes.LocRep D k, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ c = pull I k v τ := by
    intro σ k v
    obtain ⟨s, τ, hs, h1, -⟩ := h σ k v
    have gen : ∀ (w) (e : s.w = w), ∃ τ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E)),
        GlobalTheory.HeightCounting.IsLocS (rep σ).S s (e ▸ τ') := by
      rintro _ rfl
      exact ⟨τ, h1⟩
    obtain ⟨τ', a⟩ := gen _ hs
    exact ⟨_, s, hs, τ', a, rfl⟩
  choose c hc using this
  exact ⟨c, hc⟩

end GlobalTheory.TypeRec
