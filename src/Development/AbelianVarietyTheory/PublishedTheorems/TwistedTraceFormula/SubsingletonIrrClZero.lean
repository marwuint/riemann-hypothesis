import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.SmGL.SegModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_irrCl_zero : Subsingleton (IrrCl (GL (Fin 0) k)) := by
  have key : ∀ σ : IrrRep (GL (Fin 0) k),
      Nonempty ((ofChar (1 : GL (Fin 0) k →* ℂˣ)).Equiv σ.ρ) := by
    intro σ
    have := nontrivial_of_irreducible σ.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.V)
    have h1 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
    let f : (ofChar (1 : GL (Fin 0) k →* ℂˣ)).IntertwiningMap σ.ρ :=
      ⟨LinearMap.toSpanSingleton ℂ σ.V v, fun g => by rw [h1 g]; ext; simp⟩
    have hf : Function.Injective f := LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
    obtain ⟨φ⟩ := (IsSubquotient.of_injective f hf).nonempty_equiv (isIrreducible_ofChar _) σ.irr
    exact ⟨φ.symm⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨φ⟩ := key a.rep
  obtain ⟨ψ⟩ := key b.rep
  rw [← a.cl_rep, ← b.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨φ.symm.trans ψ⟩

end GlobalTheory.SmGL.SegModel
