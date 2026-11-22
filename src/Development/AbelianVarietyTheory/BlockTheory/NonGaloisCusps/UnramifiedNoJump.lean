import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {c : Ω ≃+* Ω}

theorem conj_conj (hc : IsCMConjOm E Ω c) (x : Ω) : c (c x) = x := by
  obtain ⟨⟨j, hj⟩, -⟩ := hc
  apply j.injective
  rw [hj, hj]
  simp

theorem conj_symm (hc : IsCMConjOm E Ω c) (x : Ω) : c.symm x = c x := by
  rw [RingEquiv.symm_apply_eq, conj_conj hc]

def conjElt (hc : IsCMConjOm E Ω c) (g : G E Ω) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (c.symm.trans g.toRingEquiv).trans c) (fun x => by
    obtain ⟨y, hy⟩ := hc.2 x
    change c (g (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
    rw [conj_symm hc, hy, AlgEquiv.commutes, ← hy, conj_conj hc])

theorem conjElt_apply (hc : IsCMConjOm E Ω c) (g : G E Ω) (x : Ω) :
    conjElt hc g x = c (g (c.symm x)) := rfl

def conjHom (hc : IsCMConjOm E Ω c) : G E Ω →* G E Ω where
  toFun := conjElt hc
  map_one' := by
    ext x
    simp [conjElt_apply]
  map_mul' g h := by
    ext x
    simp [conjElt_apply]

end Conj

variable (D : D7)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

end
