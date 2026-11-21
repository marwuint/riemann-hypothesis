import Formalism.MahlerMeasure.Statement

namespace Formalism.GM

open MvPolynomial

namespace QuotientRingDecomposition

variable {R : Type} [CommRing R] {r Q : ℕ}

noncomputable def E (e : Fin r → Fin Q) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => ((e i : ℕ)))

noncomputable def divQ (Q : ℕ) (m : Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i / Q)

@[simp] lemma E_apply (e : Fin r → Fin Q) (i : Fin r) : E e i = (e i : ℕ) := rfl

@[simp] lemma divQ_apply (m : Fin r →₀ ℕ) (i : Fin r) : divQ Q m i = m i / Q := rfl

end QuotientRingDecomposition

end Formalism.GM
