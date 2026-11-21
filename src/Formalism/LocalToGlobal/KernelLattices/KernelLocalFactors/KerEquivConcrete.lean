import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivGen
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Inv

theorem mem_divs_of {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.mp h
  · simp at h

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word}

open Classical in

theorem cB_div_int (P : rowSG Pr sel mu) :
    IntAt P.1 (((Col.qOf P.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) := by
  have hq : (Col.qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (qOf_pos P.1).ne'
  have e : ((cBof sel mu cst u : ℕ) : X.E) =
      (Col.qOf P.1 : X.E) ^ cst.B * (((Pr.T u * (∏ P' ∈ Finset.univ.erase P, Col.qOf P'.1) ^ cst.B : ℕ)) : X.E) := by
    unfold cBof
    rw [← Finset.mul_prod_erase Finset.univ (fun P' : rowSG Pr sel mu => Col.qOf P'.1) (Finset.mem_univ P)]
    push_cast
    ring
  rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  have := xqIntAt_intCast (P := P.1) ((Pr.T u * (∏ P' ∈ Finset.univ.erase P, Col.qOf P'.1) ^ cst.B : ℕ) : ℤ)
  simpa using this

end Inv

end Formalism.L2.Ker
