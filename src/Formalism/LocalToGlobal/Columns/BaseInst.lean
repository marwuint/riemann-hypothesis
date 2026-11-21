import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
import Formalism.LocalToGlobal.UnitaryNorms.Lemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

instance fin_KQ (d : ℕ) : FiniteDimensional ℚ (KQ d) := fin_sqQ _

instance normal_KQ (d : ℕ) : Normal ℚ (KQ d) := normal_sqQ _

def quadFields (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL) : Fields where
  F := ℚ
  E := KQ d
  K := CoF ι LL
  nfE := { to_charZero := inferInstance, to_finiteDimensional := fin_KQ d }
  starE := starLL ι (KQ d)
  Tau := Unit
  emb := fun _ => (tauLL hE (KQ d).val).toRingHom

section DegTwo

variable (X : Fields)

theorem conjO_coe (x : 𝓞 X.E) : ((X.conjO x : 𝓞 X.E) : X.E) = star (x : X.E) := rfl

end DegTwo

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def iQb : Qb := Classical.choose (exists_sqrt (-((1 : ℕ) : ℤ)))

theorem iQb_mem : iQb ∈ sqrts (-((1 : ℕ) : ℤ)) := Classical.choose_spec (exists_sqrt (-((1 : ℕ) : ℤ)))

theorem iQb_sq : iQb ^ 2 = -1 := by
  have h : iQb ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb) := iQb_mem
  rw [h]; simp

abbrev gaussFields : Fields := quadFields 1 ι LL hE

def iE : (gaussFields ι LL hE).E := (⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)

theorem iE_sq : iE ι LL hE ^ 2 = -1 := by
  have h : ((⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)) ^ 2 = -1 := Subtype.val_injective iQb_sq
  exact h

def iO : 𝓞 (gaussFields ι LL hE).E :=
  ⟨iE ι LL hE, IsIntegral.of_pow (n := 2) (by norm_num) (by rw [iE_sq]; exact isIntegral_one.neg)⟩

def gz (a b : ℤ) : 𝓞 (gaussFields ι LL hE).E := (a : 𝓞 (gaussFields ι LL hE).E) + (b : 𝓞 (gaussFields ι LL hE).E) * iO ι LL hE

end Gauss

instance fin_cyc : FiniteDimensional ℚ (cycQ 780) := fin_adjoin (finite_pow_eq 780 (by norm_num) 1)

instance normal_cyc : Normal ℚ (cycQ 780) := normal_adjoin fun s x hx => by
  show (s x) ^ 780 = 1
  rw [← map_pow, show x ^ 780 = 1 from hx, map_one]

end Formalism.L2.Col
