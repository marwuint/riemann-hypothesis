import Mathlib
import Formalism.LocalToGlobal.Columns.BaseHost
import Formalism.LocalToGlobal.Columns.NonDeg

open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host Formalism.FrobeniusOrbits

theorem finiteDimensional_cyclotomic {N : ℕ} (hN : 0 < N) : FiniteDimensional ℚ (cycQ N) := fin_adjoin (finite_pow_eq N hN 1)

theorem normal_cyclotomic (N : ℕ) : Normal ℚ (cycQ N) := normal_adjoin fun s x hx => by
  show (s x) ^ N = 1
  rw [← map_pow, show x ^ N = 1 from hx, map_one]

theorem cyclotomic_mono_of_dvd {M N : ℕ} (h : M ∣ N) : cycQ M ≤ cycQ N := by
  unfold cycQ
  apply adjoin.mono
  intro z hz
  obtain ⟨c, rfl⟩ := h
  show z ^ (M * c) = 1
  rw [pow_mul, show z ^ M = 1 from hz, one_pow]

section Split

variable {X : Fields}

def toyConjugatePrime (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, X.conjO_invol]
      exact hx
    rw [h] at h1
    have h2 : X.conjO x = 0 := h1
    apply hx0
    rw [← X.conjO_invol x, h2, map_zero]

theorem mem_conjugatePrime_iff (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ (toyConjugatePrime P).asIdeal ↔ X.conjO x ∈ P.asIdeal := Iff.rfl

end Split

section HostZ

variable {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

def hwQb (d : ℕ) : Qb := Classical.choose (exists_sqrt (-(d : ℤ)))

theorem hwQb_mem (d : ℕ) : hwQb d ∈ sqrts (-(d : ℤ)) := Classical.choose_spec (exists_sqrt (-(d : ℤ)))

theorem hwQb_sq (d : ℕ) : hwQb d ^ 2 = -(d : Qb) := by
  have h : hwQb d ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hwQb_mem d
  rw [h]; simp

theorem hwQb_mem_EQ : hwQb H.d ∈ H.EQ :=
  H.KQ_le_EQ (sqrts_sub _ (hwQb_mem H.d))

def hwE : (hostFields H ι LL hE).E := (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)

theorem hwE_sq : hwE H ι LL hE ^ 2 = -(H.d : (hostFields H ι LL hE).E) := by
  have h : ((⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)) ^ 2 = -(H.d : H.EQ) := Subtype.val_injective (by
    show hwQb H.d ^ 2 = _
    rw [hwQb_sq]
    simp)
  exact h

def hwO : 𝓞 (hostFields H ι LL hE).E :=
  ⟨hwE H ι LL hE, IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hwE_sq]; exact (isIntegral_natCast H.d).neg)⟩

def hz (a b : ℤ) : 𝓞 (hostFields H ι LL hE).E :=
  (a : 𝓞 (hostFields H ι LL hE).E) + (b : 𝓞 (hostFields H ι LL hE).E) * hwO H ι LL hE

end HostZ

def toyFirstParameter : ℕ := 5812161310401002497

def toySecondParameter : ℕ := 10580716767734447210497

def nd2T : ℕ := 56194698826333161291662198507648755438473557111144279252246328293211974734191775333427954228508737780869538570051953955243454133837703637171933755744705457828859522702609327843686445057

def columnDegreeBound : ℕ := 175899382716746995995794692370095808443505986460327359316203003947391329197558870718244898147225575657278023097973275990081581282841096000378419862656504066221696375796925055794734493697

def nd2N : ℕ := 204572886511813553061037407562329625995783655411690436542768105489192394035355663504895707466548678171695054788500010062488923813826764064938234928730947196464262768270018653110228498338042697795156970159903677022807129186961004810571117527615229822789011462114279289419559348825463524785325415815445950503458435921145728668675289394505621558664460319354973532563002004291054537384997546176343222140701606270894674242774158138205418672187221164903157007908864

theorem example_level_pos : 0 < nd2N := by decide +kernel

theorem exampleField_le_cyclotomic : Examples₂.H0.EQ ≤ cycQ nd2N :=
  (condEQ Examples₂.H0).1.trans (cyclotomic_mono_of_dvd (by decide +kernel))

section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)

abbrev nd2X : Fields := hostFields Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL)

abbrev nd2z (a b : ℤ) : 𝓞 (nd2X LL hLL).E := hz Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) a b

def toyPrimes : Primes (nd2X LL hLL) where
  cond := Examples₂.H0.condN
  g := ![toyFirstParameter, toySecondParameter]
  piG := ![nd2z LL hLL 1 (((Examples₂.H0.condN : ℕ) : ℤ) * 18),
    nd2z LL hLL 1 (((Examples₂.H0.condN : ℕ) : ℤ) * 768)]
  Word := Fin 2
  T := ![nd2T, columnDegreeBound]
  piT := ![nd2z LL hLL 1 (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 468),
    nd2z LL hLL 1 (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 828)]

end Inst

instance fin_cycNd2 : FiniteDimensional ℚ (cycQ nd2N) := finiteDimensional_cyclotomic example_level_pos

instance normal_cycNd2 : Normal ℚ (cycQ nd2N) := normal_cyclotomic nd2N

end Formalism.L2.Col
