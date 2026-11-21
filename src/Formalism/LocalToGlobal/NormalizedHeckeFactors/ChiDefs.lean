import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

section hecke

variable {E : Type} [Field E] [NumberField E]

@[ext]
structure HC (E : Type) [Field E] [NumberField E] where
  χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ
  cont : Continuous χ
  triv : ∀ a : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom a) = 1

instance : Mul (HC E) where
  mul χ ψ := ⟨χ.χ * ψ.χ, χ.cont.mul ψ.cont, fun a => by rw [MonoidHom.mul_apply, χ.triv a, ψ.triv a, one_mul]⟩

instance : Inv (HC E) where
  inv χ := ⟨χ.χ⁻¹, χ.cont.inv, fun a => by rw [MonoidHom.inv_apply, χ.triv a, inv_one]⟩

instance : One (HC E) where
  one := ⟨1, continuous_const, fun _ => rfl⟩

@[simp] theorem HC.mul_χ (χ ψ : HC E) : (χ * ψ).χ = χ.χ * ψ.χ := rfl
@[simp] theorem HC.inv_χ (χ : HC E) : (χ⁻¹).χ = χ.χ⁻¹ := rfl
@[simp] theorem HC.one_χ : (1 : HC E).χ = 1 := rfl

open scoped Classical in

def locM (P : HeightOneSpectrum (𝓞 E)) : P.adicCompletion E →* AdeleRing (𝓞 E) E where
  toFun x := ((1 : InfiniteAdeleRing E),
    (RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletionIntegers E) P x :
      FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [RestrictedProduct.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E) * 1, _ * _)
    rw [RestrictedProduct.mulSingle_mul, mul_one]
    rfl

def HC.At (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) (α : ℂ) : Prop :=
  (∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1) ∧
    ∀ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) →
      ((χ.χ (Units.map (locM P) ϖ) : ℂˣ) : ℂ) = α

theorem HC.At.mul {χ ψ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (h : χ.At P a) (h' : ψ.At P b) :
    (χ * ψ).At P (a * b) := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · simp [h.1 u hu, h'.1 u hu]
  · simp [← h.2 ϖ hϖ, ← h'.2 ϖ hϖ]

theorem HC.At.inv {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a : ℂ} (h : χ.At P a) : (χ⁻¹).At P a⁻¹ := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · simp [h.1 u hu]
  · simp [← h.2 ϖ hϖ]

theorem exists_unif (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hv : Valued.v (π : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [P.valuedAdicCompletion_eq_valuation' π, hπ]
  have h0 : (π : P.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ h0, hv⟩

theorem HC.At.unique {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (ha : χ.At P a) (hb : χ.At P b) : a = b := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif P
  rw [← ha.2 ϖ hϖ, ← hb.2 ϖ hϖ]

open scoped Classical in

def locInf (v : InfinitePlace E) : v.Completion →* AdeleRing (𝓞 E) E where
  toFun x := ((Pi.mulSingle v x : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((Pi.mulSingle v (1 : v.Completion) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [Pi.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((Pi.mulSingle v (x * y) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((Pi.mulSingle v x : InfiniteAdeleRing E) * Pi.mulSingle v y, (1 : FiniteAdeleRing (𝓞 E) E) * 1)
    rw [Pi.mulSingle_mul, mul_one]

def HC.Unr (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1

def HC.IsUnitArg (χ : HC E) (τ : E →+* ℂ) : Prop :=
  ∀ f : (InfinitePlace.mk τ).Completion →+* ℂ, Continuous f → (∀ x : E, f (x : (InfinitePlace.mk τ).Completion) = τ x) →
    ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
      ((χ.χ (Units.map (locInf (InfinitePlace.mk τ)) z) : ℂˣ) : ℂ) = f z / (‖f z‖ : ℂ)

end hecke

section read

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def Read {A K L : Type} [CommRing A] [CommRing K] [CommRing L] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω)
    (φ : G E Ω →* Aˣ) (rd : A →+* K) (eL : L →+* K) (embC : L →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  ∃ B : Finset (HeightOneSpectrum (𝓞 E)), ∀ P ∉ B, ∃ α : ℂ, χ.At P α ∧ ∃ x : L,
    embC x = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ w ∧
    ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ → rd (φ σ : A) = eL x

abbrev ReadC {A : Type} [CommRing A] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (φ : G E Ω →* Aˣ)
    (rd : A →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  Read pl φ rd (RingHom.id ℂ) (RingHom.id ℂ) χ w

theorem normV_ne_zero (P : HeightOneSpectrum (𝓞 E)) : normV P ≠ 0 := by
  have h : normV P = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [h]
  exact fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem finite_placesOver (l : ℕ) [Fact l.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

end read

section rcg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def UnrOut {A : Type} [Group A] (φ : G E Ω →* A) (Q : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1

def IsRcgChar (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) {A : Type} [CommGroup A]
    (φ : G E Ω →* A) : Prop :=
  Finite A ∧ (∀ x : A, ∃ n : ℕ, x ^ (l ^ n) = 1) ∧ IsOpen (φ.ker : Set (G E Ω)) ∧ AntiHom c φ ∧ UnrOut φ Q

def rcgKer (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Subgroup (G E Ω) where
  carrier := {g | ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ g = 1}
  one_mem' := fun A _ φ _ => map_one φ
  mul_mem' := fun {a b} ha hb A _ φ h => by rw [map_mul, ha A φ h, hb A φ h, one_mul]
  inv_mem' := fun {a} ha A _ φ h => by rw [map_inv, ha A φ h, inv_one]

theorem mem_rcgKer {c : Ω ≃+* Ω} {l : ℕ} {Q : Set (HeightOneSpectrum (𝓞 E))} {g : G E Ω} :
    g ∈ rcgKer c l Q ↔ ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ g = 1 := Iff.rfl

instance rcgKer_normal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : (rcgKer c l Q).Normal where
  conj_mem g hg h A _ φ hφ := by
    rw [map_mul, map_mul, hg A φ hφ, mul_one, map_inv, mul_inv_cancel]

abbrev RCGGal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  G E Ω ⧸ rcgKer c l Q

instance rcgGal_comm (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : CommGroup (RCGGal c l Q) :=
  { (inferInstance : Group (RCGGal c l Q)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      refine mem_rcgKer.2 fun A _ φ _ => ?_
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (φ b) (φ a), inv_mul_cancel] }

end rcg

end Formalism.L2.NC
