import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LogVandermondeBounds.FinrankFiberSumZero
import Formalism.LogVandermondeBounds.GaussOperatorProductFormula

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Coord

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

structure CoordAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, co (x + y) = co x + co y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → co x = 0
  surj : ∀ c, ∃ x ∈ N, co x = c
  ker : ∀ x ∈ N, co x = 0 → x ∈ P.asIdeal • N

structure FunAt (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop where
  add : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, f (x + y) = f x + f y
  smul : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, f (a • x) = Ideal.Quotient.mk P.asIdeal a * f x
  off : ∀ x, x ∉ localization₂ P.asIdeal N → f x = 0

def coF {P : HeightOneSpectrum (𝓞 E)} (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)) (c : Fin n → 𝓞 E ⧸ P.asIdeal)
    (y : Sp E n) : 𝓞 E ⧸ P.asIdeal := ∑ i, c i * co y i

def dualV {κ : Type} [CommRing κ] (x : Fin n → κ) : Fin n → κ := Classical.epsilon fun c => ∑ i, c i * x i = 1

def liftV {P : HeightOneSpectrum (𝓞 E)} (N : Submodule (𝓞 E) (Sp E n)) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.asIdeal) : Sp E n := Classical.epsilon fun y => y ∈ N ∧ co y = x

end Coord

section Fib

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.fibF (d : Deco E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : Deco E n ST SG := d.repl P d.N (coF co c)

def DecoSet.fibF (d : DecoSet E n ST SG) (P : ST) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (c : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet E n ST SG :=
  open Classical in if h : (d.1.fibF P co c).Ok then ⟨_, h⟩ else d

def DecoSet.fibX (d : DecoSet E n ST SG) (P : ST) (q : 𝓞 E) (co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal))
    (x : Fin n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet E n ST SG :=
  (d.fibF P co (dualV x)).up P q (liftV d.1.N co x)

def DecoSet.trSet (P : ST) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | d'.1 = d.1.repl P d.1.N (d'.1.f P)}

theorem Deco.repl_act (d : Deco E n ST SG) (g : Sp E n ≃ₗ[E] Sp E n) (h : GLG E n SG) (P : ST)
    (N' : Submodule (𝓞 E) (Sp E n)) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) :
    (d.act g h).repl P (gmap g N') (fun y => f' (g.symm y)) = (d.repl P N' f').act g h := by
  classical
  ext1
  · rfl
  · funext Q y
    by_cases hQ : Q = P
    · subst hQ
      simp only [Deco.repl, Deco.act, Function.update_self]
    · simp only [Deco.repl, Deco.act, Function.update_of_ne hQ]
  · rfl

theorem DecoSet.rel_smul_iff {r : DecoSet E n ST SG → DecoSet E n ST SG → Prop}
    (hr : ∀ (a : UF E n × GLG E n SG) d d', r d d' → r (a • d) (a • d')) (a : UF E n × GLG E n SG)
    (d d' : DecoSet E n ST SG) : r (a • d) (a • d') ↔ r d d' := by
  refine ⟨fun h => ?_, hr a d d'⟩
  have := hr a⁻¹ _ _ h
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem DecoSet.smul_mem_trSet (a : UF E n × GLG E n SG) (P : ST) (d d' : DecoSet E n ST SG) :
    a • d' ∈ (a • d).trSet P ↔ d' ∈ d.trSet P := by
  refine DecoSet.rel_smul_iff (r := fun d d' => d' ∈ d.trSet P) (fun a d d' h => ?_) a d d'
  change (d'.1.act a.1.1 a.2) = _
  have h' : d'.1 = d.1.repl P d.1.N (d'.1.f P) := h
  conv_lhs => rw [h']
  exact (d.1.repl_act a.1.1 a.2 P d.1.N (d'.1.f P)).symm

theorem DecoSet.trSet_finite (P : ST) (d : DecoSet E n ST SG) : (d.trSet P).Finite :=
  (DecoSet.finite_fibre (ST := ST) (SG := SG) d.1.N d.2.lat.fg).subset fun d' hd' => by
    have h1 : d'.1 = d.1.repl P d.1.N (d'.1.f P) := hd'
    have := congrArg Deco.N h1
    exact this

structure SepElt (ST : Finset (HeightOneSpectrum (𝓞 E))) (a : 𝓞 E) : Prop where
  conj : ∀ P : ST, cO E a ∈ P.1.asIdeal
  off : ∀ P : ST, a ∉ P.1.asIdeal

end Fib

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)

def trG (P : ST) : Module.End X.K (formGSD C Λ).EqFun :=
  (LocOp.ofNbr (S := formGSD C Λ) (S' := formGSD C Λ) (MonoidHom.id _)
    (fun d => (DecoSet.trSet_finite P d).toFinset) LinearMap.id
    (fun g d' d => by
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact DecoSet.smul_mem_trSet (FormG.incl Λ g) P d' d) (fun _ _ => rfl)).op

variable {C Λ}

def resX {R : Type} (d : DecoSet X.E n ST SG) (P : ST) (q : 𝓞 X.E)
    (co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)) (ℓ : C.V → R) (φ : (formGSD C Λ).EqFun) :
    (Fin n → 𝓞 X.E ⧸ P.1.asIdeal) → R :=
  fun x => ℓ ((φ : (formGSD C Λ).D → (formGSD C Λ).V) (d.fibX P q co x))

end Ops

@[reducible] def resField {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal

@[reducible] def resFintype {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _

section Below

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ} (emb : ι → E →+* K)

def SameBelow (w : HeightOneSpectrum (𝓞 K)) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ τ, (∀ x ∈ L, ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L') ∧
    ∀ x ∈ L', ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L

end Below

end Formalism.L2.Col
