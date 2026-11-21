import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
import Formalism.FrobeniusOrbits.Statement

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LHost

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

def localUnits (N p : ℕ) : Subgroup (ZMod N)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker

def IsFrobUnit (N p : ℕ) (w : (ZMod N)ˣ) : Prop :=
  ((w : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ∧
    ((w : ZMod N).cast : ZMod (ordProj[p] N)) = 1

def frobUnit (N p : ℕ) : (ZMod N)ˣ := by
  classical
  exact if h : ∃ w, IsFrobUnit N p w then h.choose else 1

section
variable {N : ℕ} {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def cftData (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) : ArithData H where
  q1 := q1
  d := d
  inertia p := Subgroup.toAddSubgroup' ((localUnits N p).map r)
  frob p := Multiplicative.toAdd (r (frobUnit N p))

def dirChar (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) : DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (ψ.toMonoidHom.comp r).toHomUnits

end

def hostN (e q d : ℕ) : ℕ := 2 ^ (e + 2) * q * d

abbrev HA (e : ℕ) : Type := Additive (FrobeniusOrbits.HGrp e)

instance (e : ℕ) : Fintype (HA e) := Fintype.ofFinite _
instance (e : ℕ) : DecidableEq (HA e) := Classical.decEq _

def sgn2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun s := Multiplicative.ofAdd (if s = 1 then 0 else 1)
  map_one' := by simp
  map_mul' := by decide

def legU (N ℓ : ℕ) [Fact ℓ.Prime] (h : ℓ ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  (quadraticChar (ZMod ℓ)).toUnitHom.comp (ZMod.unitsMap h)

theorem d_dvd_hostN (e q d : ℕ) : d ∣ hostN e q d := dvd_mul_left d _
theorem q_dvd_hostN (e q d : ℕ) : q ∣ hostN e q d :=
  dvd_mul_of_dvd_left (dvd_mul_left q _) d
theorem two_dvd_hostN (e q d : ℕ) : 2 ^ (e + 2) ∣ hostN e q d :=
  dvd_mul_of_dvd_left (dvd_mul_right _ q) d

def recMap (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] : (ZMod (hostN e q d))ˣ →* Multiplicative (E0 × HA e) where
  toFun u := Multiplicative.ofAdd
    ((Multiplicative.toAdd (sgn2 (legU _ d (d_dvd_hostN e q d) u)),
      Multiplicative.toAdd (sgn2 (legU _ q (q_dvd_hostN e q d) u))),
      Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u)))
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' u v := by
    simp only [map_mul]
    rfl

def FrobUnitSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → IsFrobUnit N p (frobUnit N p) ∧ ∀ w, IsFrobUnit N p w → w = frobUnit N p

def UnramSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → ¬ p ∣ N → localUnits N p = ⊥ ∧ ((frobUnit N p : (ZMod N)ˣ) : ZMod N) = (p : ZMod N)

section
variable (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H]

def DirCharSpec : Prop :=
  ∀ (N : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ),
    (∀ u : (ZMod N)ˣ, dirChar r ψ (u : ZMod N) = ψ (Multiplicative.toAdd (r u))) ∧
    ∀ x : ZMod N, ¬ IsUnit x → dirChar r ψ x = 0

def InertiaConductor : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p : ℕ), N ≠ 0 → p.Prime →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ ¬ p ∣ (dirChar r ψ).conductor)

def PrimValRamified : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p i : ℕ), p.Prime → 1 ≤ i →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) →
      primVal (cftData q1 d r) ψ (p ^ i) = ψ ((cftData q1 d r).frob p) ^ i) ∧
    ((¬ ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) → primVal (cftData q1 d r) ψ (p ^ i) = 0)

def PrimValPrimitive : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (n : ℕ), N ≠ 0 → n ≠ 0 →
    primVal (cftData q1 d r) ψ n = (dirChar r ψ).primitiveCharacter (n : ZMod (dirChar r ψ).conductor)

end

end Formalism.LFunctionChainParameters.LHost
