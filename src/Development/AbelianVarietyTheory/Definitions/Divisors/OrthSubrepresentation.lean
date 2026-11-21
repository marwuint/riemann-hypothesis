import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

noncomputable section

namespace GlobalTheory.Shin

open Polynomial GlobalTheory.CuspGL
open scoped Classical

def nrmG {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ) (l : ℕ) (δ : G) : G :=
  ((List.range l).map fun i => φ (s ^ i) δ).prod

def Kills {G : Type} [Group G] (φ Y : G → ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
    ∑ᶠ g, star (Y g) * LinearMap.trace ℂ V (ρ g) = 0 → ∑ᶠ g, star (φ g) • ρ g = 0

namespace IsoPart

end IsoPart

def IsCl {G : Type} [Group G] (f : G → ℂ) : Prop := ∀ x y : G, f (y⁻¹ * x * y) = f x

def Reg (q m k : ℕ) : Prop := ∀ i : ℕ, 0 < i → i < m → ¬ k * q ^ i ≡ k [MOD q ^ m - 1]

section OneField

variable {F : Type} [Field F]

def ent {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) : F :=
  if h : i < n ∧ j < n then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def tl (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin a) (Fin a) F := fun i j => ent M i j

def br (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin b) (Fin b) F :=
  fun i j => ent M (a + i) (a + j)

def InPar (a : ℕ) {n : ℕ} (x : GL (Fin n) F) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (x : Matrix (Fin n) (Fin n) F) i j = 0

def toG {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : GL (Fin n) F := if h : IsUnit M then h.unit else 1

def tlG (a : ℕ) {n : ℕ} (x : GL (Fin n) F) : GL (Fin a) F := toG (tl a (x : Matrix (Fin n) (Fin n) F))

def brG (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) : GL (Fin b) F := toG (br a b (x : Matrix (Fin n) (Fin n) F))

def gal {F' : Type} [Field F'] (t : F →+* F') (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  Matrix.GeneralLinearGroup.map t

def hcTw (t : F →+* F) (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  fun x => (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
    ∑ᶠ y : GL (Fin n) F, if InPar a (y⁻¹ * x * gal t n y) then
      α (tlG a (y⁻¹ * x * gal t n y)) * β (brG a b (y⁻¹ * x * gal t n y)) else 0

def hc (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  hcTw (RingHom.id F) a b α β n

def psiG (S : F[X] → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  fun x => psi S (Fin n → F) (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F))

def chG (S : F[X] → ℂ) (n : ℕ) : GL (Fin n) F → ℂ := fun x => S (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))

def cusp (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) : GL (Fin m) F → ℂ :=
  fun x => (-1) ^ (m - 1) * psiG (rootSum θ k) m x

def deg (L : List (ℕ × ℕ)) : ℕ := (L.map Prod.fst).sum

def J (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) : (n : ℕ) → GL (Fin n) F → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → GL (Fin n) F → ℂ) (fun _ _ => 1)
    (fun p L ih n => hc p.1 (deg L) (cusp θ p.1 p.2) (ih (deg L)) n) L

theorem J_nil (θ : AlgebraicClosure F →* ℂ) (n : ℕ) : J θ [] n = fun _ => 1 := rfl

theorem J_cons (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) (n : ℕ) :
    J θ (p :: L) n = hc p.1 (deg L) (cusp θ p.1 p.2) (J θ L (deg L)) n := rfl

def HFree {n : ℕ} (Y : GL (Fin n) F → ℂ) : Prop :=
  0 < n → ∑ᶠ x ∈ {x : GL (Fin n) F | ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j}, Y x = 0

end OneField

section TwoFields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

def galAct (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) :
    (F' ≃ₐ[F] F') →* MulAut (GL (Fin n) F') where
  toFun t :=
    { toFun := gal (t : F' →+* F') n
      invFun := gal (t.symm : F' →+* F') n
      left_inv := fun x => by ext i j; simp [gal]
      right_inv := fun x => by ext i j; simp [gal]
      map_mul' := fun x y => map_mul _ x y }
  map_one' := by ext x i j; simp [gal]
  map_mul' s t := by ext x i j; simp [gal]

theorem galAct_apply (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    galAct F F' n t x = gal (t : F' →+* F') n x := rfl

def incl (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  gal (algebraMap F F') n

def nrm (s : F' ≃ₐ[F] F') {n : ℕ} (δ : GL (Fin n) F') : GL (Fin n) F' :=
  nrmG (galAct F F' n) s (Module.finrank F F') δ

def IsNorm (s : F' ≃ₐ[F] F') {n : ℕ} (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (incl F F' n γ) (nrm s δ)

def shLift (s : F' ≃ₐ[F] F') {n : ℕ} (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsNorm s δ γ then f h.choose else 0

abbrev GHat (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) : Type :=
  GL (Fin n) F' ⋊[galAct F F' n] (F' ≃ₐ[F] F')

def pullθ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) :
    AlgebraicClosure F →* ℂ := θ.comp (ι : AlgebraicClosure F →* AlgebraicClosure F')

end TwoFields

def liftL (q l : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.flatMap fun p => (List.range l).map fun i => (p.1 / l, p.2 * q ^ i)

def liftAll (q l : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.flatMap fun p => if l ∣ p.1 then liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]

theorem isNorm_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (n : ℕ) :
    IsNorm s (1 : GL (Fin n) F') (1 : GL (Fin n) F) := by
  have : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact map_one _
  unfold IsNorm
  rw [this, map_one]

end GlobalTheory.Shin

end
