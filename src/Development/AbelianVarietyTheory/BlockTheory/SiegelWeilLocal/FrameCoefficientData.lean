import Mathlib

open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData

section Groups
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]

def Carries (g : V ≃ₗ[E] V) (A B : Set V) : Prop := ∀ v, g v ∈ B ↔ v ∈ A

def trivOn (E : Type) [CommRing E] [Module E V] (A : Set V) (B : AddSubgroup V) :
    Subgroup (V ≃ₗ[E] V) where
  carrier := {g | (∀ v, g v ∈ B ↔ v ∈ B) ∧ ∀ v ∈ A, g v - v ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun v _ => by simp⟩
  mul_mem' := by
    rintro g g' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun v => (h1 (g' v)).trans (h3 v), fun v hv => ?_⟩
    have : (g * g') v - v = g (g' v - v) + (g v - v) := by
      simp [LinearEquiv.mul_apply]
    rw [this]
    exact B.add_mem ((h1 _).2 (h4 v hv)) (h2 v hv)
  inv_mem' := by
    rintro g ⟨h1, h2⟩
    have k : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
    refine ⟨fun v => by rw [← h1 (g⁻¹ v), k], fun v hv => ?_⟩
    rw [← h1, map_sub, k, ← neg_sub]
    exact B.neg_mem (h2 v hv)

def stab (E : Type) [CommRing E] [Module E V] (B : AddSubgroup V) : Subgroup (V ≃ₗ[E] V) :=
  trivOn E ∅ B

def isom [StarRing E] (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ v w, h (g v) (g w) = h v w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g g'} h1 h2 v w => (h1 (g' v) (g' w)).trans (h2 v w)
  inv_mem' := by
    intro g h1 v w
    have k : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
    rw [← h1 (g⁻¹ v), k, k]

end Groups

def invVol {G : Type} [Group G] (K₀ K : Subgroup G) : ℝ≥0∞ :=
  (K.relIndex K₀ : ℝ≥0∞) / (K₀.relIndex K : ℝ≥0∞)

section Local
variable (o F E : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]

def ord_vw (x : F) : ℤ :=
  - WithZero.log ((IsDiscreteValuationRing.maximalIdeal o).valuation F x)

abbrev MaxOrd : Subalgebra o E := integralClosure o E

def IsUnramifiedQuadratic : Prop :=
  Module.finrank F E = 2 ∧ (∀ x : F, star (algebraMap F E x) = algebraMap F E x) ∧
    ∃ w ∈ MaxOrd o E, ∃ u ∈ MaxOrd o E, (w - star w) * u = 1

def IsStdChar (ψ : AddChar E Circle) : Prop :=
  (∀ y ∈ MaxOrd o E, ψ y = 1) ∧ (∀ y, (∀ c ∈ MaxOrd o E, ψ (c * y) = 1) → y ∈ MaxOrd o E) ∧
    ∀ y, ψ (star y) = ψ y

end Local

structure Frame (F V : Type) (r : ℕ) where
  f : Fin (r + 1) → V
  y : Fin r → V
  T : F

structure Data (o F E V : Type) [CommRing o] [Field F] [CommRing E] [StarRing E] [Algebra o E]
    [AddCommGroup V] [Module E V] (r : ℕ) where
  h : V →ₗ[E] V →ₛₗ[starRingEnd E] E
  ψ : AddChar E Circle
  θ : F
  A : Frame F V r
  B : Frame F V r
  blocks : Composition (r + 1)
  t : Fin blocks.length → Eˣ
  ref : Submodule (MaxOrd o E) V

section Main
variable {o F E V : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]
  [AddCommGroup V] [Module E V] {r : ℕ}

def perp (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (S : Set V) : Set V := {v | ∀ w ∈ S, h v w = 0}

namespace Frame
variable (E) (A : Frame F V r)

def z : V := A.f (Fin.last r)

def X (j : ℕ) : Submodule E V := Submodule.span E (A.f '' {i | (i : ℕ) < j})

variable {E}

def IsFrame (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) : Prop :=
  (∀ (i : Fin r) (b : Fin (r + 1)), h (A.f b) (A.f i.castSucc) = 0) ∧
    h A.z A.z = algebraMap F E (-A.T) ∧ A.T ≠ 0 ∧
    (∀ i j : Fin r, h (A.y j) (A.f i.castSucc) = if i = j then 1 else 0) ∧
    (∀ i j : Fin r, h (A.y i) (A.y j) = 0) ∧ ∀ j : Fin r, h (A.y j) A.z = 0

def N (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) : Subgroup (V ≃ₗ[E] V) :=
  isom h ⊓ (⨅ j : Fin r, trivOn E (A.X E (j + 1) : Set V) (A.X E j).toAddSubgroup) ⊓
    trivOn E (perp h (A.X E r)) (A.X E r).toAddSubgroup

def coeffSum (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (g : V ≃ₗ[E] V) : E :=
  ∑ j : Fin r, h (g (A.f j.succ)) (A.y j)

def IsInnerLattice (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (L : Submodule (MaxOrd o E) V) : Prop :=
  (∃ s : Finset V, L = (A.X E r).restrictScalars (MaxOrd o E) ⊔
      Submodule.span (MaxOrd o E) (s : Set V)) ∧
    (∀ v, v ∈ L ↔ v ∈ perp h (A.X E r) ∧ ∀ w ∈ L, h v w ∈ MaxOrd o E) ∧
    A.z ∈ L ∧ ∀ c : E, c • A.z ∈ L → c ∈ MaxOrd o E

def stdLattice (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (L : Submodule (MaxOrd o E) V) :
    Submodule (MaxOrd o E) V :=
  Submodule.span (MaxOrd o E) (Set.range (fun i : Fin r => A.f i.castSucc) ∪
    ((L : Set V) ∩ perp h (Set.range A.y)) ∪ Set.range A.y)

end Frame

namespace Data
variable {k : ℕ} (D : Data o F E V r)

def θinv : E := algebraMap F E D.θ⁻¹

def Zhat : Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun a b => D.h (D.A.f a) (D.B.f b)

def minor (l : ℕ) (hl : l ≤ r + 1) : E :=
  (D.Zhat.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def G : F :=
  Algebra.norm F (D.minor (r + 1) le_rfl) -
    D.A.T * D.B.T * Algebra.norm F (D.minor r (Nat.le_succ r))

def Relevant : Prop :=
  ∀ a b : Fin (r + 1), D.Zhat a b =
    if (a : ℕ) + b + 1 = D.blocks.sizeUpTo (D.blocks.index a) +
        D.blocks.sizeUpTo (D.blocks.index a + 1)
    then (D.t (D.blocks.index a) : E) * (-1) ^ (r - (b : ℕ)) else 0

def psi (g : V ≃ₗ[E] V) : Circle := D.ψ (D.θinv * D.A.coeffSum D.h g)

def psi' (g : V ≃ₗ[E] V) : Circle := D.ψ (D.θinv * D.B.coeffSum D.h g)

def St : Subgroup (V ≃ₗ[E] V) := D.A.N D.h ⊓ D.B.N D.h

def StInt : Subgroup (V ≃ₗ[E] V) :=
  D.St ⊓ stab E (Submodule.span (MaxOrd o E) (Set.range D.A.f)).toAddSubgroup ⊓
    stab E (Submodule.span (MaxOrd o E) (Set.range D.B.f)).toAddSubgroup

def Hyp (k : ℕ) : Prop :=
  IsUnramifiedQuadratic o F E ∧ IsStdChar o E D.ψ ∧
    Module.finrank E V = k + 2 * r + 1 ∧
    (∀ v w, D.h w v = star (D.h v w)) ∧ (∀ v, (∀ w, D.h v w = 0) → v = 0) ∧
    (D.θ = 1 ∨ (D.θ ≠ 0 ∧ ord_vw o F D.θ = 1 ∧ ¬ IsField E ∧
      ord_vw o F D.A.T = 0 ∧ ord_vw o F D.B.T = 0)) ∧
    D.A.IsFrame D.h ∧ D.B.IsFrame D.h ∧ D.Relevant ∧
    4 * r + 7 ≤ k ∧ D.G ≠ 0 ∧ (∀ g ∈ D.St, D.psi g = D.psi' g) ∧
    D.ref.FG ∧ Submodule.span E (D.ref : Set V) = ⊤

structure InnerDatum where
  L : Submodule (MaxOrd o E) V
  L' : Submodule (MaxOrd o E) V
  Γ : Submodule (MaxOrd o E) (V × V)
  hL : D.A.IsInnerLattice D.h L
  hL' : D.B.IsInnerLattice D.h L'
  mem : ∀ p ∈ Γ, p.1 ∈ L' ∧ p.2 ∈ L
  total : ∀ w' ∈ L', ∃ w, (w', w) ∈ Γ
  onto : ∀ w ∈ L, ∃ w', (w', w) ∈ Γ
  ker_left : ∀ w', (w', (0 : V)) ∈ Γ ↔ D.θinv • w' ∈ L'
  ker_right : ∀ w, ((0 : V), w) ∈ Γ ↔ D.θinv • w ∈ L
  base : (D.B.z, D.A.z) ∈ Γ
  isometric : ∀ p ∈ Γ, ∀ p' ∈ Γ, D.θinv * (D.h p.1 p'.1 - D.h p.2 p'.2) ∈ MaxOrd o E

variable {D}

def Serves (d : D.InnerDatum) (Λ : Submodule (MaxOrd o E) V) (n n' : V ≃ₗ[E] V) : Prop :=
  n ∈ D.A.N D.h ∧ n' ∈ D.B.N D.h ∧
    Carries n (D.A.stdLattice D.h d.L) Λ ∧ Carries n' (D.B.stdLattice D.h d.L') Λ ∧
    (∀ b, D.θinv • (n' (D.B.f b) - n (D.A.f b)) ∈ Λ) ∧
    ∀ w' w, (w', w) ∈ d.Γ ↔
      w' ∈ perp D.h (D.B.X E r) ∧ w ∈ perp D.h (D.A.X E r) ∧
        ∃ x ∈ D.A.X E r, ∃ x' ∈ D.B.X E r, w + x ∈ Λ ∧ w' + x' ∈ Λ ∧
          D.θinv • ((w' + x') - (w + x)) ∈ Λ

def Term (d : D.InnerDatum) : Type :=
  {Λ : Submodule (MaxOrd o E) V // ∃ p : (V ≃ₗ[E] V) × (V ≃ₗ[E] V), Serves d Λ p.1 p.2}

namespace Term
variable {d : D.InnerDatum} (Λ : Term d)

def pair : (V ≃ₗ[E] V) × (V ≃ₗ[E] V) := Classical.choose Λ.2

def om : Circle := D.psi Λ.pair.1 * (D.psi' Λ.pair.2)⁻¹

def mu : ℝ≥0∞ := invVol D.StInt (D.St ⊓ stab E Λ.1.toAddSubgroup)

def M : Submodule (MaxOrd o E) V :=
  Submodule.span (MaxOrd o E) (Set.range (fun b => Λ.pair.1 (D.A.f b)) ∪
    Set.range (fun b => D.θinv • (Λ.pair.2 (D.B.f b) - Λ.pair.1 (D.A.f b))))

end Term

variable (D)

end Data
end Main

end GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
