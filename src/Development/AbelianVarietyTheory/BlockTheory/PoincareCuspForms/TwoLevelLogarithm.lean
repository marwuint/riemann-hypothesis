import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ r) : Frame Ψ' r :=
  fun τ => x ⟨τ.1, h.symm ▸ τ.2⟩

def castWt {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) : Wt Ψ r :=
  fun τ => la ⟨τ.1, h ▸ τ.2⟩

def deMul (Ψ : Finset (E →+* ℂ)) (r p0 s : ℕ) : Wt Ψ r :=
  fun _ i => if (i : ℕ) < p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)

def GapsGe {Ψ : Finset (E →+* ℂ)} (p0 : ℕ) (la : Wt Ψ r) (a : ℤ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ p0 → a ≤ la τ i - la τ j

def PairGe {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (a : ℝ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (i : ℕ) = 0 → (j : ℕ) = r - 1 → a ≤ ((la τ j - la τ i : ℤ) : ℝ)

structure TwoLevels (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (U C : Type) [Group U] [MulAction U C] where
  Ψ : Finset (E →+* ℂ)
  Gm : Matrix (Fin r) (Fin r) E
  p0 : ℕ
  ξ0 : E
  comp : C → DataX E r
  comp_Ψ : ∀ c, (comp c).Ψ = Ψ
  comp_Gm : ∀ c, (comp c).Gm = Gm
  comp_basePoint : ∀ c, (comp c).p0 = p0
  comp_ξ0 : ∀ c, (comp c).ξ0 = ξ0

  χ_one : ∀ c la, ∀ γ ∈ (comp c).Γ, (comp c).χ la γ = 1

  Γ_L' : ∀ c, ∀ γ ∈ (comp c).Γ, ∀ v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v ∈ (comp c).L'

  tr : U → C → GL (Fin r) E
  tr_herm : ∀ u c v w, herm Gm (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v)
    (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) w) = herm Gm v w
  tr_Λ : ∀ u c v,
    v ∈ (comp c).Λ ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).Λ
  tr_L' : ∀ u c v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).L'
  tr_conj : ∀ u c γ, γ ∈ (comp c).Γ ↔ tr u c * γ * (tr u c)⁻¹ ∈ (comp (u • c)).Γ
  tr_mul : ∀ u v c, tr (u * v) c * (tr u (v • c) * tr v c)⁻¹ ∈ (comp ((u * v) • c)).Γ

  tr_faithful : ∀ u c, u • c = c → tr u c ∈ (comp c).Γ → u = 1

namespace TwoLevels

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

def dom : Set (Frame M.Ψ r) := GG M.Ψ M.Gm M.p0

def dimX : ℕ := M.Ψ.card * (M.p0 * (r - M.p0))

def dimY : ℕ := M.Ψ.card * (r * (r - 1) / 2)

def upper (c : C) : Set (GL (Fin r) E) :=
  {β | ∃ u : U, u • c = c ∧ ∃ γ ∈ (M.comp c).Γ, β = γ * M.tr u c}

def UnipotentOver (g : ℕ) : Prop :=
  ∀ c, ∀ β ∈ M.upper c, ∀ P : Ideal (𝓞 E), P.IsPrime → (g : 𝓞 E) ∈ P → ∀ v ∈ (M.comp c).L',
    Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • (M.comp c).L'

def SS (la : Wt M.Ψ r) : Set (C → Frame M.Ψ r → ℂ) :=
  {F | ∀ c, (fun x => F c (castFrame (M.comp_Ψ c) x)) ∈ (M.comp c).SS (castWt (M.comp_Ψ c) la)}

def pull (h : U) (F : C → Frame M.Ψ r → ℂ) : C → Frame M.Ψ r → ℂ :=
  fun c x => F (h • c) (lact (M.tr h c) x)

def res (F : C → Frame M.Ψ r → ℂ) : C → M.dom → ℂ := fun c x => F c x.1

def cusp (la : Wt M.Ψ r) : Submodule ℂ (C → M.dom → ℂ) := Submodule.span ℂ (M.res '' M.SS la)

def detTr [Fintype U] [DecidableEq U] (F : C → Frame M.Ψ r → ℂ) (c : C) (x : Frame M.Ψ r) : ℂ :=
  (Matrix.of fun h h' : U => M.pull (h * h') F c x).det

end TwoLevels

def SplitsCompletely (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P}.ncard = Module.finrank ℚ E

def LevelHyp {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C) : Prop :=
  ∃ g : ℕ, SplitsCompletely E g ∧ 3 * r < g ∧ M.UnipotentOver g

def IndependentTranslates (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Fintype U] [DecidableEq U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s →
      ∃ u0 ∈ M.SS (deMul M.Ψ r M.p0 s), ∀ c : C, ∃ x ∈ M.dom, M.detTr u0 c x ≠ 0

def kLog (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Wt Ψ r := fun _ a => 2 * (a : ℤ) - ((r : ℤ) - 1)

end

end GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
