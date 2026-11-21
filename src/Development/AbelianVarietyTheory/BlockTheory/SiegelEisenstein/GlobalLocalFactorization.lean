import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n I I' : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {c : ℕ}

def stdL (k : Type) [Field k] [ValuativeRel k] (I : Type) : Set (I → k) := {y | ∀ i, y i ∈ 𝒪[k]}

def mono (c : ℕ) (L : Set (n → k)) (b : ℕ → kˣ) : Set (n ⊕ Fin c → k) :=
  {y | (fun l => y (Sum.inl l)) ∈ L ∧ ∀ i : Fin c, (((b (i.val + 1))⁻¹ : kˣ) : k) * y (Sum.inr i) ∈ 𝒪[k]}

def Carries (g : GL I k) (S Λ : Set (I → k)) : Prop := ∀ y, y ∈ S ↔ g.val *ᵥ y ∈ Λ

def stab (Λ : Set (I → k)) : Set (GL I k) := {g | Carries g Λ Λ}

def InCoset {G : Type} [Group G] (R : Subgroup G) (t : G) (J : Set G) (h : G) : Prop := ∃ r ∈ R, ∃ κ ∈ J, h = r * t * κ

def prC (J : Set (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) : Set (GL n k) :=
  {g | ∃ u ∈ N k n c 1, h⁻¹ * (u * embX c g) * h ∈ J}

variable [MeasurableSpace k] [BorelSpace k]

def lower (ν : Measure k) (p : ℕ) (l : GL (n ⊕ Fin c) k → ℂ) (i : ℕ) : GL (n ⊕ Fin c) k → ℂ :=
  Nat.rec (motive := fun _ => GL (n ⊕ Fin c) k → ℂ) l
    (fun i l' h => ∫ β : n → k, l' (colE c (p - i) β * h) ∂(Measure.pi fun _ => ν)) i

def entry (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (K J : Set (GL (n ⊕ Fin c) k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    Matrix n n' k → ℂ :=
  ((((volN ν n c 1).real {u | h⁻¹ * u.1 * h ∈ J} / (volN ν n c 1).real {u | u.1 ∈ K})⁻¹ : ℝ) : ℂ) • opE ψ ν 1 (om μ h' h Φ)

def IsIdx (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (J : Set (GL (n ⊕ Fin c) k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (A' : Finset (GL (n' ⊕ Fin (c + 1)) k)) (A : Finset (GL (n ⊕ Fin c) k)) :
    Prop :=
  (∀ h ∈ A, ∀ h₀ ∈ A, InCoset (R k n c 1) h₀ J h → h = h₀) ∧ (∀ h ∈ A, ∃ h' ∈ A', opE ψ ν 1 (om μ h' h Φ) ≠ 0) ∧
    ∀ h' ∈ A', ∀ h, opE ψ ν 1 (om μ h' h Φ) ≠ 0 → ∃ h₀ ∈ A, InCoset (R k n c 1) h₀ J h

end Local

abbrev XI (κ t j : ℕ) : Type := Fin κ ⊕ Fin j ⊕ Fin j × Fin t

def lab {κ t j c : ℕ} : XI κ t j ⊕ Fin c → Fin κ ⊕ ℕ ⊕ ℕ × Fin t
  | .inl (.inl l) => .inl l
  | .inl (.inr (.inl s)) => .inr (.inl (c + j - s.val))
  | .inl (.inr (.inr d)) => .inr (.inr (d.1.val, d.2))
  | .inr i => .inr (.inl (i.val + 1))

def FreeG {κ t : ℕ} (p : ℕ) : Fin κ ⊕ ℕ ⊕ ℕ × Fin t → Fin κ ⊕ ℕ ⊕ ℕ × Fin t → Prop
  | .inl l, .inl l' => l < l'
  | .inl _, .inr (.inl i) => p < i
  | .inr (.inl i), .inl _ => i < p
  | .inr (.inl i), .inr (.inl i') => i < i'
  | .inr (.inr d), .inr (.inr d') => d.1 ≤ d'.1
  | .inr (.inr _), .inl _ => False
  | .inr (.inr _), .inr (.inl _) => False
  | .inl _, .inr (.inr _) => True
  | .inr (.inl _), .inr (.inr _) => True

def Simple {κ t : ℕ} : Fin κ ⊕ ℕ ⊕ ℕ × Fin t → Fin κ ⊕ ℕ ⊕ ℕ × Fin t → Prop
  | .inl l, .inl l' => l'.val = l.val + 1
  | .inr (.inl i), .inr (.inl i') => i' = i + 1
  | _, _ => False

def inc {κ t j c : ℕ} : XI κ t j ⊕ Fin (c + 1) → XI κ t (j + 1) ⊕ Fin c
  | .inl (.inl l) => .inl (.inl l)
  | .inl (.inr (.inl s)) => .inl (.inr (.inl s.castSucc))
  | .inl (.inr (.inr d)) => .inl (.inr (.inr (d.1.castSucc, d.2)))
  | .inr i => if h : i.val < c then .inr ⟨i.val, h⟩ else .inl (.inr (.inl (Fin.last j)))

def aEmb {κ t j c : ℕ} : Fin κ ⊕ Fin j ⊕ Fin c → XI κ t j ⊕ Fin c
  | .inl l => .inl (.inl l)
  | .inr (.inl s) => .inl (.inr (.inl s))
  | .inr (.inr i) => .inr i

def dEmb {κ t j : ℕ} (c : ℕ) (d : Fin j × Fin t) : XI κ t j ⊕ Fin c := .inl (.inr (.inr d))

section Data

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ t j c : ℕ}

def rebase₂ {n n' : Type} {c c' : ℕ} (b' b : ℕ → kˣ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k :=
  fun r s => x r s * ((Sum.elim (fun _ => 1) (fun i => b' (i.val + 1)) s * (Sum.elim (fun _ => 1) (fun i => b (i.val + 1)) r)⁻¹ : kˣ) : k)

open Classical in

def chr (μ : kˣ →* ℂˣ) (x : k) : ℂ := if h : x = 0 then 0 else μ (Units.mk0 x h)

def pw (q : Unif k) (i : ℕ) : kˣ := q.unit ^ i

def InPat (p : ℕ) (M : Matrix (XI κ t j ⊕ Fin c) (XI κ t j ⊕ Fin c) k) : Prop :=
  (∀ r s, M r s ∈ 𝒪[k]) ∧ valuation k M.det = 1 ∧
    ∀ r s, ¬ FreeG p (lab r) (lab s) → valuation k (M r s - (1 : Matrix _ _ k) r s) < 1

open Classical in

def lamM (ψ : AddChar k Circle) (q : Unif k) (μ : ℕ → kˣ →* ℂˣ) (M : Matrix (XI κ t j ⊕ Fin c) (XI κ t j ⊕ Fin c) k) : ℂ :=
  (ψ (q.inv * ∑ r, ∑ s, if Simple (lab r) (lab s) then M r s else 0) : ℂ) *
    ∏ i : Fin j, chr (μ (i.val + 1)) (M.submatrix (fun s => dEmb c (i, s)) fun s => dEmb c (i, s)).det

def latG (q : Unif k) (κ t j c : ℕ) : Set (XI κ t j ⊕ Fin c → k) := mono c (stdL k _) (pw q)

def JG (q : Unif k) (p κ t j c : ℕ) : Set (GL (XI κ t j ⊕ Fin c) k) := {g | InPat p (rebase₂ (pw q) (pw q) g.val)}

def lamG (ψ : AddChar k Circle) (q : Unif k) (μ : ℕ → kˣ →* ℂˣ) (g : GL (XI κ t j ⊕ Fin c) k) : ℂ :=
  lamM ψ q μ (rebase₂ (pw q) (pw q) g.val)

open Classical in

def phiG (ψ : AddChar k Circle) (q : Unif k) (μ : ℕ → kˣ →* ℂˣ) (p κ t j c : ℕ)
    (x : Matrix (XI κ t (j + 1) ⊕ Fin c) (XI κ t j ⊕ Fin (c + 1)) k) : ℂ :=
  if InPat p ((rebase₂ (pw q) (pw q) x).submatrix inc id) ∧
      ∀ s r, valuation k (rebase₂ (pw q) (pw q) x (dEmb c (Fin.last j, s)) r) < 1 then
    lamM ψ q μ ((rebase₂ (pw q) (pw q) x).submatrix inc id) * (chr (μ (j + 1)) ((rebase₂ (pw q) (pw q) x).submatrix inc id).det)⁻¹
  else 0

def JQ (k : Type) [Field k] [ValuativeRel k] (κ t j c : ℕ) : Set (GL (XI κ t j ⊕ Fin c) k) :=
  {g | (∀ r s, g.val r s ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 ∧ ∀ d a, valuation k (g.val (dEmb c d) (aEmb a)) < 1}

def lamQ (δ : kˣ →* ℂˣ) (g : GL (XI κ t j ⊕ Fin c) k) : ℂ := chr δ (g.val.submatrix (dEmb c) (dEmb c)).det

open Classical in

def phiQ (δ : kˣ →* ℂˣ) (b' b : ℕ → kˣ) (κ t j c : ℕ) (x : Matrix (XI κ t (j + 1) ⊕ Fin c) (XI κ t j ⊕ Fin (c + 1)) k) : ℂ :=
  if (∀ r s, rebase₂ b' b x r s ∈ 𝒪[k]) ∧ valuation k ((rebase₂ b' b x).submatrix (fun a => inc (aEmb a)) aEmb).det = 1 ∧
      ∀ d a, valuation k (rebase₂ b' b x (dEmb c d) (aEmb a)) < 1 then
    (chr δ ((rebase₂ b' b x).submatrix (fun a => inc (aEmb a)) aEmb).det)⁻¹
  else 0

def IsNF {n : Type} [Fintype n] [DecidableEq n] (q : Unif k) (j : ℕ) (h : GL (n ⊕ Fin (c + 1)) k) : Prop :=
  ∃ (e : ℕ → ℤ) (z : n → k), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ z ∈ stdL k n ∧ Carries h (stdL k _)
    {y | (fun l => y (Sum.inl l) - y (Sum.inr 0) * z l) ∈ stdL k n ∧
      ∀ i : Fin (c + 1), ((q.unit ^ (-e (i.val + 1)) : kˣ) : k) * y (Sum.inr i) ∈ 𝒪[k]}

end Data

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Pt (D : D7) where
  k : Type
  [fld : Field k]
  [vr : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [ms : MeasurableSpace k]
  [bs : BorelSpace k]
  p : SplitPt D k
  q : Unif k
  χ : AddChar k Circle
  ν : Measure k

attribute [instance] Pt.fld Pt.vr Pt.top Pt.loc Pt.ms Pt.bs

def Pt.Is (x : Pt D) (ψ : AddChar (AF D.host.F) ℂ) : Prop := HasConductor x.χ 1 ∧ IsUnitVol x.ν ∧ x.p.IsChar ψ x.χ ∧ x.p.UnitAA

def Pt.letter (x : Pt D) (μ : (AE D)ˣ →* Circle) : x.kˣ →* ℂˣ := (Circle.toUnits.comp (μ.comp x.p.idele))⁻¹

variable {ι : Type} {x : ι → Pt D}

structure Vert (x : ι → Pt D) (V A : HSp D) (κ t j c : ℕ) where
  α : ∀ i, Frame (x i).p A (XI κ t j)
  β : ∀ i, Frame (x i).p V (XI κ t j ⊕ Fin c)
  τ : ∀ i, ℕ → (x i).kˣ

variable {V V₀ A V' A' : HSp D} {κ t j c ρ : ℕ}

def Vert.Cols (v : Vert x V A κ t j c) (d : HypDec V V₀ ρ) (ι₀ : Matrix (Fin V.rank) (Fin A.rank) D.host.E)
    (z : Fin V.rank → D.host.E) (i : ι) : Prop :=
  (∀ l, valuation (x i).k (v.τ i l : (x i).k) = 1) ∧
  (v.β i).b.submatrix id Sum.inl = ι₀.map (fun a => (x i).p.pr (incA D a)) * (v.α i).b ∧
  ∀ (s : Fin c) r, (∀ l : Fin ρ, s.val = l.val → (v.β i).b r (Sum.inr s) = v.τ i (s.val + 1) * (x i).p.pr (incA D (d.e r l))) ∧
    (∀ l : Fin ρ, s.val + l.val + 1 = c → (v.β i).b r (Sum.inr s) = v.τ i (s.val + 1) * (x i).p.pr (incA D (d.e' r l))) ∧
    (c = 2 * ρ + 1 → s.val = ρ → (v.β i).b r (Sum.inr s) = v.τ i (s.val + 1) * (x i).p.pr (incA D (z r)))

def Vert.IsBes (v : Vert x V A κ t j c) (ψ : AddChar (AF D.host.F) ℂ) (b : BesAt V A ρ) (i : ι) : Prop :=
  v.Cols b.d (b.d.i₀ * b.o.iA) (b.d.i₀ *ᵥ vecB b.o b.ζ) i ∧
    ∀ u ∈ N (x i).k _ c (ρ + 1), psiBes ψ b.d 1 (vecB b.o b.ζ) ((v.β i).gl u) = (x i).χ (RootEx.simpleSum u)

def Vert.IsJac (v : Vert x V A κ t j c) (ψ : AddChar (AF D.host.F) ℂ) (b : JacAt V A ρ) (L : HSp D) (ζ : Fin L.rank → D.host.E)
    (i : ι) : Prop :=
  v.Cols b.d b.d.i₀ 0 i ∧ ∀ u ∈ N (x i).k _ c ρ ⊓ N (x i).k _ c (ρ + 1), ∀ Y, IsThetaFunO ψ A L Y →
    psiFlag ψ b.d ((v.β i).gl u) • jacS ψ b.d L (zEll L ρ ζ) ((v.β i).gl u) Y = ((x i).χ (RootEx.simpleSum u) : ℂ) • Y

def IsLatS {y : Pt D} {S : HSp D} {I : Type} [Fintype I] [DecidableEq I] (β : Frame y.p S I) (L : Lat S) (Λ : Set (I → y.k)) : Prop :=
  ∀ w : I → y.k, w ∈ Λ ↔ (fun r => y.p.sec ((β.b *ᵥ w) r)) ∈ latV S L (· = y.p.v)

def OverFam (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
    (α : ∀ i, Frame (x i).p S I') (β : ∀ i, Frame (x i).p T I) (LS : Lat S) (LT : Lat T) (Ψ : ∀ i, Matrix I I' (x i).k → ℂ)
    (l : List ι) (f f' : WO S T → ℂ) : Prop :=
  l.foldr (fun i (r : (WO S T → ℂ) → Prop) f₂ => ∃ g, r g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f₂) (fun f₂ => f₂ = f) f'

def Vert.HasType (v : Vert x V A κ t j c) (Ig IQ : List ι) (p : ℕ) (μ₀ : ℕ → (AE D)ˣ →* Circle) (ξ : (AE D)ˣ →* Circle)
    (L : Lat V) (b : GA D V) (l : GA D V → ℂ) : Prop :=
  (∀ i ∈ Ig, ∀ κ' ∈ JG (x i).q p κ t j c, ∀ g,
    l (g * (v.β i).gl κ') = lamG (x i).χ (x i).q (fun a => (x i).letter (μ₀ a)) κ' * l g) ∧
  (∀ i ∈ IQ, ∀ κ' ∈ JQ (x i).k κ t j c, ∀ g, l (g * (v.β i).gl κ') = lamQ ((x i).letter ξ) κ' * l g) ∧
  ∀ κ', InK V L (fun w => ∀ i, i ∈ Ig ∨ i ∈ IQ → w ≠ (x i).p.v) κ' → ∀ g, l (g * (b⁻¹ * κ' * b)) = l g

def idxC (y : Pt D) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (J : Set (GL (n ⊕ Fin c) y.k)) (h : GL (n ⊕ Fin c) y.k) : ℂ :=
  (((volGL y.ν n).real (KO y.k n) / (volGL y.ν n).real (prC J h) : ℝ) : ℂ)

def Vert.Lowers (v : Vert x V A κ t j c) (ψ : AddChar (AF D.host.F) ℂ) (B : BesAt V A ρ) (Ig IQ : List ι) (p : ℕ)
    (μ₀ : ℕ → (AE D)ˣ →* Circle) (ξ : (AE D)ˣ →* Circle) (L : Lat V) (b : GA D V) (h : ∀ i, GL (XI κ t j ⊕ Fin c) (x i).k)
    (e : GA D V →₀ ℂ) : Prop :=
  ∀ l : GA D V → ℂ, (∀ u ∈ flagN B.d, u ∈ GfC V → ∀ g, l (u * g) = psiBes ψ B.d 1 (vecB B.o B.ζ) u * l g) →
    v.HasType Ig IQ p μ₀ ξ L b l →
    ∑ g ∈ e.support, e g * l g = IQ.foldr (fun i l' g => idxC (x i) (JQ _ κ t j c) (h i) *
      lower (x i).ν (ρ + 1) (fun y => l' ((v.β i).gl y * g)) ρ (h i)) l b

def IsChart {Ch : Type} {G : ι → Type} (IQ : List ι) (A : ∀ i, Finset (G i)) (h : Ch → ∀ i, G i) : Prop :=
  (∀ a, ∀ i ∈ IQ, h a i ∈ A i) ∧ (∀ a a', (∀ i ∈ IQ, h a i = h a' i) → a = a') ∧
    ∀ f : ∀ i, G i, (∀ i ∈ IQ, f i ∈ A i) → ∃ a, ∀ i ∈ IQ, h a i = f i

def datG (y : Pt D) (μ₀ : ℕ → (AE D)ˣ →* Circle) (p κ t j c : ℕ) :
    Matrix (XI κ t (j + 1) ⊕ Fin c) (XI κ t j ⊕ Fin (c + 1)) y.k → ℂ :=
  phiG y.χ y.q (fun a => y.letter (μ₀ a)) p κ t j c

def datQ (v : Vert x V A κ t j (c + 1)) (v' : Vert x V' A' κ t (j + 1) c) (ξ : (AE D)ˣ →* Circle) (i : ι) :
    Matrix (XI κ t (j + 1) ⊕ Fin c) (XI κ t j ⊕ Fin (c + 1)) (x i).k → ℂ :=
  phiQ ((x i).letter ξ) (fun l => (v.τ i l)⁻¹) (fun l => (v'.τ i l)⁻¹) κ t j c

def ProdData {𝒯 Pol : Type} (ψ : AddChar (AF D.host.F) ℂ) (v : Vert x V A κ t j (c + 1)) (v' : Vert x V' A' κ t (j + 1) c)
    (Ig : List ι) (IQ : 𝒯 → List ι) (p : ℕ) (μ₀ : ℕ → (AE D)ˣ →* Circle) (ξ : 𝒯 → (AE D)ˣ →* Circle) (L : Lat V) (L' : Lat V')
    (b : GA D V) (b' : GA D V') (atT : Pl D → Prop) (om : 𝒯 → Om V V') (Φ : 𝒯 → Pol → WO V V' → ℂ) : Prop :=
  ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∃ a : (AE D)ˣ, (a : AE D) - 1 ∈ idAt D atT ∧ ∀ P, ∃ f₀ f₁, Vac ψ V V' L L' (fun _ => True) f₀ ∧
    OverFam ψ v.β v'.β L L' (fun i => datG (x i) μ₀ p κ t j c) Ig f₀ f₁ ∧
    ∀ s, OverFam ψ v.β v'.β L L' (datQ v v' (ξ s)) (IQ s) f₁ ((κ₀ * (ξ s a : ℂ)) • om s (b, b') (Φ s P))

def KerData (ψ : AddChar (AF D.host.F) ℂ) (v : Vert x V A κ t j (c + 1)) (v' : Vert x V' A' κ t (j + 1) c) (Ig IQ : List ι)
    (p : ℕ) (μ₀ : ℕ → (AE D)ˣ →* Circle) (ξ : (AE D)ˣ →* Circle) (LA : Lat A) (LA' : Lat A')
    (atT : (WO A A' → ℂ) → (WO A A' → ℂ) → Prop) (h' : ∀ i, GL (XI κ t j ⊕ Fin (c + 1)) (x i).k)
    (h : ∀ i, GL (XI κ t (j + 1) ⊕ Fin c) (x i).k) (dd : WO A A' →₀ ℂ) : Prop :=
  ∀ f, Vac ψ A A' LA LA' (fun _ => True) f → ∃ f₁ f₂, atT f f₁ ∧
    OverFam ψ v.α v'.α LA LA' (fun i => entry (x i).χ (x i).ν ((x i).letter (μ₀ (j + 1))) (stab (latG (x i).q _ _ _ _))
      (JG (x i).q p κ t (j + 1) c) (datG (x i) μ₀ p κ t j c) 1 1) Ig f₁ f₂ ∧
    OverFam ψ v.α v'.α LA LA' (fun i => idxC (x i) (JQ _ κ t j (c + 1)) (h' i) •
      entry (x i).χ (x i).ν ((x i).letter (μ₀ (j + 1) * ξ)) (stab (stdL _ _)) (JQ _ κ t (j + 1) c) (datQ v v' ξ i) (h' i) (h i))
      IQ f₂ (comb ψ A A' dd f)

set_option maxHeartbeats 2000000 in

structure Site (c : Comm D) {𝒯 : Type} (T : 𝒯 → Tup c) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ιT ι : Type) (x : ι → Pt D)
    (κ t : ℕ) where
  μ₀ : ℕ → (AE D)ˣ →* Circle
  ξ : 𝒯 → (AE D)ˣ →* Circle
  χz : (AE D)ˣ →* Circle

  p : ιT → SplitPt D k
  IT : List ιT
  q : Unif k
  χ : ιT → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1
  a : PairDat p (c.X j) (c.bes j (σ + 1) h).V₀ (Fin (c.X j).rank)
  b : MidDat p (c.X (j + 1)) (Fin (c.X (j + 1)).rank)
  a' : PairDat p (c.X (j + 1 + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).V₀ (Fin (c.X (j + 1 + 1)).rank)

  Ig : List ι
  IQ : 𝒯 → List ι
  v₀ : Vert x (c.V j) (c.X j) κ t j (2 * σ + 1 + 1 + 1)
  v₁ : Vert x (c.V (j + 1)) (c.X (j + 1)) κ t (j + 1) (2 * σ + 1 + 1)
  v₂ : Vert x (c.V (j + 1 + 1)) (c.X (j + 1 + 1)) κ t (j + 1 + 1) (2 * σ + 1)

  b₀ : GA D (c.V j)
  b₁ : GA D (c.V (j + 1))
  b₂ : GA D (c.V (j + 1 + 1))
  Λ : DblLat (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))

  A₀ : 𝒯 → ∀ i, Finset (GL (XI κ t j ⊕ Fin (2 * σ + 1 + 1 + 1)) (x i).k)
  A₁ : 𝒯 → ∀ i, Finset (GL (XI κ t (j + 1) ⊕ Fin (2 * σ + 1 + 1)) (x i).k)
  A₂ : 𝒯 → ∀ i, Finset (GL (XI κ t (j + 1 + 1) ⊕ Fin (2 * σ + 1)) (x i).k)
  h₀ : ∀ s, (T s).Ch j → ∀ i, GL (XI κ t j ⊕ Fin (2 * σ + 1 + 1 + 1)) (x i).k
  h₁ : ∀ s, (T s).Ch (j + 1) → ∀ i, GL (XI κ t (j + 1) ⊕ Fin (2 * σ + 1 + 1)) (x i).k
  h₂ : ∀ s, (T s).Ch (j + 1 + 1) → ∀ i, GL (XI κ t (j + 1 + 1) ⊕ Fin (2 * σ + 1)) (x i).k

section Pins

variable {c : Comm D} {𝒯 : Type} {T : 𝒯 → Tup c} {j σ : ℕ} {h : j + 2 * (σ + 1) + 2 = D.R.m}
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ιT : Type}
  (o : Site c T j σ h k ιT ι x κ t)

def Site.atT (v : Pl D) : Prop := ∃ i, v = (o.p i).v

set_option maxHeartbeats 2000000 in

structure Site.Pins (ε : ℤˣ) : Prop where
  even : Even j

  pt : ∀ i, (x i).Is c.ψ
  inj : Function.Injective fun i => (x i).p.v
  offT : ∀ i, ¬ o.atT (x i).p.v
  listT : o.IT.Nodup ∧ (∀ i, i ∈ o.IT) ∧ ∀ i, (o.p i).IsChar c.ψ (o.χ i)
  lists : o.Ig.Nodup ∧ ∀ s, (o.IQ s).Nodup ∧ ∀ i ∈ o.IQ s, i ∉ o.Ig

  xi : ∀ s, IsOfFinOrder (o.ξ s) ∧ (∀ a : (AF D.host.F)ˣ, o.ξ s (Units.map (algebraMap (AF D.host.F) (AE D)).toMonoidHom a) = 1) ∧
    (∀ i, IsTame ((x i).letter (o.ξ s))) ∧ ∀ v, CharUnramAt D (o.ξ s) v ↔ ∀ i ∈ o.IQ s, v ≠ (x i).p.v
  mu : ∀ a i, IsTame ((x i).letter (o.μ₀ a)) ∧ (i ∉ o.Ig → CharUnramAt D (o.μ₀ a) (x i).p.v) ∧ CharUnramAt D o.χz (x i).p.v
  weil : ∀ s, ((T s).sBF j (σ + 1) h).χV = o.μ₀ (j + 1) * o.ξ s * o.χz ∧ ((T s).sBF j (σ + 1) h).χW = o.μ₀ (j + 1) * o.ξ s ∧
    ((T s).sFB j σ h).χV = o.μ₀ (j + 1 + 1) * o.ξ s ∧ ((T s).sFB j σ h).χW = o.μ₀ (j + 1 + 1) * o.ξ s * o.χz ∧
    IsWeilDatumO c.ψ _ _ (o.μ₀ (j + 1) * o.ξ s) (o.μ₀ (j + 1) * o.ξ s) ((T s).kom j) ∧
    IsWeilDatumO c.ψ _ _ (o.μ₀ (j + 1 + 1) * o.ξ s) (o.μ₀ (j + 1 + 1) * o.ξ s) ((T s).kom (j + 1))
  line : ∀ s, ∃ (ω : Om (c.bes j (σ + 1) h).L (c.X (j + 1))) (ω' : Om (c.X (j + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).L),
    IsWeilDatumO c.ψ _ _ o.χz (o.μ₀ (j + 1) * o.ξ s) ω ∧ IsWeilDatumO c.ψ _ _ (o.μ₀ (j + 1 + 1) * o.ξ s) o.χz ω'

  frames : ∀ i, o.v₀.IsBes c.ψ (c.bes j (σ + 1) h) i ∧
    o.v₁.IsJac c.ψ (c.jac j (σ + 1) h) (c.bes (j + 1 + 1) σ (idx_step h)).L (c.bes (j + 1 + 1) σ (idx_step h)).ζ i ∧
    o.v₂.IsBes c.ψ (c.bes (j + 1 + 1) σ (idx_step h)) i ∧ o.v₁.τ i 1 = o.v₀.τ i 1 ∧ o.v₂.τ i 1 = o.v₁.τ i 1

  sd : IsSelfDualC _ o.Λ.L₀ ∧ IsSelfDualC _ o.Λ.L₁ ∧ IsSelfDualC _ o.Λ.L₂
  latX : ∀ i, IsLatS (o.v₀.α i) (c.x j).L (stdL _ _) ∧ IsLatS (o.v₁.α i) (c.x (j + 1)).L (stdL _ _) ∧
    IsLatS (o.v₂.α i) (c.x (j + 1 + 1)).L (stdL _ _)
  latg : ∀ i ∈ o.Ig, IsLatS (o.v₀.β i) o.Λ.L₀ (latG (x i).q _ _ _ _) ∧ IsLatS (o.v₁.β i) o.Λ.L₁ (latG (x i).q _ _ _ _) ∧
    IsLatS (o.v₂.β i) o.Λ.L₂ (latG (x i).q _ _ _ _)
  latQ : ∀ i ∉ o.Ig, IsLatS (o.v₀.β i) o.Λ.L₀ (stdL _ _) ∧ IsLatS (o.v₁.β i) o.Λ.L₁ (stdL _ _) ∧ IsLatS (o.v₂.β i) o.Λ.L₂ (stdL _ _)
  shape : ∀ s, DblShape ((T s).sBF j (σ + 1) h) ((T s).sFB j σ h) o.Λ (fun w => ∀ i, i ∈ o.Ig ∨ i ∈ o.IQ s → w ≠ (x i).p.v)
    o.q o.a o.b o.a'
  mid : o.Λ.M₁ = (c.x (j + 1)).L
  latT : ∀ i, (o.a.α i).IsLat (c.x j).L (o.a.P i).lat ∧ (o.a'.α i).IsLat (c.x (j + 1 + 1)).L (o.a'.P i).lat
  core : ∀ v, ¬ o.atT v → (∀ i ∈ o.Ig, v ≠ (x i).p.v) →
    (∃ LL, IsSelfDualC _ LL ∧ OrthAt (c.bes j (σ + 1) h).o o.Λ.M₀ (c.x j).L LL v) ∧
    ∃ LL, IsSelfDualC _ LL ∧ OrthAt (c.bes (j + 1 + 1) σ (idx_step h)).o o.Λ.M₂ (c.x (j + 1 + 1)).L LL v
  base : o.b₀ ∈ grpAt _ o.atT ∧ o.b₁ ∈ grpAt _ o.atT ∧ o.b₂ ∈ grpAt _ o.atT

  prod₁ : ProdData c.ψ o.v₀ o.v₁ o.Ig o.IQ (σ + 2 + j / 2) o.μ₀ o.ξ o.Λ.L₀ o.Λ.L₁ o.b₀ o.b₁ o.atT (fun s => (T s).om j)
    fun s => (T s).pt j
  prod₂ : ProdData c.ψ o.v₁ o.v₂ o.Ig o.IQ (σ + 2 + j / 2) o.μ₀ o.ξ o.Λ.L₁ o.Λ.L₂ o.b₁ o.b₂ o.atT (fun s => (T s).om (j + 1))
    fun s => (T s).pt (j + 1)

  row : ∀ s (G : (T s).CC (j + 1 + 1)) w, o.v₂.HasType o.Ig (o.IQ s) (σ + 2 + j / 2) o.μ₀ (o.ξ s) o.Λ.L₂ o.b₂ (G.1 w)

  idx : ∀ s, ∀ i ∈ o.IQ s,
    IsIdx (x i).χ (x i).ν ((x i).letter (o.μ₀ (j + 1) * o.ξ s)) (JQ _ _ _ _ _) (datQ o.v₀ o.v₁ (o.ξ s) i) (o.A₀ s i) (o.A₁ s i) ∧
    IsIdx (x i).χ (x i).ν ((x i).letter (o.μ₀ (j + 1 + 1) * o.ξ s)) (JQ _ _ _ _ _) (datQ o.v₁ o.v₂ (o.ξ s) i) (o.A₁ s i)
      (o.A₂ s i) ∧
    (∀ g ∈ o.A₀ s i, IsNF (x i).q j g) ∧ (∀ g ∈ o.A₁ s i, IsNF (x i).q (j + 1) g) ∧ ∀ g ∈ o.A₂ s i, IsNF (x i).q (j + 1 + 1) g
  chart : ∀ s, IsChart (o.IQ s) (o.A₀ s) (o.h₀ s) ∧ IsChart (o.IQ s) (o.A₁ s) (o.h₁ s) ∧ IsChart (o.IQ s) (o.A₂ s) (o.h₂ s)

  e₀ : ∀ s a, o.v₀.Lowers c.ψ (c.bes j (σ + 1) h) o.Ig (o.IQ s) (σ + 2 + j / 2) o.μ₀ (o.ξ s) o.Λ.L₀ o.b₀ (o.h₀ s a) ((T s).e j a)
  e₂ : ∀ s a, o.v₂.Lowers c.ψ (c.bes (j + 1 + 1) σ (idx_step h)) o.Ig (o.IQ s) (σ + 2 + j / 2) o.μ₀ (o.ξ s) o.Λ.L₂ o.b₂
    (o.h₂ s a) ((T s).e (j + 1 + 1) a)

  dd₁ : ∀ s a b, KerData c.ψ o.v₀ o.v₁ o.Ig (o.IQ s) (σ + 2 + j / 2) o.μ₀ (o.ξ s) (c.x j).L (c.x (j + 1)).L
    (OverAll c.ψ o.a.α o.b.β (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.a.P i) (o.b.Q i)) o.IT) (o.h₀ s a) (o.h₁ s b)
    ((T s).dd j a b)
  dd₂ : ∀ s a b, KerData c.ψ o.v₁ o.v₂ o.Ig (o.IQ s) (σ + 2 + j / 2) o.μ₀ (o.ξ s) (c.x (j + 1)).L (c.x (j + 1 + 1)).L
    (OverAll c.ψ o.b.β o.a'.α (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => phiOne (o.b.Q i) (o.a'.P i)) o.IT) (o.h₁ s a)
    (o.h₂ s b) ((T s).dd (j + 1) a b)

  ram : ∀ s, ∀ ψ ∈ (T s).Ram j, ∀ a y, o.a.Ram ((T s).rd j a ψ y) ∧ (T s).rd j a ((T s).S j ψ) y =
    o.a.sAll o.q (fun i => resChar (o.χ i) (o.hχ i) o.q) (fun _ => sgnRes k ε) o.IT ((T s).rd j a ψ y)

end Pins

end Global

end GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

end
