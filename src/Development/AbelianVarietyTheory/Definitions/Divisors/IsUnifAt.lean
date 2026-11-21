import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def toSub {G : Type} [Group G] (H : Subgroup G) (g : G) : H := if h : g ∈ H then ⟨g, h⟩ else 1

def trOn {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ M, L v ∈ M then LinearMap.trace ℂ M (L.restrict h) else 0

def hint {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) : ℂ :=
  (((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out

def IsMu (μ : HChar E) (e : InfinitePlace E → ℤ) : Prop :=
  μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
    (∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1)) ∧ (∀ v, Odd (e v)) ∧
    ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v

def blk {a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw n w :=
  let M := Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
    (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)
  if hM : IsUnit M then hM.unit else 1

def intMat (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
  Subgroup.closure {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}

def ct {a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => avg fun k : GlobalTheory.LFun.KGL w n => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)

def ctMu {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    ct h w (fun y => f (toSub _ y)) m

def iwGL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

def tdiag {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) : GLw n w :=
  GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) fun i => ϖ ^ a i

def dcos (n : ℕ) (w : Pl E) (t : GLw n w) : GLw n w → ℂ :=
  fun y => if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

def IsUnifAt {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) : Prop := ordL (ϖ : w.adicCompletion E) = 1 ∧ cj w ϖ = ϖ

def IsWitt (n : ℕ) (w : Pl E) (b : GLw n w) : Prop :=
  b ∈ GlobalTheory.LFun.KGL w n ∧ (b.val.map (cj w))ᵀ * b.val = antiJ (w.adicCompletion E) n

def iwU (n : ℕ) (w : Pl E) (b : GLw n w) : Subgroup (UL n w) :=
  ((iwGL n w).map (MulAut.conj b).toMonoidHom).subgroupOf (UL n w)

def wexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ else if h' : n - 1 - i.val < n / 2 then -l ⟨_, h'⟩ else 0

def Cone {m : ℕ} (l : Fin m → ℤ) : Prop := (∀ i j : Fin m, (j : ℕ) = i + 1 → 2 ≤ l i - l j) ∧ ∀ i, 2 ≤ l i

def fU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) : UL n w → ℂ :=
  fun γ => if ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 then 1 else 0

def qh (w : Pl E) : ℂ := (Real.sqrt (qV E w : ℝ) : ℝ)

def dlt (n : ℕ) (w : Pl E) (l : Fin (n / 2) → ℤ) : ℂ := qh w ^ (∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)

def vRes (n a : ℕ) (l : Fin (n / 2) → ℤ) (s : Finset (Fin (n / 2))) : ℤ :=
  -2 * (∑ i ∈ s, ∑ j ∈ sᶜ, max (l i) (l j)) -
    (if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, l j else ∑ j ∈ s, l j) else 0)

def HasVals {w : Pl E} (Q : (w.adicCompletion E)[X]) (a : Fin n → ℤ) : Prop :=
  ∃ u : Fin n → w.adicCompletion E, Q = ∏ i, (X - C (u i)) ∧ ∀ i, u i ≠ 0 ∧ ordL (u i) = a i

def pw {m : ℕ} (y : Fin m → ℂˣ) (l : Fin m → ℤ) : ℂ := ∏ i, ((y i ^ l i : ℂˣ) : ℂ)

def SatUL {w : Pl E} (b : GLw n w) (ϖ : w.adicCompletion E) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (p : UL n w ≃* GU (cj w) n) (σ' : SmIrr (GU (cj w) n)), (∀ x, (p x).1 = b⁻¹ * x.1 * b) ∧
    GlobalTheory.LFun.HasSatU ϖ q σ'.ρ α ∧ Nonempty (σ.ρ.Equiv (σ'.ρ.comp p.toMonoidHom))

def UE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (GL (Fin n) E) :=
  UJ (IsCMField.complexConj E).toRingEquiv.toRingHom 1

def finPt (γ : UE E n) : finU E n := toSub _ (toSub _ (finGL E n (ratF E n γ.1)))

def ratFinU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (finU E n) :=
  (((UE E n).map ((finGL E n).comp (ratF E n))).comap (UA E n).subtype).comap (finU E n).subtype

def locPt (w : Pl E) (γ : UE E n) : UL n w := toSub _ (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)

def globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Subgroup (finU E n) :=
  ⨅ w ∈ S, ((K' w).map (UL n w).subtype).comap ((cLoc w).comp (finU E n).subtype)

def globFn (S : Set (Pl E)) (f : ∀ w : Pl E, UL n w → ℂ) (x : finU E n) : ℂ := ∏ᶠ w ∈ S, f w (toSub _ (cLoc w x.1))

def RF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Representation ℂ (finU E n) (UA E n → ℂ) :=
  (RU E n).comp (finU E n).subtype

def forms (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (UA E n → ℂ) :=
  ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)),
    π ⊓ fixed (RF E n) (globLev S K')

def hop (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) :
    (UA E n → ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
  levOp (RF E n) (globLev S (KL n)) (globLev S K') (globFn S f) LinearMap.id

def dimW (lam : InfinitePlace E → DomWeight n) : ℂ :=
  ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (lam v) 1)

def geomURat (lam : InfinitePlace E → DomWeight n) (orb : UE E n → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then
    mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0

def nfac {k : Type} [Field k] (P : k[X]) : ℕ := Multiset.card (UniqueFactorizationMonoid.normalizedFactors P)

end GlobalTheory.BCT
