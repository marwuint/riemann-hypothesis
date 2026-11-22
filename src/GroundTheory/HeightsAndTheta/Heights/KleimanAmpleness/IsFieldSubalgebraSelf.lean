import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver secMOver GeneratesOver cechHc cechZc
  quotPart cechMap IsMGraded)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing intNum IsMultiProjPrime specialIdeal genFib IsModelOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim resDeg)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

section Coordinates

variable {K : Type} {ι : K → Type} {Ω : Type*}

def blockVec (y : (Σ k, ι k) → Ω) (k : K) : ι k → Ω := fun i => y ⟨k, i⟩

def oneBlock {κ : Type} (x : κ → Ω) : (Σ _ : Unit, κ) → Ω := fun p => x p.2

def baseDeg [DecidableEq K] (k₀ : K) : K → ℤ := Pi.single k₀ 1

variable {K₁ K₀ : Type} {ι₁ : K₁ → Type} {ι₀ : K₀ → Type}

def joinVec (y₁ : (Σ k, ι₁ k) → Ω) (y₀ : (Σ k, ι₀ k) → Ω) : (Σ k, Sum.elim ι₁ ι₀ k) → Ω
  | ⟨Sum.inl k, i⟩ => y₁ ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => y₀ ⟨k, i⟩

def joinChart (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) : ∀ k, Sum.elim ι₁ ι₀ k
  | Sum.inl k => c₁ k
  | Sum.inr k => c₀ k

def pullDeg (β : K₀ → ℤ) : K₁ ⊕ K₀ → ℤ := Sum.elim 0 β

instance joinFintype [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₀ k)] :
    ∀ k, Fintype (Sum.elim ι₁ ι₀ k)
  | Sum.inl k => (inferInstance : Fintype (ι₁ k))
  | Sum.inr k => (inferInstance : Fintype (ι₀ k))

end Coordinates

section Points

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} {ι : K → Type}

def locIn (A : Subalgebra S Ω) (p : Ideal A) : Subring Ω :=
  Subring.closure {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}

variable (S) in

def modelPts (y : (Σ k, ι k) → Ω) : Set (Subring Ω) :=
  {z | ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
    ∃ p : Ideal (chartRingOver S y c), p.IsPrime ∧ z = locIn (chartRingOver S y c) p}

variable (S) in

def SameModel {K' : Type} {ι' : K' → Type} (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) : Prop :=
  modelPts S y = modelPts S y'

variable (S) in

def IsModelWithBase (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ SameModel S y (oneBlock (blockVec y k₀))

end Points

section Bundles

variable (S : Type*) [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

def IsGenerated (y : (Σ k, ι k) → Ω) (β : K → ℤ) : Prop :=
  ∃ (n : ℕ) (s : Fin n → Ω), (∀ j, s j ∈ secOver S y β) ∧ GeneratesOver S y β s

def VeryAmple (y : (Σ k, ι k) → Ω) (β : K → ℤ) : Prop :=
  ∃ (n : ℕ) (x' : Fin n → Ω), (∀ j, x' j ∈ secOver S y β) ∧ GeneratesOver S y β x' ∧
    SameModel S y (oneBlock x')

def MultipleVeryAmple (y : (Σ k, ι k) → Ω) (μ ν : K → ℤ) (t : ℚ) : Prop :=
  ∃ (a : ℕ) (m : ℤ), 1 ≤ a ∧ (m : ℚ) = a * t ∧ VeryAmple S y (a • μ + m • ν)

end Bundles

section Residue

variable (S : Type*) [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} {ι : K → Type}

def ResField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime] :
    Type _ :=
  FractionRing (chartRingOver S y c ⧸ p)

instance resField.field (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c))
    [p.IsPrime] : Field (ResField S y c p) :=
  @FractionRing.field _ _ (Ideal.Quotient.isDomain p)

instance resField.algebraQuot (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (p : Ideal (chartRingOver S y c)) [p.IsPrime] :
    Algebra (chartRingOver S y c ⧸ p) (ResField S y c p) :=
  inferInstanceAs (Algebra _ (FractionRing (chartRingOver S y c ⧸ p)))

instance resField.algebraBase (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (p : Ideal (chartRingOver S y c)) [p.IsPrime] : Algebra S (ResField S y c p) :=
  inferInstanceAs (Algebra S (FractionRing (chartRingOver S y c ⧸ p)))

open Classical in

def residue (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (u : Ω) : ResField S y c p :=
  if h : u ∈ chartRingOver S y c then
    algebraMap (chartRingOver S y c ⧸ p) _ (Ideal.Quotient.mk p ⟨u, h⟩)
  else 0

def modVec (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime] :
    (Σ k, ι k) → ResField S y c p :=
  fun q => residue S y c p (y q / y ⟨q.1, c q.1⟩)

def resImage (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (z : Subring Ω) : Set (ResField S y c p) :=
  {v | ∃ a b : chartRingOver S y c, b ∉ p ∧ (a : Ω) / b ∈ z ∧
    v = algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p a) /
      algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p b)}

end Residue

section Numbers

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsNefIdeal (F : Type) [Field F] (P : Ideal (MRing ι F)) (β : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W → relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
    0 ≤ intNum F W ![β]

def IsNef (F : Type) [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (β : K → ℤ) : Prop :=
  IsNefIdeal F (mIdealOver F y) β

end Numbers

section StepObjects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]

def stepL (k₀ : K) (μ : K → ℤ) (a : ℕ) (m : ℤ) : K → ℤ := a • μ + m • baseDeg k₀

variable (S : Type*) [CommRing S] [Algebra S Ω] [∀ k, Fintype (ι k)]

end StepObjects

def SectionCount.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (d : ℕ) (ν : K → ℤ) (q : ℕ),
    IsModelWithBase F y k₀ → relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) →
    VeryAmple F y ν → 1 ≤ q →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
          ((d + 1 : ℕ) : ℝ) * (intNum F (mIdealOver F y)
            (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • baseDeg k₀)) : ℝ)) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank F (secOver F y (n • (ν - q • baseDeg k₀))) : ℝ)

def KAt (d : ℕ) : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsModelWithBase F y k₀ → relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∀ μ : K → ℤ, IsNef F y μ → ∀ t : ℚ, 0 < t → MultipleVeryAmple F y μ (baseDeg k₀) t

def VeryAmpleNefPlusAmple.Statement : Prop :=
  ∀ d : ℕ, KAt d

def NefProductNonneg.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    (∀ j, IsNef F y (μs j)) → 0 ≤ intNum F (mIdealOver F y) μs

section Examples

variable (F : Type) [Field F]

abbrev pnIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

abbrev pnField (N : ℕ) : Type := FractionRing (MvPolynomial (Σ k, pnIdx N k) F)

def pnPt (N : ℕ) : (Σ k, pnIdx N k) → pnField F N :=
  fun p => algebraMap (MvPolynomial (Σ k, pnIdx N k) F) (pnField F N) (X p)

theorem pnPt_ne_zero (N : ℕ) (p : Σ k, pnIdx N k) : pnPt F N p ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Σ k, pnIdx N k) F)
    (pnField F N))).mpr (MvPolynomial.X_ne_zero p)

theorem isModelWithBase_pnPt (N : ℕ) : IsModelWithBase F (pnPt F N) () :=
  ⟨fun _ => ⟨0, pnPt_ne_zero F N _⟩, rfl⟩

end Examples

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
