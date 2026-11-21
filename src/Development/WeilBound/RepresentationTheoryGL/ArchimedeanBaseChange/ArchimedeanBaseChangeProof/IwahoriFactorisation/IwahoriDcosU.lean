import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

open MeasureTheory Polynomial
open scoped ENNReal

namespace PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.Tf.Loc

noncomputable section

section Helpers

variable {n : ℕ} {k E : Type*} [Field k] [Field E] [Algebra k E]

def starσ (σ : E ≃ₐ[k] E) (M : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  (M.map σ).transpose

variable [ValuativeRel E]

def EntriesIn (ϖ : E) (m : ℕ) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, ValuativeRel.valuation E (M i j) ≤ ValuativeRel.valuation E ϖ ^ m

def IsUnitLift (σ : E ≃ₐ[k] E) (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E) : Prop :=
  c ∈ unitGL (n := Fin n) E ∧
    (∃ p : E[X], (∀ i, ValuativeRel.valuation E (p.coeff i) ≤ 1) ∧
      (c : Matrix (Fin n) (Fin n) E) = aeval ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p) ∧
    c * theta1 σ c = (γ : GL (Fin n) E)

def congSet (ϖ : E) (m : ℕ) : Set (GL (Fin n) E) :=
  {g | g ∈ unitGL (n := Fin n) E ∧ EntriesIn ϖ m ((g : Matrix (Fin n) (Fin n) E) - 1)}

def kmFn (σ : E ≃ₐ[k] E) (ϖ : E) (m : ℕ) : unitaryGL σ (1 : GL (Fin n) E) → ℂ :=
  Set.indicator {u | (u : GL (Fin n) E) ∈ congSet ϖ m} 1

def liftSet (σ : E ≃ₐ[k] E) (ϖ : E) (m : ℕ) : Set (GL (Fin n) E) :=
  {δ | δ ∈ unitGL (n := Fin n) E ∧
    EntriesIn ϖ m ((δ : Matrix (Fin n) (Fin n) E) - starσ σ (δ : Matrix (Fin n) (Fin n) E))}

def liftFn (σ : E ≃ₐ[k] E) (ϖ : E) (m : ℕ) : GL (Fin n) E → ℂ :=
  Set.indicator (liftSet σ ϖ m) 1

end Helpers

def B1 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ (1 : GL (Fin n) E))),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E)
          (μc : Measure (twCent (theta1 σ) c))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          IsUnitLift σ γ c → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (theta1 σ) c => (x : GL (Fin n) E)) μc =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))) =>
              ((t : unitaryGL σ (1 : GL (Fin n) E)) : GL (Fin n) E)) μγ →
          twOrbIntegralC (theta1 σ) μE c μc (unitFnC E) = orbIntegralC μU γ μγ (unitFnUC σ 1)) ∧
      (∀ (δ : GL (Fin n) E) (μδ : Measure (twCent (theta1 σ) δ)),
          ((normU σ 1 δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          (¬ ∃ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E),
              IsUnitLift σ γ c ∧ TwConjugate (theta1 σ) c δ) →
          twOrbIntegralC (theta1 σ) μE δ μδ (unitFnC E) = 0) ∧
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          (∃ i, 1 < ValuativeRel.valuation E
              (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.coeff i)) →
          orbIntegralC μU γ μγ (unitFnUC σ 1) = 0)

def B2 : Prop :=
  ∀ (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E],
    Module.finrank k E = 2 → IsUnramifiedLoc k E →
    ∀ σ : E ≃ₐ[k] E, σ ≠ 1 →
    ∀ ϖ : k, IsUniformiser (algebraMap k E ϖ) →
    ∀ m : ℕ, 1 ≤ m →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      (μE : Measure (GL (Fin n) E)) (μU : Measure (unitaryGL σ (1 : GL (Fin n) E))),
      μE.IsHaarMeasure → μU.IsHaarMeasure →
      μE (unitGL (n := Fin n) E : Set (GL (Fin n) E)) = 1 →
      μU {u | (u : GL (Fin n) E) ∈ unitGL (n := Fin n) E} = 1 →
      (∀ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E)
          (μc : Measure (twCent (theta1 σ) c))
          (μγ : Measure (Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))))),
          ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          IsUnitLift σ γ c → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (theta1 σ) c => (x : GL (Fin n) E)) μc =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (unitaryGL σ (1 : GL (Fin n) E))) =>
              ((t : unitaryGL σ (1 : GL (Fin n) E)) : GL (Fin n) E)) μγ →
          twOrbIntegralC (theta1 σ) μE c μc (liftFn σ (algebraMap k E ϖ) m) =
            orbIntegralC μU γ μγ (kmFn σ (algebraMap k E ϖ) m)) ∧
      (∀ (δ : GL (Fin n) E) (μδ : Measure (twCent (theta1 σ) δ)),
          ((normU σ 1 δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable →
          (¬ ∃ (γ : unitaryGL σ (1 : GL (Fin n) E)) (c : GL (Fin n) E),
              IsUnitLift σ γ c ∧ TwConjugate (theta1 σ) c δ) →
          twOrbIntegralC (theta1 σ) μE δ μδ (liftFn σ (algebraMap k E ϖ) m) = 0) ∧
      (∀ α : E, ValuativeRel.valuation E α ≤ 1 → ValuativeRel.valuation E (α - σ α) = 1 →
        ∀ δ : GL (Fin n) E, δ ∈ liftSet σ (algebraMap k E ϖ) m ↔
          ∃ h h' : Matrix (Fin n) (Fin n) E, starσ σ h = h ∧ starσ σ h' = h' ∧
            (∀ i j, ValuativeRel.valuation E (h i j) ≤ 1) ∧ ValuativeRel.valuation E h.det = 1 ∧
            EntriesIn (algebraMap k E ϖ) m h' ∧ (δ : Matrix (Fin n) (Fin n) E) = h + α • h')

section Split

variable {F : Type*} [Field F]

variable {a b : ℕ}

def blockDiag (A : GL (Fin a) F) (D : GL (Fin b) F) : GL (Fin a ⊕ Fin b) F :=
  ⟨Matrix.fromBlocks (A : Matrix (Fin a) (Fin a) F) 0 0 (D : Matrix (Fin b) (Fin b) F),
    Matrix.fromBlocks ((A⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
      ((D⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F),
    by simp [Matrix.fromBlocks_multiply], by simp [Matrix.fromBlocks_multiply]⟩

variable [ValuativeRel F] [MeasurableSpace F]

variable [TopologicalSpace F] [MeasurableSpace (GL (Fin a ⊕ Fin b) F)]

end Split

end

end PositivityTheory.Rg.Bc.ArchbcB.B
