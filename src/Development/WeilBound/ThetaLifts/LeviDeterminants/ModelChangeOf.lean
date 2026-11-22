import Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsNeOfSurjOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
import Development.WeilBound.ThetaLifts.LeviDeterminants.ChiIndep
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.DarbouxModelRationalLatticeOf

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem exists_linearEquiv_of_rational {K R E α β κ : Type} [Field K] [CommRing R] [Algebra K R] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Fintype α] [Fintype β] [Fintype κ]
    (hinj : Function.Injective (algebraMap K R))
    (e : Matrix α β (R ⊗[K] E) ≃ₗ[R] (κ → R) × (κ → R))
    (h : ∀ x : Matrix α β E, ∃ y z : κ → K, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R (y i), fun i => algebraMap K R (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[K] (κ → K) × (κ → K), ∀ x, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R ((d₀ x).1 i), fun i => algebraMap K R ((d₀ x).2 i)) := by
  classical
  haveI : Nontrivial R := hinj.nontrivial
  choose y z hyz using h
  have hadd : ∀ a b : Matrix α β E, ((a + b).map fun t => (1 : R) ⊗ₜ[K] t) =
      (a.map fun t => (1 : R) ⊗ₜ[K] t) + b.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro a b
    ext i j
    simp [TensorProduct.tmul_add]
  have hsmul : ∀ (c : K) (a : Matrix α β E), ((c • a).map fun t => (1 : R) ⊗ₜ[K] t) =
      algebraMap K R c • a.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro c a
    ext i j
    change (1 : R) ⊗ₜ[K] (c • a i j) = algebraMap K R c • ((1 : R) ⊗ₜ[K] a i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let f : Matrix α β E →ₗ[K] (κ → K) × (κ → K) :=
    { toFun := fun x => (y x, z x)
      map_add' := by
        intro a b
        have key := hyz (a + b)
        rw [hadd, map_add, hyz a, hyz b] at key
        have h1 : ∀ i, algebraMap K R (y a i) + algebraMap K R (y b i) = algebraMap K R (y (a + b) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R (z a i) + algebraMap K R (z b i) = algebraMap K R (z (a + b) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (a + b) i) = algebraMap K R (y a i + y b i)
          rw [map_add, h1]
        · change algebraMap K R (z (a + b) i) = algebraMap K R (z a i + z b i)
          rw [map_add, h2]
      map_smul' := by
        intro c a
        have key := hyz (c • a)
        rw [hsmul, map_smul, hyz a] at key
        have h1 : ∀ i, algebraMap K R c * algebraMap K R (y a i) = algebraMap K R (y (c • a) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R c * algebraMap K R (z a i) = algebraMap K R (z (c • a) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (c • a) i) = algebraMap K R (c * y a i)
          rw [map_mul, h1]
        · change algebraMap K R (z (c • a) i) = algebraMap K R (c * z a i)
          rw [map_mul, h2] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : (a.map fun t => (1 : R) ⊗ₜ[K] t) = b.map fun t => (1 : R) ⊗ₜ[K] t :=
      e.injective (by rw [hyz a, hyz b, h1, h2])
    ext i j
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := R) (B := E) hinj (congrFun (congrFun h3 i) j)
  have hdim : Module.finrank K (Matrix α β E) = Module.finrank K ((κ → K) × (κ → K)) := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi, Module.finrank_baseChange] at h1
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi]
    simpa using h1
  refine ⟨LinearMap.linearEquivOfInjective f hf hdim, fun x => ?_⟩
  simpa [f] using hyz x

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem ratRel_of_good {ψ : AddChar (AF F) ℂ} {M M₁ : Model σ X W} (h : M.IsGood ψ) (h₁ : M₁.IsGood ψ) : RatRel M.co M₁.co := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d₀, hd⟩ := exists_linearEquiv_of_rational (AdeleRing.algebraMap_injective (𝓞 F) F) M.co.e h.rat
  intro y z
  obtain ⟨x, hx⟩ := d₀.surjective (y, z)
  obtain ⟨y', z', h'⟩ := h₁.rat x
  refine ⟨incM F x, y', z', ?_, h'⟩
  have := hd x
  rw [hx] at this
  exact this

end PositivityTheory.ThKF0

end
