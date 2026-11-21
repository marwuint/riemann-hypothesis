import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvectorStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Adele.IntegersLattice

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def Scales (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (p : GAd σ J)
    (l : (AF F ⊗[F] E)ˣ) : Prop := (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x

structure Data (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  unr : Algebra.Unramified (𝓞 F) (𝓞 E)
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  adapted : GlobalTheory.EisLine.IsAdapted σ J X Y L a
  iwa : ∀ g, ∃ p l, Scales σ J (col X) p l ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p l, Scales σ J (col X) p l → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

structure IsFlow (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (a : ℝ → GAd σ J) : Prop where
  cont : Continuous a
  add : ∀ s t, a (s + t) = a s * a t
  onX : ∀ t, ∃ l, Scales σ J (col X) (a t) l ∧ (absE F E l : ℝ) = Real.exp t
  onY : ∀ t, ∃ l, Scales σ J (col Y) (a t) l ∧ (absE F E l : ℝ) = Real.exp (-t)
  mem : ∀ t, a t ∈ GlobalTheory.StdPar.levi σ J X Y {0}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {0}, a t * m = m * a t

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

abbrev Pl : Type := Multiplicative (Fin 2 → ℝ)

scoped instance measurableSpacePl : MeasurableSpace Pl := borel _

scoped instance borelSpacePl : BorelSpace Pl := ⟨rfl⟩

def axis (i : Fin 2) : Subgroup Pl where
  carrier := {g | ∀ j, j ≠ i → g.toAdd j = 0}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  inv_mem' := fun ha j hj => by simp [ha j hj]

theorem cont_coord (j : Fin 2) : Continuous fun g : Pl => g.toAdd j := (continuous_apply j).comp continuous_toAdd

theorem isClosed_axis (i : Fin 2) : IsClosed (axis i : Set Pl) := by
  have : (axis i : Set Pl) = ⋂ j, ⋂ (_ : j ≠ i), {g | g.toAdd j = 0} := by ext g; simp [axis]
  rw [this]
  exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (cont_coord j) continuous_const

scoped instance locallyCompactSpace_axis (i : Fin 2) : LocallyCompactSpace (axis i) := (isClosed_axis i).locallyCompactSpace

theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

end Inhab

end GlobalTheory.ResLine

end
