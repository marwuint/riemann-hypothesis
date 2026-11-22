import Mathlib
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds

noncomputable section

namespace Formalism.MainNotions.PrimeDegreeVariant

open Formalism.BasicNotions MvPolynomial

def blkHom (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

def embGL (R : Type) [CommRing R] (n N : ℕ) (h : n + 1 = N) : GL (Fin n) R →* GL (Fin N) R :=
  Units.map (((Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))).toAlgHom.toRingHom.toMonoidHom).comp
    (blkHom R n))

def lastGL (R : Type) [CommRing R] (N : ℕ) (a : Rˣ) : GL (Fin N) R :=
  diagGL R N (fun i => if i.1 + 1 = N then a else 1)

def wsum {k : ℕ} (l : DomWeight k) : ℤ := ∑ i, l.w i

def Interlace {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, sg.w i ≤ lam.w ⟨i.1, by omega⟩ ∧ lam.w ⟨i.1 + 1, by omega⟩ ≤ sg.w i

def aa {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  sg.w i - lam.w ⟨i.1 + 1, by omega⟩

def bb {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  lam.w ⟨i.1, by omega⟩ - sg.w i

def D0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, (sg.w i - lam.w ⟨i.1 + 1, by omega⟩)

def D1 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg)

def degZ {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n) : ℤ := wsum lam - wsum sg

def Rset {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg))

def cBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - sg.w j + (j.1 : ℤ))

def rowsZ {n N : ℕ} (h : n + 1 = N) (i : Fin n) : Fin (i.1 + 1) → Fin N :=
  fun p => if p.1 = i.1 then ⟨N - 1, by omega⟩ else ⟨p.1, by omega⟩

def xi (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin n, (Formalism.GradedWeylDivisibility.lpMinor R (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat *
    (Formalism.GradedWeylDivisibility.initMinor R (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat

def cBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  (((2 * lam.spread : ℤ) : ℝ)) ^ ((((N : ℤ) * D1 h lam sg : ℤ) : ℝ))

def brBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  cBd h lam sg * Real.sqrt (Module.finrank ℂ (delSq ℂ N lam))

def IsIota {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
    io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) ∧
  (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
    io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s)) ∧
  io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg ∧
  (∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (io s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • io s) ∧
  (∀ s ∈ nablaSq ℂ n sg,
    (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re)

def IsBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
    br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)

def IsTranspose {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ s ∈ nablaSq ℂ n sg, ∀ f ∈ delSq ℂ N lam, normFock lam (io s) f = normFock sg s (br f)

def Branch {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧ xi ℂ h lam sg ≠ 0 ∧
  degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg ∧
  ∃ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io ∧ IsBr h lam sg br ∧ IsTranspose lam sg io br

def Conclusion6 : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

section Abstract

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

structure GoodSet (K : Type) [Field K] (G : Type) [Group G] where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  W : S → Type
  [acgW : ∀ s, AddCommGroup (W s)]
  [modW : ∀ s, Module K (W s)]
  [fdW : ∀ s, FiniteDimensional K (W s)]
  [ntW : ∀ s, Nontrivial (W s)]
  tau : ∀ s, Representation K G (W s)

  irr : ∀ s, Function.Surjective (tau s).asAlgebraHom

  inj : Function.Injective fun s g => LinearMap.trace K (W s) (tau s g)

attribute [instance] GoodSet.finS GoodSet.decS GoodSet.acgW GoodSet.modW GoodSet.fdW GoodSet.ntW

structure Pair (K : Type) [Field K] (G : Type) [Group G] where
  H : Subgroup G
  chi : H →* Kˣ

def eS (T : GoodSet K G) (s : T.S) : MonoidAlgebra K G :=
  ∑ x : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)) • MonoidAlgebra.of K G x

def eG (T : GoodSet K G) : MonoidAlgebra K G := ∑ s, eS T s

open Classical in

def eps (P : Pair K G) : MonoidAlgebra K G :=
  ((Nat.card P.H : ℕ) : K)⁻¹ • ∑ x : G, if h : x ∈ P.H then
    (((P.chi ⟨x, h⟩)⁻¹ : Kˣ) : K) • MonoidAlgebra.of K G x else 0

def nS (T : GoodSet K G) (P : Pair K G) (s : T.S) : ℕ :=
  Module.finrank K (LinearMap.range ((T.tau s).asAlgebraHom (eps P)))

def M1 (T : GoodSet K G) (P0 : Pair K G) : Prop := ∀ s, nS T P0 s = 1

variable (A : HLat K) (ρ : Representation K G A.V)

def cutE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M ⊓ (LinearMap.range e).restrictScalars (𝓞 K)

def imgE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M.map (LinearMap.restrictScalars (𝓞 K) e)

def dimE (e : Module.End K A.V) : ℕ := Module.finrank K (LinearMap.range e)

def degL (M : Submodule (𝓞 K) A.V) : ℝ := (Formalism.HN.rkK M : ℝ) * Formalism.HN.muDef A.b A.X M

def muMaxL (M : Submodule (𝓞 K) A.V) : ℝ := Formalism.HN.muMaxDef A.b A.X M

def lenAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥M ⧸ N.comap M.subtype))

def idxAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℤ :=
  ((lenAt w M N).toNat : ℤ) - ((lenAt w N M).toNat : ℤ)

def LocLe {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) (F : ℕ)
    (M N : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ M, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ F) • N

def IsFull (M : Submodule (𝓞 K) A.V) : Prop := M.FG ∧ Submodule.span K (M : Set A.V) = ⊤

def IsProj (e : Module.End K A.V) (n : ℕ) : Prop :=
  A.Good ∧ 0 < n ∧ e * e = e ∧ (∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) ∧
  ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) y = Formalism.HermitianLatticesTheory.majAt A.b A.X v x (e y)

end Abstract

section Lemma2

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def ProjectionSandwichLength (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  (∀ x ∈ imgE A e A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A e A.L) ∧
  cutE A e A.L ≤ imgE A e A.L ∧
  Nonempty ((↥(imgE A e A.L) ⧸ (cutE A e A.L).comap (imgE A e A.L).subtype) ≃ₗ[𝓞 K]
    (↥(imgE A (1 - e) A.L) ⧸ (cutE A (1 - e) A.L).comap (imgE A (1 - e) A.L).subtype)) ∧
  (∀ w : HeightOneSpectrum (𝓞 K),
    idxAt w (imgE A e A.L) (cutE A e A.L) = idxAt w (imgE A (1 - e) A.L) (cutE A (1 - e) A.L) ∧
    0 ≤ idxAt w (imgE A e A.L) (cutE A e A.L) ∧
    idxAt w (imgE A e A.L) (cutE A e A.L) ≤
      (min (dimE A e) (dimE A (1 - e)) : ℕ) * vAdd w ((n : ℕ) : K)) ∧
  (∀ ψ : Module.Dual K A.V, ψ ∘ₗ e = ψ →
    (ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e))

def DegreeKernelLowerBound (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  degL A A.L - (dimE A (1 - e) : ℝ) * (muMaxL A A.L + 2 * Real.log (n : ℝ)) ≤ degL A (cutE A e A.L)

def KernelIndexFullLattice (A : HLat K) (e : Module.End K A.V) : Prop :=
  ∀ Th : Submodule (𝓞 K) A.V, IsFull A Th →
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w F Th A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th - (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w 0 ((w.asIdeal ^ F) • Th) A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th + (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    cutE A e Th ≤ imgE A e Th

def projection_lemma_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → ProjectionSandwichLength A e n ∧ DegreeKernelLowerBound A e n ∧ KernelIndexFullLattice A e

end Lemma2

section Lemma8

structure GMap (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (T : GoodSet K G)
    (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρE : Representation ℂ G EE) where
  VK : Type
  [acgK : AddCommGroup VK]
  [modK : Module K VK]
  [fdK : FiniteDimensional K VK]
  rhoK : Representation K G VK
  V : Type
  [acgV : AddCommGroup V]
  [modV : Module ℂ V]
  rho : Representation ℂ G V

  j : VK →ₛₗ[σ] V
  j_indep : ∀ (n : ℕ) (b : Fin n → VK), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))
  j_span : Submodule.span ℂ (Set.range j) = ⊤
  j_eq : ∀ g x, j (rhoK g x) = rho g (j x)

  good : rhoK.asAlgebraHom (eG T) = 1
  io : V →ₗ[ℂ] EE
  io_eq : ∀ g x, io (rho g x) = ρE g (io x)

attribute [instance] GMap.acgK GMap.modK GMap.fdK GMap.acgV GMap.modV

end Lemma8

namespace Ten

section Tensor

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (a : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => ∏ i, (a i).coeff (g i))

theorem tens_coeff (a : ∀ i, MonoidAlgebra ℂ (G i)) (g : ∀ i, G i) :
    (tens a).coeff g = ∏ i, (a i).coeff (g i) := rfl

theorem conv_coeff {H : Type} [Group H] [Fintype H] (x y : MonoidAlgebra ℂ H) (g : H) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro i; simp

theorem tens_mul (a b : ∀ i, MonoidAlgebra ℂ (G i)) :
    tens a * tens b = tens (fun i => a i * b i) := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  ext g
  rw [conv_coeff, tens_coeff]
  simp only [tens_coeff, conv_coeff]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

variable [DecidableEq ι]

def plc (i : ι) (a : MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  tens (Function.update (fun _ => 1) i a)

theorem tens_mul_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (i : ι) (b : MonoidAlgebra ℂ (G i)) :
    tens a * plc i b = tens (Function.update a i (a i * b)) := by
  rw [plc, tens_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem mapDomain_mulSingle (i : ι) (a : MonoidAlgebra ℂ (G i)) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun h => Pi.mulSingle (M := G) i h) a.coeff) = plc i a := by
  classical
  ext g
  rw [MonoidAlgebra.coeff_ofCoeff, plc, tens_coeff, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hinj : Function.Injective (fun h : G i => Pi.mulSingle (M := G) i h) := Pi.mulSingle_injective i
  have hrest : ∏ j ∈ Finset.univ.erase i,
      (Function.update (fun j => (1 : MonoidAlgebra ℂ (G j))) i a j).coeff (g j) =
      if ∀ j ∈ Finset.univ.erase i, g j = 1 then 1 else 0 := by
    trans ∏ j ∈ Finset.univ.erase i, (if g j = 1 then (1 : ℂ) else 0)
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), MonoidAlgebra.one_def,
        MonoidAlgebra.coeff_single, Finsupp.single_apply]
      simp [eq_comm]
    · rw [Finset.prod_boole]; congr
  rw [hrest, Function.update_self]
  by_cases hg : ∀ j ∈ Finset.univ.erase i, g j = 1
  · have : g = Pi.mulSingle i (g i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact hg j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
    rw [if_pos hg, mul_one]
    conv_lhs => rw [this]
    exact Finsupp.mapDomain_apply hinj _ _
  · rw [if_neg hg, mul_zero]
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨h, rfl⟩
    exact hg fun j hj => Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj) _

variable {P : ι → Type} [∀ i, Fintype (P i)]

open Classical in

def eGood (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) (good : (∀ i, P i) → Prop) :
    MonoidAlgebra ℂ (∀ i, G i) :=
  ∑ p : ∀ i, P i, if good p then tens (fun i => E i (p i)) else 0

end Tensor

end Ten

section Record

open NumberField IsDedekindDomain

@[instance_reducible] def finiteLevelGroupFintype (D : D7) : Fintype (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Finite (G0g D.nd) := inferInstance
  exact Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

structure GSp (D : D7) where
  V : Type
  [nacg : NormedAddCommGroup V]
  [ips : InnerProductSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  lat : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) V
  act : Representation ℂ (G0g D.nd) V

attribute [instance] GSp.nacg GSp.ips GSp.fd

structure Prov (D : D7) (X : BaseLevelRowSide D) where

  T : GoodSet D.what₂.LL (G0g D.nd)

  T_e : ∀ g, (eG T).coeff g = ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL)

  psi0 : D.nexp.U →* (D.what₂.LL)ˣ

  Ps : Pair D.what₂.LL (G0g D.nd)

  EEK : Type
  [nacgEE : NormedAddCommGroup EEK]
  [ipsEE : InnerProductSpace ℂ EEK]
  [fdEE : FiniteDimensional ℂ EEK]

  sK : RowSide D EEK

  actEE : Representation ℂ (G0g D.nd) EEK

  actAmb : ∀ μ, Representation ℂ (G0g D.nd) (sK.Amb μ)

  cen_tie : ∀ μ z, sK.cen μ z = (actAmb μ).asAlgebraHom (z : MonoidAlgebra ℂ (G0g D.nd))

  MtK : D.what₂.Tup → ℕ → GSp D

  MjK : ℕ → GSp D

  thK : ∀ μ j, (MtK μ j).V →ₗ[ℂ] (MjK j).V

  rho : Representation D.what₂.LL (G0g D.nd) sK.RR.V

  j0 : X.principalHermitianLattice.V →ₗ[D.what₂.LL] sK.RR.V

  js : D.div.RR.V →ₗ[D.what₂.LL] sK.RR.V

attribute [instance] Prov.nacgEE Prov.ipsEE Prov.fdEE

variable {D : D7} {X : BaseLevelRowSide D}

def Conclusion0 (D : D7) : Prop :=
  ∀ Y : ℝ, (∀ i, (D.host.g i : ℝ) ≤ 2 * Y) → lam0 D ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * Y)

section GoodType

local instance factG (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

namespace Ten

def ESer (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (p : Fin D.R.r → ZMod (D.host.g kv.1)) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p)

def goodVec (D : D7) (p : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) : Prop :=
  D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩))

theorem monicOf_inj {K : Type} [Field K] {N : ℕ} (a b : Fin N → K)
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  have hc := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_inj] at hc
  simpa [i.isLt.ne, Finset.sum_ite_eq, Finset.sum_ite_eq'] using hc

theorem e0_eq (D : D7) [DecidableEq (Σ k : Fin 2, D.nd.PlG k)] : D.ntypes.e0 = eGood (ESer D) (goodVec D) := by
  classical
  ext g
  rw [eGood, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  show (∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))), _) = _
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : goodVec D p
  · rw [if_pos hp]; exact (if_pos hp).trans rfl
  · rw [if_neg hp]; exact (if_neg hp).trans rfl

theorem atPlace_eq (D : D7) [DecidableEq (Σ k : Fin 2, D.nd.PlG k)] (k : Fin 2) (v : D.nd.PlG k)
    (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a =
      plc (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ a := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  convert mapDomain_mulSingle (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) a
  all_goals rfl

end Ten

end GoodType

theorem sharp_downTo (D : D7) (μ : D.what₂.Tup) (j : ℕ) :
    (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp ((RowSide.sharp D).io μ j) =
      (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]
    all_goals rfl

def LabTie (Y : Prov D X) (lab : Y.T.S → ∀ k : Fin 2, D.nd.PlG k → Polynomial (ZMod (D.host.g k))) : Prop :=
  ∀ s (g : G0g D.nd), D.what₂.embLL ((eS Y.T s).coeff g) =
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (lab s kv.1 kv.2)).coeff (g kv)

def LevelRatioBound (D : D7) : Prop := 4 * D.R.f * D.R.r ≤ min (D.host.g 0) (D.host.g 1)

end Record

section Herm

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

def IsCM (z : K) : Prop := ∀ σ : K →+* ℂ, σ (star z) = star (σ z)

def IsConjPlK (w w' : HeightOneSpectrum (𝓞 K)) : Prop := ∀ x : K, vAdd w' x = vAdd w (star x)

def IsHermE (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ (∀ x, (∀ y, h x y = 0) → x = 0) ∧ ∀ x y, h (e x) y = h x (e y)

def IsBasisAt (A : HLat K) {d : ℕ} (a : Fin d → A.V) (M : Submodule (𝓞 K) A.V)
    (w w' : HeightOneSpectrum (𝓞 K)) : Prop :=
  LinearIndependent K a ∧ ∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
    LocLe u 0 (Submodule.span (𝓞 K) (Set.range a)) M ∧ LocLe u 0 M (Submodule.span (𝓞 K) (Set.range a))

def LamStar (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (y : A.V) : Prop :=
  y ∈ LinearMap.range e ∧ (∀ u ∈ U, h y u = 0) ∧
  ∀ m ∈ cutE A e A.L, h y m ∈ Set.range (algebraMap (𝓞 K) K)

def IsValG (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Prop :=
  ∃ w', IsConjPlK w w' ∧ ∃ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y ∧
    (∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
      (∀ i, ∃ s : 𝓞 K, s ∉ u.asIdeal ∧ LamStar A e h U (s • y i)) ∧
      ∀ z, LamStar A e h U z → ∃ s : 𝓞 K, s ∉ u.asIdeal ∧
        s • z ∈ Submodule.span (𝓞 K) (Set.range y)) ∧
    n = - vAdd w (Matrix.of fun i j => h (y i) (y j)).det

def L7 (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    (∀ w k, IsValG A e h U w k →
      k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K)) ∧
    (∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)) ∧
    (∀ φ ∈ A.dualL, (∀ u ∈ U, φ u = 0) →
      ∀ m ∈ cutE A e A.L, φ m ∈ Set.range (algebraMap (𝓞 K) K))

end Herm

end Formalism.MainNotions.PrimeDegreeVariant
