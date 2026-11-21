import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev Cone (ι : K → Type) : Type := (Σ k, ι k) → ℂ

def cls (P : Ideal (MRing ι)) (f : MRing ι) : FnField P :=
  algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f)

def IsHomogOf (P : Ideal (MRing ι)) (x : FnField P) (d : K → ℤ) : Prop :=
  ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ h ∉ P ∧
    (∀ k, (dg k : ℤ) - dh k = d k) ∧ x * cls P h = cls P g

def openPts (P : Ideal (MRing ι)) (Bd : Finset (Ideal (MRing ι))) : Set (Cone ι) :=
  {z | z ∈ mcPts P ∧ ∀ B ∈ Bd, z ∉ mcPts B}

def IsTorusInv (u : Cone ι → ℝ) : Prop :=
  ∀ (c : K → ℂ) (z : Cone ι), (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z

end Points

namespace RLine

end RLine

section Data

abbrev FlagBundleBlocksOverX {K : Type} (ι : K → Type) (Ψ : Type) (N1 N : ℕ) : K ⊕ (Ψ × Fin (N - 1)) → Type :=
  Sum.elim ι (fun q => PluckerBlocks N1 N q.2)

variable (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]

structure ComponentData where

  N : ℕ

  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N

  P : Ideal (MRing ι)
  arith : IsArithVar P (Fintype.card Ψ * j * (N - j) + 1)

  Bd : Finset (Ideal (MRing ι))
  bd_comp : ∀ B ∈ Bd, IsArithVar B (Fintype.card Ψ * j * (N - j)) ∧ P ≤ B

  bdEq : Ideal (MRing ι) → MRing ι
  bdDeg : Ideal (MRing ι) → K → ℕ
  bdEq_spec : ∀ B ∈ Bd, IsMultiHomog (bdEq B) (bdDeg B) ∧ bdEq B ∉ P ∧ bdEq B ∈ B

  N1 : ℕ
  t : ℕ
  what₂ : Ψ → Fin t → Fin N1 → MRing ι
  rowDeg : Ψ → K → ℕ
  quot : ∀ τ, IsQuotRows P (what₂ τ) (rowDeg τ) N
  twist : Ψ → K → ℤ

  basis : Ψ → Matrix (Fin N) (Fin N1) (FnField P)
  ker_basis : ∀ τ, IsKerBasis P (what₂ τ) (basis τ)
  basis_homog : ∀ τ a l, IsHomogOf P (basis τ a l) (twist τ)

  hodge : Ψ → Matrix (Fin (N - j)) (Fin N1) (FnField P)
  hodge_homog : ∀ τ a l, IsHomogOf P (hodge τ a l) (twist τ)
  hodge_indep : ∀ τ, LinearIndependent (FnField P) (hodge τ)
  hodge_sub : ∀ τ a, hodge τ a ∈ Submodule.span (FnField P) (Set.range (basis τ))

  metric : Ψ → Cone ι → Matrix (Fin N1) (Fin N1) ℂ

  detLine : Ψ → HermLine ι

  detCoord : Ψ → FnField P
  detCoord_homog : ∀ τ, IsHomogOf P (detCoord τ) (detLine τ).a

  kMu : K
  k0 : ℕ
  one_le_k0 : 1 ≤ k0

  muCoord : ι kMu → FnField P
  muCoord_homog : ∀ i, IsHomogOf P (muCoord i) 0
  muCoord_ratio : ∀ i i', genPt P ⟨kMu, i⟩ * muCoord i' = genPt P ⟨kMu, i'⟩ * muCoord i
  muCoord_ne : ∃ i, muCoord i ≠ 0

  muLine : HermLine ι
  muLine_a : muLine.a = Pi.single kMu 1

  muRef : HermLine ι
  muRef_a : muRef.a = Pi.single kMu 1

  ample : HermLine ι

  Kamp : ℝ

  S : Finset ℕ
  S_prime : ∀ p ∈ S, p.Prime

  latNum : ℕ → Ψ → Fin N → MRing ι
  latDen : ℕ → Ψ → Fin N → MRing ι
  latFl : ℕ → Ψ → Fin N → HermLine ι

  cuspNorm : ℕ → Cone ι → ℝ

  rd : ℝ

  Lchi : ℝ
  one_le_rd : 1 ≤ rd

  regMu : ℝ → Cone ι → ℝ
  regMu_inv : ∀ t, IsTorusInv (regMu t)

  regCusp : ℝ → Cone ι → ℝ
  regCusp_inv : ∀ t, IsTorusInv (regCusp t)

  regFl : ℝ → Ψ → Fin N → Cone (FlagBundleBlocksOverX ι Ψ N1 N) → ℝ
  regFl_inv : ∀ t τ r, IsTorusInv (regFl t τ r)

variable {Ψ K ι}

namespace ComponentData

variable (D : ComponentData Ψ K ι)

def f (_D : ComponentData Ψ K ι) : ℕ := Fintype.card Ψ

def jp : ℕ := D.N - D.j

def n : ℕ := D.f * D.j * D.jp

def Xo : Set (Cone ι) := openPts D.P D.Bd

def SB (B : ℕ) : Finset ℕ := D.S.filter (· ≤ B)

def U (z : Cone ι) : ℝ := max 0 (⨆ I : ℕ, -Real.log (D.cuspNorm I z))

end ComponentData

end Data

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
