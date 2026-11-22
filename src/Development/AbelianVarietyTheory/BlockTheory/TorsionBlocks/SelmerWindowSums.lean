import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.finKs (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.Ks K s) := by
  classical
  have hl : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hK : FiniteDimensional ℚ_[l] ↥(K.1) := K.2
  have hK0 : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : (K.1 : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) ⊓
        _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l ≤ K.1)).toLinearMap (RingHom.injective _)
  have hfin : {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}.Finite := by
    refine (Polynomial.nthRoots (l ^ s) (1 : _root_.Formalism.BasicNotions.Loc.Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hl] using hx
  have : Finite {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1} := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hl (by rw [show x ^ l ^ s = 1 from hx]; exact isIntegral_one)
  unfold _root_.Formalism.BasicNotions.Loc.Ks
  infer_instance

def levelField (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finKs K s⟩

section Generic

variable {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]

def charLat (hO : Function.Injective (algebraMap O LL)) (ψ : G →* LLˣ)
    (hψ : ∀ g, ∃ a : O, algebraMap O LL a = ((ψ g : LLˣ) : LL)) :
    Lattice (O := O) (charRep ψ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hψ g
    refine ⟨b * a, ?_⟩
    change algebraMap O LL (b * a) = ((ψ g : LLˣ) : LL) * algebraMap O LL a
    rw [map_mul, hb]
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hO)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

variable [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) [Algebra Qp LL] [TopologicalSpace LL]
    [ContinuousAdd LL] [ContinuousConstSMul LL LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))

end Generic

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem (P : _root_.Formalism.BasicNotions.LocPrime l) (K LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (g : ↥(_root_.Formalism.BasicNotions.Loc.GK K)) :
    ((_root_.Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : _root_.Formalism.BasicNotions.Loc.GQ l) 0 1 (by simp)
  have hnorm : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have ha' : ‖(a : ℚ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] a
    calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
        = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) + a‖ := by ring_nf
      _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le (by simpa using ha) ha'
  unfold _root_.Formalism.MainNotions.N.cycLL
  show algebraMap ℚ_[l] LL (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∈ _
  rw [P.PD_χ K g]
  have hmap : algebraMap ℚ_[l] LL ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) =
      algebraMap ℤ_[l] LL ⟨_, hnorm⟩ := rfl
  rw [hmap]
  unfold _root_.Formalism.BasicNotions.Loc.OL
  exact (integralClosure ℤ_[l] LL).algebraMap_mem _

variable {P : LocPrime l} (AI : LocAinf l P)

def piS (s : ℕ) : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

def resKs {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (Y : Lat K LL) :
    Representation ↥LL.1 ↥(GK (levelField K s)) Y.V :=
  Y.ρ.comp (Subgroup.inclusion (GK_le (K := K) (K' := levelField K s) h.2.2.1))

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified
