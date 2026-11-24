module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Algebra.Module.ZMod
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem finTw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  have hs : ∀ i j, ∀ x, ∀ᶠ y in nhds x, f y i j = f x i j := fun i j =>
    (IsLocallyConstant.iff_eventually_eq _).1 (h i j)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hall : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simpa only [Filter.eventually_all] using fun i j => hs i j x
  filter_upwards [hall] with y hy
  ext i j
  exact hy i j

theorem UpperTheory.V.Pa.finTw :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), PhiCond G0.Γ l → (TwZ k (x.Am m)).Finite := by
  intro l _ L G0 n x k m hΦ
  obtain ⟨_, _, hfinR, _, hlR, _, htR, _, _⟩ := finAm l G0.frame n x m k.g
  let χ : G0.Γ →* x.A := (algebraMap ℤ_[l] x.A).toMonoidHom.comp ((Units.coeHom ℤ_[l]).comp G0.ε)
  have hok := (ok1 l L G0 G0 (Glob.Hom.refl G0) n x k (x.Am m) χ).2.1
  obtain ⟨rep, hrep⟩ := adEx l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ hok
  obtain ⟨_, hlce, hLC⟩ := lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m
  have hLCrep := hLC _ _ rep hlce hrep
  haveI : Finite (DD (x.Am m) k.g) := hfinR
  have hl : ∀ v : pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a, l • v = 0 := by
    intro v
    apply Subtype.ext
    funext i j
    simp [hlR]
  have finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
      Finite (M →+ ZMod l) := by
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective
  
  have eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
      (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
    letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
    let b := Module.Basis.ofVectorSpace (ZMod l) M
    apply b.repr.injective
    ext i
    have := h (b.coord i).toAddMonoidHom
    rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simpa using this
  have finZ_local : ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) := by
    intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
    let N : Subgroup Γ :=
      { carrier := {g | ∀ m, ρ g m = m}
        mul_mem' := by
          intro a b ha hb m
          simp only [Set.mem_setOf_eq] at ha hb
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by
          intro m
          simp
        inv_mem' := by
          intro a ha m
          simp only [Set.mem_setOf_eq] at ha
          have h1 := ha (ρ a⁻¹ m)
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
          exact h1.symm }
    have hN : IsOpen (N : Set Γ) := by
      have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
        ext g
        simp [N]
      rw [hset]
      exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
    haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
    haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
    haveI := hΦ N hN
    have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
      intro z hz
      simpa using ((mem_Zl ρ).1 hz).2 1 1
    have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
      intro z hz a b ha
      rw [((mem_Zl ρ).1 hz).2, ha]
    refine Finite.of_injective
      (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
        {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
      (fun z => (fun q => z.1 q.out, fun f =>
        ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
    · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
      rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
    · intro k k'
      show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
        Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
      rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add (f := _), ofAdd_add]
    · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
        (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
      rw [MonoidHom.coe_ker]
      exact hlc.isOpen_fiber 1
    · intro z z' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply Subtype.ext
      funext g
      have key : ∀ k : N, z.1 k = z'.1 k := by
        intro k
        have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
          intro f
          have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
            Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
          rw [map_sub, h3, sub_self]
        exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
      have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
        rw [hk]
        simp [mul_assoc]
      have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
        congrFun h1 (QuotientGroup.mk g)
      rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
  have hfin := finZ_local l x.A G0.Γ (pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a) rep hΦ hLCrep hl
  have key : ∀ z ∈ TwZ k (x.Am m), ∃ y ∈ Zl rep, y G0.c = 0 ∧
      ∀ g : G0.frame.G₀, (y (g : G0.Γ) : Matrix _ _ _) = z g := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine (polZ l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ rep hrep).1 z h1 ?_ h3 h4
    apply finTw_lc
    intro i j
    exact (adicLC G0.frame.G₀ (DD (x.Am m) k.g) _ m _ htR).1 (h2 i j)
  let φ : TwZ k (x.Am m) → Zl rep := fun z => ⟨(key z.1 z.2).choose, (key z.1 z.2).choose_spec.1⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    funext g
    have ha := (key a.1 a.2).choose_spec.2.2 g
    have hb := (key b.1 b.2).choose_spec.2.2 g
    have he : (key a.1 a.2).choose = (key b.1 b.2).choose := congrArg Subtype.val hab
    rw [← ha, ← hb, he]
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hinj)
