import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteLevelPreimageFinitelyManyCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.VFormCls

open Formalism.IndefR.Bridge

theorem reps_inj {G Γ' : Type} [Group G] [Group Γ'] {ι : Γ' →* G} {J : Subgroup G} {I : Type} {y : I → G}
    (hy : IsReps ι J y) : Function.Injective y := by
  intro i i' h
  exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [h]⟩

theorem transport {G G' Γ' : Type} [Group G] [Group G'] [Group Γ'] (Γ : Subgroup G) (ι : Γ' →* G')
    (hι : Function.Injective ι) (φ : G →* G') (hφ : Function.Bijective φ) (a : G)
    (hrat : ∀ h, h ∈ Γ ↔ ∃ γ, ι γ = φ (a⁻¹ * h * a)) (J' : Subgroup G') {I : Type} [Fintype I]
    (y : I → G') (hy : IsReps ι J' y) :
    ∃ T : Finset G, (∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t * κ) ∧
      ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (F F' : G' → W),
        adInner ι J' y F F' = ∑ t ∈ T, ((Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ J'.comap φ} : ℕ) : ℂ)⁻¹ *
          inner ℂ (F (φ (a⁻¹ * t))) (F' (φ (a⁻¹ * t))) := by
  classical
  let e : G ≃* G' := MulEquiv.ofBijective φ hφ
  have he : ∀ x, φ (e.symm x) = x := fun x => e.apply_symm_apply x
  let t : I → G := fun i => a * e.symm (y i)
  have hty : ∀ i, φ (a⁻¹ * t i) = y i := by
    intro i; simp only [t, ← mul_assoc, inv_mul_cancel, one_mul, he]
  have tinj : Function.Injective t := by
    intro i i' h
    apply reps_inj hy
    rw [← hty i, ← hty i', h]

  have hrat' : ∀ γ : Γ, ∃ γ', ι γ' = φ (a⁻¹ * γ * a) := fun γ => (hrat γ).1 γ.2

  have key : ∀ (g : G) (i : I), (∃ (γ : Γ) (κ : G), κ ∈ J'.comap φ ∧ g = (γ : G) * t i * κ) ↔
      ∃ (γ' : Γ') (k : J'), φ (a⁻¹ * g) = ι γ' * y i * k := by
    intro g i
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨γ', hγ'⟩ := hrat' γ
      refine ⟨γ', ⟨φ κ, hκ⟩, ?_⟩
      rw [hγ', ← hty i]
      simp only [t, map_mul, map_inv, he]
      group
    · rintro ⟨γ', k, h⟩
      have hγ : a * e.symm (ι γ') * a⁻¹ ∈ Γ := by
        rw [hrat]; exact ⟨γ', by simp [he, mul_assoc]⟩
      refine ⟨⟨_, hγ⟩, e.symm k, by simp [he], ?_⟩
      apply hφ.1
      have h2 : φ g = φ a * (ι γ' * y i * k) := by
        rw [← h, map_mul, map_inv]; group
      rw [h2]
      simp only [t, map_mul, map_inv, he]
      group
  choose c hc using hrat'
  refine ⟨Finset.univ.image t, ?_, ?_⟩
  · intro g
    obtain ⟨i, ⟨γ', k, hi⟩, huniq⟩ := hy (φ (a⁻¹ * g))
    refine ⟨t i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 ⟨γ', k, hi⟩⟩, ?_⟩
    rintro s ⟨hs, hd⟩
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs
    rw [huniq i' ((key g i').1 hd)]
  · intro W _ _ F F'
    rw [Finset.sum_image (fun i _ j _ h => tinj h)]
    unfold adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hty i]
    congr 2
    refine congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr (Equiv.symm ?_))
    refine
      { toFun := fun γ => ⟨c γ.1, ?_⟩
        invFun := fun γ' => ⟨⟨a * e.symm (ι γ'.1) * a⁻¹, (hrat _).2 ⟨γ'.1, by simp [he, mul_assoc]⟩⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [mem_stab, hc γ.1, ← hty i]
      have := γ.2
      rw [Subgroup.mem_comap] at this
      convert this using 1
      simp only [map_mul, map_inv]; group
    · have := γ'.2
      rw [mem_stab] at this
      rw [Subgroup.mem_comap]
      convert this using 1
      simp only [t, map_mul, map_inv, he]; group
    · intro γ
      apply Subtype.ext; apply Subtype.ext
      apply hφ.1
      simp only [map_mul, map_inv, he]
      rw [hc]
      simp only [map_mul, map_inv]
      group
    · intro γ'
      apply Subtype.ext
      apply hι
      rw [hc]
      simp [he, mul_assoc]

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (g : G) (k : J) : F (g * k) = (χ k : ℂ) • F g := by
  have h0 := hF 1 g k
  simpa using h0

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.L2.Theta

theorem ipA_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) (μ : D.what₂.Tup) (i : Fin D.R.m)
    (x y : GA D (Vc D i) → (R.cV i).W) :
    (toLiftReal R F tupT hm hTop hinj).ipA μ i x y = (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) x y :=
  rfl

set_option maxHeartbeats 1000000 in

theorem inner_eq {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : Fin D.R.m) :
    ∃ Fx : D.what₂.Mt μ (j.1 + 1) → (Bridge.Gf (Vc D j) → (X.R.cV j).W),
      (∀ x, Fx x ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).J (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).χ) ∧
      (∀ x, (X.R.cV j).ext (Fx x) = X.fn hμ j x) ∧
      ∀ x y, inner ℂ x y = (((RealDat.nP X.F false)⁻¹ : ℝ) : ℂ) *
        Bridge.adInner (Bridge.ratF (Vc D j)) (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ))).J
          (X.R.B.L j (X.tupT μ)).pres.y (Fx x) (Fx y) := by
  have hC := X.given.core
  have hHV := hC.models.HV j (X.tupT μ)
  have hex : ∀ x : D.what₂.Mt μ (j.1 + 1), ∃ h, X.R.extV j (X.tupT μ) h = X.fn hμ j x :=
    fun x => (X.IL.jMt μ hμ j x).2.1
  choose hx hhx using hex
  refine ⟨fun x => (X.R.HV j (X.tupT μ)).e (hx x), fun x => ?_, fun x => hhx x, fun x y => ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HV j (X.tupT μ)).e (hx x)
    rw [hHV.2.1] at h
    exact h
  · have hmt := X.recR.tied.lift.mt μ hμ j x y
    rw [hmt]
    refine Eq.trans (ipA_eq X.R X.F X.tupT X.hm X.hTop X.hinj μ j (X.fn hμ j x) (X.fn hμ j y)) ?_
    congr 1
    unfold ipVia
    have h1 : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := ⟨hx x, hhx x⟩
    have h2 : X.fn hμ j y ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := ⟨hx y, hhx y⟩
    split_ifs with h
    · have e1 : h.1.choose = hx x := X.hinj j _ (h.1.choose_spec.trans (hhx x).symm)
      have e2 : h.2.choose = hx y := X.hinj j _ (h.2.choose_spec.trans (hhx y).symm)
      exact (congrArg₂ (fun a b => inner ℂ a b) e1 e2).trans (hHV.2.2 (hx x) (hx y))
    · exact absurd ⟨h1, h2⟩ h

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

open Formalism.IndefR Formalism.L2.Theta

set_option maxHeartbeats 4000000 in

theorem frame_bij {D : D7} {V : TH.HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) :
    Function.Bijective ((finHom V).rangeRestrict.comp P.ψ) := by
  obtain ⟨hsplit, -, hinter, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  constructor
  · intro x y h
    apply P.inj
    have h1 : finHom V (P.ψ x) = finHom V (P.ψ y) := congrArg Subtype.val h
    have h2 : (P.ψ y)⁻¹ * P.ψ x = 1 := by
      apply hinter
      · show _ ∈ (finHom V).ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      · exact (GfC V).mul_mem ((GfC V).inv_mem (P.into y)) (P.into x)
    exact (inv_mul_eq_one.1 h2).symm
  · intro x
    obtain ⟨g, hg⟩ := x.2
    obtain ⟨a, ha, k, hk, rfl⟩ := hsplit g
    obtain ⟨h, hh⟩ := P.onto k hk
    have ha' : finHom V a = 1 := ha
    refine ⟨h, Subtype.ext ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul, hh]

theorem ratF_inj {D : D7} (V : TH.HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  intro γ h
  have h1 : finHom V (γ : GA D V) = 1 := congrArg Subtype.val h
  exact Subtype.ext (GlobalTheory.DefFree.AdelCls.rat_inj V γ γ.2
    ((GlobalTheory.DefFree.AdelCls.finU_eq_one_iff V _).2 (MonoidHom.mem_ker.2 h1)))

end GlobalTheory.VFormCls

namespace GlobalTheory.VFormCls

end GlobalTheory.VFormCls

end
