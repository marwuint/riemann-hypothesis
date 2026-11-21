import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeRealRdIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Export

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

variable {YS v₀ i j b} in

theorem mem_range_realRd_of_sum {ν : ℂ} (hν : ν ≠ 0) {g : GA D (Wc D j) → ℂ} {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ k, ∃ y, ρ.e i b y = z k) (x : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h : ν • g = ∑ k, z k • evW YS v₀ j (Subtype.val (x k))) : g ∈ Set.range (realRd YS v₀ hρ i j b ν) := by
  choose y hy using hz
  exact (mem_range_realRd_iff YS v₀ hρ i j b hν g).2 ⟨n, y, x, h.trans (Finset.sum_congr rfl fun k _ => by rw [← hy k])⟩

variable (ρ) in

def UnrComb (Φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (k L : Type) (_ : Field k) (_ : NumberField k) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
    (ι : k →+* FractionRing (D.ntw.O i)) (σ : L →+* ℂ), Normal k L ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime], ((D.ntw.l i : ℕ) : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) ∧
    (∀ a, σ (algebraMap k L a) = ρ.e i b (ι a)) ∧
    ∃ (n : ℕ) (a : Fin n → L) (x : Fin n → NX.FmK S ((j : ℕ) + 1)), Φ = ∑ c, σ (a c) • evW YS v₀ j (Subtype.val (x c))

variable {YS v₀ i j b}

end Export

section Any

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

variable (ρ Y i j b) in

def xiLin (Q : Finset (Pl D.host.E)) (M : ℕ) (h : GA D (Vc D j)) (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ) where
  toFun P := ρ.xi i j b Y Q M h P a
  map_add' P P' := by funext g; simp only [Base.xiCoef_apply, map_add, Pi.add_apply]
  map_smul' c P := by funext g; simp only [Base.xiCoef_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem Faithful.mem_range_of_smul {rd : Rd ρ Y i j b} (hF : Faithful rd) {g : GA D (Wc D j) → ℂ} (hg : g ≠ 0) {u : ℂ}
    (h1 : g ∈ Set.range rd) (h2 : u • g ∈ Set.range rd) : ∃ y, ρ.e i b y = u := by
  obtain ⟨f, rfl⟩ := h1
  obtain ⟨f', h2⟩ := h2
  have hf : f ≠ 0 := fun h => hg (by rw [h, map_zero])
  have hdep : ¬ LinearIndependent (FractionRing (X.O i)) ![f, f'] := fun h => by
    have h3 : LinearIndependent ℂ ![rd f, rd f'] := by
      convert hF 2 _ h using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h3 u (-1) (by rw [h2]; simp)).2
    simp at this
  rw [LinearIndependent.pair_iff' hf] at hdep
  push Not at hdep
  obtain ⟨y, rfl⟩ := hdep
  rw [map_smulₛₗ] at h2
  exact ⟨y, smul_left_injective ℂ hg h2⟩

theorem mem_range_of_small (rd : Rd ρ Y i j b) (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → Φ P ∈ Set.range rd)
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    Φ P ∈ Set.range rd := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ Φ P' ∈ Set.range rd := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, 0, by rw [map_zero, map_zero]⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂, e2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, f₁ + f₂, by rw [map_add, map_add, e1, e2]⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, o • f₁, by rw [rd_smul, map_smul, e1]⟩
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Any

section Core
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem exists_evW_eq_phiC (t : FWTie T Rl.toRealDat κ v₀) (ht : t.Evaluates) (j : Fin D.R.m)
    (hσ : GoodEmb T.Q.c (res T (sg0 D A3.A))) (hV : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j) (f : Cu T κ j) :
    ∃ x : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j (Subtype.val x) = phiC T hV (wtA (κ j)) (f : T.R ((j : ℕ) + 1)) := by
  have hx : (YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) ∈ (S.A ((j : ℕ) + 1)).WK := by
    refine ((YS.fi j).wk _).2 ?_
    have e1 : (YS.fi j).e ((YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)) =
        ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) := LinearEquiv.apply_symm_apply _ _
    rw [e1]
    exact (t.e j f).2
  refine ⟨⟨_, hx⟩, Eq.trans ?_ (ht j (sg0 D A3.A) hσ hV f)⟩
  have e2 := LinearEquiv.apply_symm_apply (YS.fi j).e ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [e2]
  rfl

end Core
end GlobalTheory.SeriesTie
