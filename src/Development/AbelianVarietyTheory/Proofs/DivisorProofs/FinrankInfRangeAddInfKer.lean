import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadOnRec

theorem finrank_inf_range_add_inf_ker {K M : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (e : M →ₗ[K] M) (he : ∀ x, e (e x) = e x) (V : Submodule K M) (hV : ∀ x ∈ V, e x ∈ V) :
    finrank K (V ⊓ LinearMap.range e : Submodule K M) + finrank K (V ⊓ LinearMap.ker e : Submodule K M) = finrank K V := by
  let f : V →ₗ[K] V := e.restrict hV
  have h1 : (LinearMap.range f).map V.subtype = V ⊓ LinearMap.range e := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨hV x x.2, x, rfl⟩
    · rintro ⟨hy, z, rfl⟩
      exact ⟨⟨e z, hy⟩, ⟨⟨e z, hy⟩, Subtype.ext (he z)⟩, rfl⟩
  have h2 : (LinearMap.ker f).map V.subtype = V ⊓ LinearMap.ker e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨hy, hk⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hk, rfl⟩
  rw [← h1, ← h2, Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
  exact LinearMap.finrank_range_add_finrank_ker f

theorem finrank_eq_of_bij {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (hf : Function.Bijective f) (p : Submodule K M) (q : Submodule K N) (h : ∀ x, x ∈ p ↔ f x ∈ q) :
    finrank K p = finrank K q := by
  have e : p.map f = q := by
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    constructor
    · rintro ⟨x', hx', e'⟩
      exact hf.1 e' ▸ (h x').1 hx'
    · intro hy
      exact ⟨x, (h x).2 hy, rfl⟩
  rw [← e]
  exact (Submodule.equivMapOfInjective f hf.1 p).finrank_eq

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance runAlgBad {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst

section General

open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}

theorem mem_eig_iff (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ F.P0 F.ψ0⁻¹ ph y) (ha : ActionPin h fw ι ℓ)
    (hG : R.IsGrp F) (hinc : F.P0 ≤ inc.range) (x : Fin (O.nZ i) → D.what₂.LL) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ GlobalTheory.OnTies.toForms h fw ι z x ∈ GlobalTheory.CovTop.spType R F ι := by
  have hb := GlobalTheory.OnTies.toForms_bijective h fw ι z
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ ∀ u : O.U, O.ρ i u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ i g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW ι).ρ (inc g) (GlobalTheory.OnTies.toForms h fw ι z x) =
        (((R.FW ι).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • GlobalTheory.OnTies.toForms h fw ι z x :=
    fun g hg => by
      rw [← t.rho_eq_of_actionPin ha, GlobalTheory.OnCoord.chi_eq_one hG ι hg, one_mul, ← t.ψ_eq g hg, ← map_smul, hb.1.eq_iff]
  refine e1.trans ⟨fun hx => ?_, fun hx u => ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := hinc hg
    exact (e2 u hg).1 (hx ⟨u, t.U_eq.ge hg⟩)
  · exact (e2 u (t.U_eq.le u.2)).2 (hx ⟨inc u, t.U_eq.le u.2⟩)

end General

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

end GlobalTheory.BadOnRec

namespace GlobalTheory.BigOn

end GlobalTheory.BigOn
