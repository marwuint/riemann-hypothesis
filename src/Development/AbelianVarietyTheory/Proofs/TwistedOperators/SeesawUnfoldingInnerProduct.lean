import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSub

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.KInvData

theorem hasDerivAt_linear {Z Q : Type} [NormedAddCommGroup Q] [NormedSpace ℂ Q] (U : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ U] (φ : (Z → ℂ) →ₗ[ℂ] Q) {u : ℝ → Z → ℂ} {u' : Z → ℂ} {t : ℝ} (hu : ∀ s, u s ∈ U) (hu' : u' ∈ U)
    (hd : ∀ z, HasDerivAt (fun s => u s z) (u' z) t) : HasDerivAt (fun s => φ (u s)) (φ u') t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 : Filter.Tendsto (slope u t) (nhdsWithin t {t}ᶜ) (nhds u') := by
    rw [tendsto_pi_nhds]
    intro z
    exact hasDerivAt_iff_tendsto_slope.1 (hd z)
  have hm : ∀ s, slope u t s ∈ U := fun s => U.smul_of_tower_mem _ (U.sub_mem (hu s) (hu t))
  have h2 : Filter.Tendsto (fun s => (⟨slope u t s, hm s⟩ : U)) (nhdsWithin t {t}ᶜ) (nhds ⟨u', hu'⟩) :=
    tendsto_subtype_rng.2 h1
  have h3 := ((φ ∘ₗ U.subtype).continuous_of_finiteDimensional.tendsto _).comp h2
  refine h3.congr fun s => ?_
  simp [slope, LinearMap.map_smul_of_tower]

theorem kapX_one {D : D7} (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
  {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
  {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO W X → ℂ) →ₗ[ℂ] Pi}

theorem line_step (hθ : IsInfFam θ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hmap : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p)
    {τ : D.what₂.Tau} {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hY : Y ∈ lieAt W τ)
    (U : Submodule ℂ ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ)) [FiniteDimensional ℂ U]
    (hU : U ≤ algD Γ.M Bs.ψ Bs.emb)
    (hUt : ∀ t : ℝ, ∀ x ∈ U, om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) x ∈ U)
    {ΦD : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} (hΦD : ΦD ∈ U) {Φ Φ₁ : WO W X → ℂ}
    (h0 : IsDatum Γ.M ψ cA ΦD Φ)
    (h1 : IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y 1), 1) ΦD) Φ₁) : p Φ₁ = p Φ := by
  classical
  have huniq : ∀ {x : (Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ} {f g : WO W X → ℂ},
      IsDatum Γ.M ψ cA x f → IsDatum Γ.M ψ cA x g → f = g := fun hf hg =>
    GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cA.surjective hf hg
  let G : Submodule ℂ (((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) × (WO W X → ℂ)) :=
    { carrier := {q | q.1 ∈ U ∧ IsDatum Γ.M ψ cA q.1 q.2}
      add_mem' := fun ha hb => ⟨U.add_mem ha.1 hb.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ ha.2 hb.2⟩
      zero_mem' := ⟨U.zero_mem, GlobalTheory.SquareAgree.CoinvPass.isDatum_zero⟩
      smul_mem' := fun c _ ha => ⟨U.smul_mem c ha.1, GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c ha.2⟩ }
  let fG : G →ₗ[ℂ] U := ((LinearMap.fst ℂ _ _).comp G.subtype).codRestrict U (fun q => q.2.1)
  have hfG : Function.Injective fG := by
    intro q q' hq
    have e1 : q.1.1 = q'.1.1 := congrArg Subtype.val hq
    have e2 : q.1.2 = q'.1.2 := huniq q.2.2 (e1 ▸ q'.2.2)
    exact Subtype.ext (Prod.ext e1 e2)
  haveI : FiniteDimensional ℂ G := Module.Finite.of_injective fG hfG
  let Uf : Submodule ℂ (WO W X → ℂ) := G.map (LinearMap.snd ℂ _ _)
  let Φt : ℝ → WO W X → ℂ := fun t => ωA (oneP θ W τ Y t, 1) Φ
  have hdat : ∀ t, IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W τ Y t), 1) ΦD) (Φt t) := by
    intro t
    have h := hO.weilA ΦD Φ h0 (oneP θ W τ Y t) 1
    rwa [kapX_one] at h
  have hmemU : ∀ t, Φt t ∈ Uf := fun t => ⟨(_, Φt t), ⟨hUt t ΦD hΦD, hdat t⟩, rfl⟩
  have halg : ∀ t, Φt t ∈ algF ψ θ true A B := by
    intro t
    obtain ⟨Φ', hΦ', hD'⟩ := hO.algA' _ (hU (hUt t ΦD hΦD))
    rwa [huniq hD' (hdat t)] at hΦ'
  have hshift : ∀ s t, ωA (oneP θ W τ Y s, 1) (Φt t) = Φt (s + t) := by
    intro s t
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hY s t, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hzero : ∀ t, ∀ l : Module.Dual ℂ Pi, HasDerivAt (fun s => l (p (Φt s))) 0 t := by
    intro t l
    obtain ⟨Φ', hΦ', hder⟩ := hmap.stabM.2 τ Y hY (Φt t) (halg t)
    have hp := hmap.invl τ Y hY (Φt t) (halg t) Φ' hΦ' hder
    have hd : ∀ z, HasDerivAt (fun s => Φt s z) (Φ' z) t := by
      intro z
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hder z)
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show Φt s z = ωA (oneP θ W τ Y (s - t), 1) (Φt t) z
      rw [hshift, sub_add_cancel]
    have h := hasDerivAt_linear (Uf ⊔ Submodule.span ℂ {Φ'}) (l.comp p) (u := Φt)
      (fun s => Submodule.mem_sup_left (hmemU s)) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) hd
    simpa [hp] using h
  have hconst : ∀ l : Module.Dual ℂ Pi, l (p (Φt 1)) = l (p (Φt 0)) := fun l =>
    is_const_of_deriv_eq_zero (fun t => (hzero t l).differentiableAt) (fun t => (hzero t l).deriv) 1 0
  have e1 : Φt 1 = Φ₁ := huniq (hdat 1) h1
  have e0 : Φt 0 = Φ := by
    simp only [Φt]
    rw [GlobalTheory.Mem.Lift.oneP_zero hθ, Prod.mk_one_one, map_one, Module.End.one_apply]
  rw [← e1, ← e0, ← sub_eq_zero]
  exact (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => by rw [map_sub, hconst l, sub_self]

end GlobalTheory.KInvData
