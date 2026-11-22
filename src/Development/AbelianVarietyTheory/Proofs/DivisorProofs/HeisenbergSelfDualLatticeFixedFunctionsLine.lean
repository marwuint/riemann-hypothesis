import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LatVacLine

theorem vacuum_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hψ hsd θ hθ φ₀ hφSB hφ0 hφ φ hψSB hψ'
  set Λ := latAtV G.V G.W v with hΛ
  set co := G.M.co with hco
  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  classical
  let χ : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E))
        (incM F G.V.J) (incM F G.W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin a × Fin (a + a') → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ Λ, Acts (evFin F v) (co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E))
          (incM F G.V.J) (incM F G.W.J) γ γ) • f)) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l := AddSubgroup.mem_map.mp hl
    obtain ⟨r, hr, x₀, hx₀⟩ := _root_.GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    have key := _root_.GlobalTheory.LatVac.heis_at_local_identity v co B.ψ h.choose f _ (hAt _ h.choose_spec.1) (hA _ h.choose_spec.1) r hr x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := _root_.GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v co hT.geo.hV.lat hT.geo.hW.lat
  have hsd' := _root_.GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ Λ hAt hsd
  have hfill := _root_.GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) c hc0 (fun x => hψ x) hsd'
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  exact _root_.GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) χ φ₀ φ (loc φ₀ hφSB hφ) (loc φ hψSB hψ')
    hφ0 hfill

end GlobalTheory.LatVacLine
