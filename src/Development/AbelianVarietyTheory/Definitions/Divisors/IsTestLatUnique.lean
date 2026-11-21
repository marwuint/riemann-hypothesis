import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG Formalism.IndefR
open GlobalTheory.ChiGrid GlobalTheory.TestLat GlobalTheory.CoefModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.FunObj.TestLatModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

theorem finE_rat (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram) (h : Bridge.IsRatMat (Xp G) γ γE.1) :
    Formalism.IndefR.Lev.finE (Xp G) γ = ratIn G γE := by
  have h' : matHom (Xp G) γ = bc (incA D) γE.1 := h
  apply Units.ext
  show ((matHom (Xp G) γ).1.map _).map _ = γE.1.1.map _
  rw [h']
  ext i j
  rfl

theorem map_rhoVr {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (γ : GQ V)
    (γE : GL (Fin V.rank) D.host.E) (h : Bridge.IsRatMat V γ γE) (x : GA D V) (v : VV D.what₂.LL lam) :
    rhoK lam (invTrK (realGL θ V (γ.1 * x)⁻¹)) (mapVV D.what₂.embLL lam (rhoVr (labLL D) lam γE v)) =
      rhoK lam (invTrK (realGL θ V x⁻¹)) (mapVV D.what₂.embLL lam v) := by
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have e : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
    funext τ
    apply Units.ext
    rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE h, embGL_inv, ← map_inv, embGL_coe, bc_coe]
    ext a b
    exact hlab _ _
  have e2 : (γ.1 * x)⁻¹ * γ.1 = x⁻¹ := by group
  show rhoK _ _ (mapVV _ _ (rhoK lam (invTrK (embGL (labLL D) γE)) _)) = _
  rw [mapVV_rhoK, e, ← Module.End.mul_apply, ← map_mul (rhoK lam), ← map_mul invTrK, ← map_mul (realGL θ V), e2]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

theorem mem_globLat_rat (γ : GL (Fin n) E) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E) :
    γ.1 *ᵥ x ∈ CS.globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g) Λ ↔ x ∈ CS.globLat g Λ := by
  have e : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ.1 *ᵥ x) i)) =
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ).1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [e, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem globLat_mul [StarRing E] (g k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ)) : CS.globLat (g * k) Λ = CS.globLat g Λ := by
  ext x
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec]
  exact ((inv_mem hk : k⁻¹ ∈ _) _).symm

end Gen

theorem mem_latOf_rat (γ : UR D.sp.cm (Xp G).gram) (g : GLf G) (x : Fin (Xp G).rank → D.host.E) :
    γ.1.1 *ᵥ x ∈ latOf G (ratIn G γ * g) ↔ x ∈ latOf G g := mem_globLat_rat _ γ.1 g x

theorem latOf_mul (g : GLf G) {k : GLf G} (hk : k ∈ G.Kplus) : latOf G (g * k) = latOf G g :=
  globLat_mul _ g k hk.2.1

theorem exists_testLat (h : (L.ΛY 0).FG) (rp : ClassReps G) : ∃ n e X M, 0 < n ∧ IsTestLat G rp n e X M := by
  obtain ⟨n, ⟨e⟩⟩ := exists_coords G h
  obtain ⟨X, M, hM⟩ := exists_isTestLat G rp n e
  obtain ⟨i⟩ := SlopeModel.nonempty_idx (LaP G)
  exact ⟨n, e, X, M, (e.symm (⟨fun _ => default, Quotient.mk'' 1⟩, i)).pos, hM⟩

end GlobalTheory.FunObj.TestLatModel

end
