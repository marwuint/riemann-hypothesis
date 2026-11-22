import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq

noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

end Record

end GlobalTheory.LvT.StabOrder
