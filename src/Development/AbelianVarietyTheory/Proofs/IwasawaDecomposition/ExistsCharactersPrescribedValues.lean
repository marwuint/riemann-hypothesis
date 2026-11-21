import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

end GlobalTheory.BaseChars
