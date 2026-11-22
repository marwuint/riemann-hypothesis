import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle

theorem dvd_pow_of_vanishing {Y : Scheme.{0}} (O V : Y.Opens) (t : Γ(Y, V))
    (ht : ∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W))
    (hf : ∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z))
    (z : Y) (hz : z ∈ W) : ∃ n : ℕ, ger z (hW hz) t ∣ ger z hz f ^ n := by
  obtain ⟨A, hA, hzA, e⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hz
  have hA' : IsAffineOpen A := hA
  let f' : Γ(Y, A) := Y.presheaf.map (homOfLE e).op f
  let t' : Γ(Y, A) := Y.presheaf.map (homOfLE (e.trans hW)).op t
  have hle : Y.basicOpen f' ≤ Y.basicOpen t' := by
    intro x hx
    have hxA : x ∈ A := Y.basicOpen_le _ hx
    rw [Y.mem_basicOpen _ x hxA] at hx ⊢
    rw [Y.presheaf.germ_res_apply] at hx ⊢
    refine (ht x _).2 ?_
    by_contra hO
    exact hf x (e hxA) hO hx
  have h2 : PrimeSpectrum.basicOpen f' ≤ PrimeSpectrum.basicOpen t' := by
    rw [← hA'.fromSpec_preimage_basicOpen, ← hA'.fromSpec_preimage_basicOpen]
    exact fun x hx => hle hx
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 h2
  have h3 := map_dvd (Y.presheaf.germ A z hzA).hom (Ideal.mem_span_singleton.1 hn)
  rw [map_pow] at h3
  refine ⟨n, ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (e.trans hW)) z hzA t, ← Y.presheaf.germ_res_apply (homOfLE e) z hzA f]
  exact h3

theorem exists_section {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (hD : D.Eff)
    (hr : ∀ (y : X) (g : X.functionFieldˣ), D.IsEqn y g → ∀ (f : X.functionField) (n : ℕ), RegAt y f →
      RegAt y (f ^ n / g) → RegAt y (f / g)) (y : X) :
    ∃ (V : X.Opens) (_ : y ∈ V) (t : Γ(X, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∉ D.supp) ∧
      ∀ z (hz : z ∈ V) (b : X.presheaf.stalk z) (n : ℕ), ger z hz t ∣ b ^ n → ger z hz t ∣ b := by
  obtain ⟨U, hyU, g, hg⟩ := D.exists_isEqn_nhds y
  obtain ⟨a, ha⟩ := (hg y hyU).regularAt_iff.1 (hD y)
  rw [one_mul] at ha
  obtain ⟨W, hyW, s, rfl⟩ := X.presheaf.germ_exist a
  have inj := fun z : X => IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have key : ∀ z (hz : z ∈ W ⊓ U), algebraMap _ X.functionField
      (ger z hz (X.presheaf.map (homOfLE inf_le_left).op s)) = g := fun z hz => by
    refine Eq.trans ?_ ((algebraMap_germ hz.1 s).trans ((algebraMap_germ hyW s).symm.trans ha))
    exact congrArg _ (X.presheaf.germ_res_apply (homOfLE inf_le_left) z hz s)
  refine ⟨W ⊓ U, ⟨hyW, hyU⟩, X.presheaf.map (homOfLE inf_le_left).op s, fun z hz => ?_, fun z hz b n hb => ?_⟩
  · rw [(hg z hz.2).mem_supp_iff, not_not]
    refine ⟨fun h => ⟨_, h, key z hz⟩, fun ⟨u, hu, e⟩ => ?_⟩
    rwa [inj z (e.trans (key z hz).symm)] at hu
  · obtain ⟨c, hc⟩ := hb
    obtain ⟨d, hd⟩ := hr z g (hg z hz.2) (algebraMap _ X.functionField b) n ⟨b, rfl⟩ ⟨c, by
      rw [eq_div_iff g.ne_zero, ← map_pow, hc, map_mul, key z hz, mul_comm]⟩
    refine ⟨d, inj z ?_⟩
    rw [map_mul, key z hz, hd, mul_div_cancel₀ _ g.ne_zero]

end GlobalTheory.BdEquation
