import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem laQ_eq : LaQ Dw l = LevQ Dw l := rfl

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

end GlobalTheory.LevPullModel
