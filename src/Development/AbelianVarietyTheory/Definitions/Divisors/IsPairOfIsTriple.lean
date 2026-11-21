import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace GlobalTheory.ThK.Check

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem resEta_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {a b m : ℕ} (h : ResEtaPow K χ a) (h' : ResEtaPow K χ' b)
    (hm : m = a + b) : ResEtaPow K (χ / χ') m := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x, hm]
  split_ifs
  · simp
  · rcases neg_one_pow_eq_or ℂ b with e | e <;> simp [pow_add, e, div_neg]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩

theorem isPair_of_isTriple {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G Y om om') :
    IsPair B G.M Y.β (Y.β / Y.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧
      IsPair B G.M' Y.α (Y.α / Y.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      resEta_div h.chars.resβ h.chars.resα rfl, h.weil⟩,
    h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      resEta_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

end GlobalTheory.ThK.Check

end
