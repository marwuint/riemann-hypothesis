import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Matrix
open scoped NNReal Classical

namespace GlobalTheory.WeilM.SplitModel

variable {K : Type} [Field K]

def sw (K : Type) [Field K] : (K × K) →ₐ[K] (K × K) := (AlgHom.snd K K K).prod (AlgHom.fst K K K)

@[simp] lemma sw_apply (z : K × K) : sw K z = (z.2, z.1) := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def g₁ (J : Matrix ι ι (K × K)) : UG (sw K) J →* GL ι K :=
  (Matrix.GeneralLinearGroup.map (RingHom.fst K K)).comp (UG (sw K) J).subtype

lemma g₁_val (J : Matrix ι ι (K × K)) (g : UG (sw K) J) :
    ((g₁ J g : GL ι K) : Matrix ι ι K) = ((g : GL ι (K × K)) : Matrix ι ι (K × K)).map Prod.fst := rfl

def om (lam : Kˣ →* ℂ) (J : Matrix ι ι (K × K)) : UG (sw K) J →* Module.End ℂ ((ι → K) → ℂ) where
  toFun g := lam (Matrix.GeneralLinearGroup.det (g₁ J g)) •
    LinearMap.funLeft ℂ ℂ (fun x : ι → K => (((g₁ J g)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x)
  map_one' := by
    ext φ x; simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    simp only [map_mul, _root_.mul_inv_rev, Units.val_mul, LinearMap.smul_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, Module.End.mul_apply, map_smul, smul_eq_mul, mulVec_mulVec]
    ring

lemma om_apply (lam : Kˣ →* ℂ) (J : Matrix ι ι (K × K)) (g : UG (sw K) J) (φ : (ι → K) → ℂ) (x : ι → K) :
    om lam J g φ x = lam (Matrix.GeneralLinearGroup.det (g₁ J g)) *
      φ ((((g₁ J g)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) := rfl

variable [Invertible (2 : K)]

variable [Fintype K]

variable [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K]

end GlobalTheory.WeilM.SplitModel

namespace GlobalTheory.WeilM.SplitModel

end GlobalTheory.WeilM.SplitModel

end

noncomputable section

open MeasureTheory Matrix ValuativeRel NumberField
open scoped NNReal Topology

namespace GlobalTheory.WeilM.SiegelModel

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

variable [Invertible (2 : R)]

omit [DecidableEq α] in

theorem rho_diag (ψ : AddChar R ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) (z : Matrix α β E)
    (φ : (κ ⊕ κ → R) → ℂ) (u : κ → R) :
    dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ) φ (Sum.elim u u) = φ (Sum.elim (u + (d.e z).1) (u + (d.e z).1)) := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one, Darboux.rho, h, schr]
  have e : (Sum.elim u u + Sum.elim (d.e z).1 (d.e z).1 : κ ⊕ κ → R) = Sum.elim (u + (d.e z).1) (u + (d.e z).1) := by
    ext (k | k) <;> rfl
  simp [sumElim_dotProduct_sumElim, e]

end Alg

section RankZero

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

def detOm (lam : Eˣ →* Circle) (J : Matrix β β E) (X : Type) : UG c J →* Module.End ℂ (X → ℂ) :=
  (algebraMap ℂ (Module.End ℂ (X → ℂ)) : ℂ →* _).comp
    (Circle.coeHom.comp (lam.comp (GeneralLinearGroup.det.comp (UG c J).subtype)))

omit [Invertible (2 : R)] in
theorem detOm_apply (lam : Eˣ →* Circle) (J : Matrix β β E) (X : Type) (g : UG c J) (φ : X → ℂ) :
    detOm lam J X g φ = (lam (GeneralLinearGroup.det (g : GL β E)) : ℂ) • φ := rfl

variable [TopologicalSpace R] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology R E] {C : TestClass R}

end RankZero

def argC : ℂˣ →* Circle where
  toFun z := ⟨z / ‖(z : ℂ)‖, by simp [Submonoid.unitSphere, z.ne_zero]⟩
  map_one' := Circle.ext (by simp)
  map_mul' z w := Circle.ext (by
    show ((z * w : ℂˣ) : ℂ) / ‖((z * w : ℂˣ) : ℂ)‖ = z / ‖(z : ℂ)‖ * (w / ‖(w : ℂ)‖)
    simp [mul_div_mul_comm])

theorem argC_apply (z : ℂˣ) : (argC z : ℂ) = z / ‖(z : ℂ)‖ := rfl

end GlobalTheory.WeilM.SiegelModel
end
