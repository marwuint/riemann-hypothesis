import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IterSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCutoff (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) (β : GA D S → ℝ) : Prop :=
  (∀ h, 0 ≤ β h) ∧ Measurable β ∧ ∀ h,
    Integrable (fun p : NI S CS × GA D S0 => β ((p.1 : GA D S) * lev p.2 * h)) (μN.prod μ0) ∧
      ∫ p, β ((p.1 : GA D S) * lev p.2 * h) ∂(μN.prod μ0) = 1

def MU (S : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) : Subgroup (GA D S) :=
  Subgroup.closure {g | ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
    HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    HMul.hMul (mt S g) (BS.map (incA D)) = BS.map (incA D) ∧
    ∃ v : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS'.map (incA D)) = HMul.hMul (CS'.map (incA D)) v}

def IsPsiUVal (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) (v : ℂ) : Prop :=
  ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    v = ψ (Algebra.trace (AF D.host.F) (AE D) (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then u i j else 0))

open Classical in

def psiU (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) : ℂ :=
  if h : ∃ v, IsPsiUVal ψ S CS g v then h.choose else 1

def jac (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (My : Mx D T0.rank ρ) (n : GA D S)
    (Ξ : WO S0 T0 → ℂ) : WO S0 T0 → ℂ :=
  fun x =>
    let w₁ : WO S T0 := HMul.hMul (embP S T0 CS' My + embQ S T0 S0 BS x) (mt S n)
    ψ (symplOH S T0 (embP S T0 CS' My + embQ S T0 S0 BS (HMul.hMul w₁ (BS.map (incA D))))
        (embS S T0 CS (HMul.hMul w₁ (CS'.map (incA D))))) *
      Ξ (HMul.hMul w₁ (BS.map (incA D)))

end Formalism.IndefR.Mi

end
