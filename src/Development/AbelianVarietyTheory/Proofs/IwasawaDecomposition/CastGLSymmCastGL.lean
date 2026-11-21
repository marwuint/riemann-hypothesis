import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
import Formalism.LocalToGlobal.Columns.InputsGenus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStOneOfInt

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Shift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}

def conjBack (J : Subgroup G) (k : G) : J.map (MulAut.conj k).toMonoidHom ≃* J where
  toFun x := ⟨k⁻¹ * x * k, by
    obtain ⟨j, hj, e⟩ := x.2
    have e' : k⁻¹ * (x : G) * k = j := by
      rw [← e]; show k⁻¹ * (k * j * k⁻¹) * k = j; group
    rw [e']; exact hj⟩
  invFun j := ⟨k * j * k⁻¹, ⟨j, j.2, rfl⟩⟩
  left_inv x := Subtype.ext (by show k * (k⁻¹ * (x : G) * k) * k⁻¹ = x; group)
  right_inv j := Subtype.ext (by show k⁻¹ * (k * (j : G) * k⁻¹) * k = j; group)
  map_mul' x y := Subtype.ext (by show k⁻¹ * ((x : G) * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k); group)

theorem conjBack_spec (J : Subgroup G) (k : G) (x : J.map (MulAut.conj k).toMonoidHom) :
    ((conjBack J k x : J) : G) = k⁻¹ * x * k := rfl

end Shift

section Read

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem classPresOf_ext (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    (f : (S.toCSD h).Forms) (g : G) :
    (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q g)) := by

  have key : ∀ (γ : Γ) (c : S.Cl) (k : J),
      (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (ι γ * A.y c * k))) := by
    intro γ c k
    have e1 : (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        (χ k : ℂ) • ρ γ (coef ((f : S.Cl → S.V) c)) :=
      ClassPres.ext_eq (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl) f γ c k
    have e2 : A.q (ι γ * A.y c * k) = A.gl (γ, k⁻¹) • S.outSec.rep c := by
      rw [A.q_mul, A.q_y]
    have e3 : (((S.res h).symm f : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
      have := S.resOf_apply h S.outSec ((S.res h).symm f) c
      rw [← this]
      show ((((S.res h) ((S.res h).symm f)).1 : S.Cl → S.V) c) = _
      rw [LinearEquiv.apply_symm_apply]
    have e4 := (S.mem_EqFun _).1 ((S.res h).symm f).2 (A.gl (γ, k⁻¹)) (S.outSec.rep c)
    rw [e1, e2, e4, e3, hgl, map_inv, inv_inv, Units.smul_def]
  rw [(classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).dec_spec g]
  exact key _ _ _

variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ : Γ →* Module.End ℂ W} {ρ' : Γ' →* Module.End ℂ W}
  {J' : Subgroup G'} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ} {T : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ}

theorem transport_ext (P : ClassPres ι T σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) (f : T.Forms) (g : G) :
    (P.transport eG eΓ hι hρ hJ hχ).ext (f : T.Cl → T.V) (eG g) = P.ext f g := by
  rw [P.dec_spec g]
  have hk : eG (P.decK g : G) ∈ J' := by
    rw [hJ]; exact Subgroup.mem_map_of_mem eG.toMonoidHom (P.decK g).2
  have e : eG (ι (P.decG g) * P.y (P.decC g) * (P.decK g : G)) =
      ι' (eΓ (P.decG g)) * (P.transport eG eΓ hι hρ hJ hχ).y (P.decC g) * ((⟨_, hk⟩ : J') : G') := by
    rw [map_mul, map_mul, hι]; rfl
  rw [e, ClassPres.ext_eq, ClassPres.ext_eq, hχ, hρ]
  rfl

end Read

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'}

def levE (eG : G ≃* G') (k : G) (J' : Subgroup G') (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom) :
    J.map (MulAut.conj k).toMonoidHom ≃* J' :=
  ((J.map (MulAut.conj k).toMonoidHom).equivMapOfInjective eG.toMonoidHom eG.injective).trans
    (MulEquiv.subgroupCongr hJ.symm)

theorem levE_coe (eG : G ≃* G') (k : G) (J' : Subgroup G') (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (x : J.map (MulAut.conj k).toMonoidHom) : ((levE eG k J' hJ x : J') : G') = eG x := rfl

variable (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ' : Γ' →* Module.End ℂ W) (k : G) (eG : G ≃* G') (eΓ : Γ ≃* Γ')
    (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (J' : Subgroup G') (χ' : J' →* ℂˣ)
    (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ κ : J, (κ : G) ∈ A.K1 → ∀ hx : eG (k * κ * k⁻¹) ∈ J', χ' ⟨_, hx⟩ = 1)
    (hgl : ∀ (γ : Γ) (κ : J) (v : S.V) (hx : eG (k * κ * k⁻¹) ∈ J'),
      coef (S.ρ (A.gl (γ, κ)) v) = ((χ' ⟨_, hx⟩)⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v))

end Assemble

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

theorem ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n) :
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show Formalism.L2.Col.toGLm E n (Formalism.UG.glEquiv (γ : GL (Fin n) E)) = _
  simp only [Formalism.L2.Col.toGLm, Formalism.UG.glEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftPres
