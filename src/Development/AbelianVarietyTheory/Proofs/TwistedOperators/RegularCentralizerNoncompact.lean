import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.ArchVanish

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def archKerEquiv (w : InfinitePlace F) : GArch σ J w × (projArch σ J w).ker ≃ₜ* GAd σ J where
  toFun p := embArch σ J w p.1 * p.2
  invFun x := (projArch σ J w x, ⟨(embArch σ J w (projArch σ J w x))⁻¹ * x, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, projArch_embArch_self, inv_mul_cancel]⟩)
  left_inv p := by
    obtain ⟨a, z, hz⟩ := p
    have hz' : projArch σ J w z = 1 := hz
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [hz']
    · simp [hz']
  right_inv x := by simp
  map_mul' p q := by
    obtain ⟨a, z, hz⟩ := p
    obtain ⟨a', z', hz'⟩ := q
    have hc := (commute_embArch σ J a' (g := z) hz).eq
    simp only [Prod.mk_mul_mk, Subgroup.coe_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (embArch σ J w a'), hc, mul_assoc]
  continuous_toFun := ((continuous_embArch σ J w).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    refine (continuous_projArch σ J w).prodMk (Continuous.subtype_mk ?_ _)
    exact ((continuous_embArch σ J w).comp (continuous_projArch σ J w)).inv.mul continuous_id

theorem archKerEquiv_apply (w : InfinitePlace F) (p : GArch σ J w × (projArch σ J w).ker) :
    archKerEquiv σ J w p = embArch σ J w p.1 * p.2 := rfl

variable {σ J}

theorem isMulCommutative_cent_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsMulCommutative (Orb.cent (projArch σ J w (ratEmb σ J γ))) :=
  Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)

end General

end GlobalTheory.ArchVanish

end

namespace GlobalTheory.ArchVanish

end GlobalTheory.ArchVanish
