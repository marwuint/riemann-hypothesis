import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.InertIwasawaLoc

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.LFun GlobalTheory.InertIwasawaIso

theorem exists_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {c : 𝓞 E} (hc : (c : E) + σ c = 1) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) (hL : IsSelfDualAt σ J L v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) (he : Formalism.UG.cT (σ : E →+* E) e * J * e = 0) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ y = q * k ∧ ∃ β : GL (Fin r) (Fv F v ⊗[F] E),
      (HA.mat (Fv F v) σ J q).1 * e.map (inclR (Fv F v)) = e.map (inclR (Fv F v)) * β.1 := by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hN := GlobalTheory.UnramSelfDual.exists_norm v hσ (GlobalTheory.UnramConjUnit.exists_sub_conj_unit _ _ _ hσ v hv)
  have hO : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v ↔ z ∈ intLoc F E v := GlobalTheory.StabOrbit.mem_OEv_iff v
  simp only [hO] at hN
  let ι : E →+* Fv F v ⊗[F] E := inclR (Fv F v)
  obtain ⟨k, h1, h2, h3⟩ := exists_stab (intLoc F E v) (w.adicCompletionIntegers E)
    (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h)
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hσ))
    (τ := ι c) (tmul_mem_intLoc (one_mem _) c)
    (by change ι c + ι (σ c) = 1
        rw [← map_add, hc, map_one]) hN
    (J := JR (Fv F v) J) (by ext i j; exact congrArg ι (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (X := e.map ι) (P := p.map ι)
    (by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ ι (fun _ => rfl), show JR (Fv F v) J = J.map ι from rfl,
          ← Matrix.map_mul, ← Matrix.map_mul, he, Matrix.map_zero _ (map_zero _)])
    (g := matHom _ σ J y) y.2
  let κ : GLoc σ J v := ⟨k, h1⟩
  exact ⟨y * κ⁻¹, κ, h2, (inv_mul_cancel_right y κ).symm, h3⟩

end GlobalTheory.InertIwasawaLoc

namespace GlobalTheory.InertIwasawaLoc

end GlobalTheory.InertIwasawaLoc

end
