import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt]
  rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isMov_hLat (V : HSp D) (hL : Bridge.hLat V 1 = stdL D.host.E V.rank) (g : GA D V) :
    IsMov (fmt V g) (stdL D.host.E V.rank) (Bridge.hLat V (fin V g)) := by
  have hs : Submodule.span D.host.E (stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (Pi.basisFun_apply _ _ i).symm⟩
  obtain ⟨⟨L, hL', hm⟩, h2⟩ := (isMov_laws D V.rank _ ⟨Submodule.fg_span (Set.finite_range _), hs⟩).2.2.2 _ _
    (fmt_mul_inv V g)
  have h3 := (isMov_laws D V.rank L hL').1
  have h4 : fmt V g⁻¹ * fmt V g = 1 := mul_eq_one_comm.1 (fmt_mul_inv V g)
  have key : Bridge.hLat V (fin V g) = L := by
    rw [Bridge.hLat, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, ← Submodule.span_eq L]
    congr 1
    ext x
    change fmt V g⁻¹ *ᵥ toAf x ∈ hatV (stdL D.host.E V.rank) ↔ x ∈ L
    rw [← h3, hm]
    constructor
    · intro hx
      exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, fmt_mul_inv, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, e⟩
      rwa [e, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rwa [key]

noncomputable abbrev cf (D : D7) : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

theorem conj_mem_hatV {k : ℕ} {L L' : Lt D.host.E k} (h : ∀ v ∈ L, (fun j => cc (v j)) ∈ L') {u : Fin k → AfE D}
    (hu : u ∈ hatV L) : cf D ∘ u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h x hx, rfl⟩
  | zero => convert (hatV L').zero_mem; funext i; exact RingHom.map_zero _
  | add a b _ _ ha hb => convert add_mem ha hb; funext i; exact RingHom.map_add _ _ _
  | neg a _ ha => convert neg_mem ha; funext i; exact RingHom.map_neg _ _

theorem isMov_conj {V : HSp D} {g : GA D V} {L L' : Lt D.host.E V.rank} (h : IsMov (fmt V g) (stdL D.host.E V.rank) L)
    (hc : ∀ v, v ∈ L' ↔ (fun j => cc (v j)) ∈ L) : IsMov (fmtC V g) (stdL D.host.E V.rank) L' := by
  have c4 : fmtC V g = (fmt V g).map (cf D) := by ext i j; exact finPart_cA _
  have c5 : ∀ v ∈ stdL D.host.E V.rank, (fun j => cc (v j)) ∈ stdL D.host.E V.rank := fun v hv => by
    rw [← GenLatCmp.std_eq, GenLatCmp.mem_std] at hv ⊢
    exact fun i => Base.isIntegral_cc (hv i)
  have c6 (u : Fin V.rank → AfE D) : cf D ∘ cf D ∘ u = u := funext fun i => cf_cf _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (cf D ∘ u) = cf D ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec (cf D) _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (conj_mem_hatV (fun v hv => (hc v).1 hv) hu)
    exact ⟨_, conj_mem_hatV c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    refine conj_mem_hatV (fun v hv => (hc _).2 ?_) ((h _).2 ⟨_, conj_mem_hatV c5 h0, rfl⟩)
    simpa [cc] using hv

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

end GlobalTheory.OneMapRef.ClassScalar
