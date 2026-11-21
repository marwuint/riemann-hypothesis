import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLatMonoId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latMul latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin GlobalTheory.SeeSaw.SplitLat
open GlobalTheory.FinPlLoc (idem mem_idAt_iff mem_idOff_iff idem_mem_idAt idem_mul_self cA_idem latV_idAt)
open GlobalTheory.FinPl.LatMem (mem_latO_iff latO_mxAt)

namespace GlobalTheory.AscFinWit

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {P : GlobalTheory.FinPl.Pl D → Prop}

theorem mxAt_mul {l m n : ℕ} (A : Mx D l m) {u : Mx D m n} (hu : MxAt P u) : MxAt P (A ⬝ u) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hu k j)

theorem mxAt_mul' {l m n : ℕ} {u : Mx D l m} (hu : MxAt P u) (B : Mx D m n) : MxAt P (u ⬝ B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem mxAt_iff {m n : ℕ} {u : Mx D m n} : MxAt P u ↔ idem D P • u = u :=
  ⟨fun h => Matrix.ext fun i j => (mem_idAt_iff P _).1 (h i j), fun h i j => (mem_idAt_iff P _).2 (congrFun (congrFun h i) j)⟩

theorem mxAt_idem {m n : ℕ} (u : Mx D m n) : MxAt P (idem D P • u) := fun _ _ => Ideal.mul_mem_right _ _ (idem_mem_idAt P)

theorem finLat_of {m n : ℕ} {A : AddSubgroup (Mx D m n)} (fin : ∀ a ∈ A, MxAt (fun _ => True) a)
    (opn : ∃ U : Set (Mx D m n), IsOpen U ∧ (0 : Mx D m n) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ A)
    {C : Set (Mx D m n)} (hC : IsCompact C) (h : ∀ a ∈ A, a ∈ C) : FinLat A := by
  refine ⟨fin, hC.of_isClosed_subset ?_ h, opn⟩
  obtain ⟨i1, -, -, i4, -⟩ := lattice_Mx D m n
  obtain ⟨U, h1, h2, h3⟩ := opn
  let e : Mx D m n →+ Mx D m n := DistribMulAction.toAddMonoidHom _ (idem D fun _ => True)
  have he : Continuous e := continuous_id.const_smul (idem D fun _ => True)
  have ho : IsOpen (A.comap e : Set (Mx D m n)) := (A.comap e).isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((h1.preimage he).mem_nhds (by rwa [Set.mem_preimage, map_zero])) fun a ha => h3 _ ha (mxAt_idem a))
  convert ((A.comap e).isClosed_of_isOpen ho).inter (isClosed_eq he continuous_id) using 1
  ext a
  refine ⟨fun ha => ⟨?_, mxAt_iff.1 (fin a ha)⟩, fun ⟨ha, hb⟩ => ?_⟩
  · show idem D (fun _ => True) • a ∈ A
    rwa [mxAt_iff.1 (fin a ha)]
  · exact (show e a = a from hb) ▸ ha

theorem sec_fin {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (s2 : ∀ a, finPart D (s a) = a) (s3 : ∀ a, infPart D (s a) = 0)
    {a : AE D} (ha : a ∈ idAt D P) (c : AE D) : s (finPart D (c * a)) = c * a := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, s3, RingHom.map_mul, GlobalTheory.FinPlLoc.infPart_of_idAt ha, mul_zero, sub_zero]
  · rw [RingHom.map_sub, s2, sub_self]

theorem finLat_latO {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : Submodule.IsLattice D.host.E LS)
    (hT : Submodule.IsLattice D.host.E LT) : FinLat (latO S T (LS : Set _) (LT : Set _) fun _ => True) := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨s, s1, s2, s3⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  have inv : ∀ N : ℕ, 0 < N → incA D (N : D.host.E)⁻¹ * (N : AE D) = 1 := fun N hN => by
    rw [← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  refine finLat_of (fun a ha => latO_mxAt ha) ⟨{a | ∀ i j, finPart D (incA D (K : D.host.E)⁻¹ * a i j) ∈ intAE D}, ?_, ?_, ?_⟩
    (C := (fun z => Matrix.of fun i j => incA D (M : D.host.E)⁻¹ * s (z i j)) ''
      {z : Matrix (Fin T.rank) (Fin S.rank) _ | ∀ i j, z i j ∈ intAE D}) (IsCompact.image ?_ ?_) fun a ha => ?_
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage
      ((GlobalTheory.Member.continuous_finPart D).comp (continuous_const.mul (continuous_id.matrix_elem i j)))
  · intro i j
    rw [Matrix.zero_apply, mul_zero, map_zero]
    exact zero_mem _
  · intro a ha hb
    have := hmul (incA D (K : D.host.E)⁻¹ • a) (Matrix.ext fun i j => by
      show infPart D (_ * a i j) = 0
      rw [map_mul, GlobalTheory.FinPlLoc.infPart_of_idAt (hb i j), mul_zero]) fun i j => GlobalTheory.PlaceCoord.toEAf_mem (ha i j)
    rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, mul_comm, inv K hK, one_smul] at this
  · exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  · exact continuous_pi fun i => continuous_pi fun j => continuous_const.mul (s1.comp (continuous_id.matrix_elem i j))
  · refine ⟨Matrix.of fun i j => finPart D ((M : AE D) * a i j), fun i j => GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_,
      Matrix.ext fun i j => ?_⟩
    · rw [RingHom.map_mul, map_natCast]
      exact hden a ha i j
    · exact (congrArg (incA D (M : D.host.E)⁻¹ * ·) (sec_fin s2 s3 (latO_mxAt ha i j) _)).trans
        (by rw [← mul_assoc, inv M hM, one_mul])

section Maps

variable {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}

theorem latMul_map (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {𝔞 𝔞' : Set D.host.E}
    (h : ∀ a ∈ 𝔞, ∀ x ∈ LS, ∃ a' ∈ 𝔞', ∃ x' ∈ LT, M *ᵥ (a • x) = a' • x') {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 LS P) :
    rat M *ᵥ y ∈ latMul T 𝔞' LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    obtain ⟨a', ha', x', hx', e⟩ := h a ha x hx
    have := rat_mulVec_gen M (pairA D.host.F 0 β) (a • x)
    simp only [e, one_mul, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, a', ha', x', hx', rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latO_right (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S' LS') (hT : IsSelfDualC T LT)
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hM : ∀ x ∈ LS', M *ᵥ x ∈ LS) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) : u ⬝ rat M ∈ latO S' T (LS' : Set _) (LT : Set _) P := by
  rw [mem_latO_iff D _ _ _ _ hS hT] at hu
  refine (mem_latO_iff D _ _ _ _ hS' hT P _).2 ⟨mxAt_mul' hu.1 _, fun y hy => ?_⟩
  show (u ⬝ rat M) *ᵥ y ∈ _
  rw [← mulVec_mulVec]
  exact hu.2 _ (rat_mulVec_mem_latV M hM P hy)

theorem rat_mem_latO (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hM : ∀ x ∈ LS, M *ᵥ x ∈ LT) {α : D.host.E} (hα : α ∈ D.host.AA) :
    idem D P • rat (α • M) ∈ latO S T (LS : Set _) (LT : Set _) P := by
  refine (mem_latO_iff D _ _ _ _ hS hT P _).2 ⟨mxAt_idem _, fun y hy => ?_⟩
  show (idem D P • rat (α • M)) *ᵥ y ∈ _
  rw [smul_mulVec, ← mulVec_smul, show idem D P • y = y from funext fun i => (mem_idAt_iff P _).1 (latV_idAt hy i)]
  refine latMul_map _ (fun a ha x hx => ⟨α, hα, _, hM x hx, ?_⟩) hy
  rw [Set.mem_singleton_iff.1 ha, one_smul, smul_mulVec]

theorem idem_mem_latO {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    idem D P • u ∈ latO S T (LS : Set _) (LT : Set _) P := by
  have h := GlobalTheory.SelfDualAt.smul_mem_latO S T _ _ P u hu
  rwa [← algebraMap_smul (AE D)] at h

theorem mem_latO_at {u : WO S T} (h : MxAt P u) : u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
    u ∈ latO S T (LS : Set _) (LT : Set _) P :=
  ⟨fun hu => mxAt_iff.1 h ▸ idem_mem_latO hu, fun hu => GlobalTheory.PlaceModel.latO_le_top _ hu⟩

theorem psi_eq_one (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {x u : WO S T}
    (hx : idem D P • x ∈ latO S T (LS : Set _) (LT : Set _) P) (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) :
    ψ (symplO S T x u) = 1 := by
  have h := (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P _ (mxAt_idem x)).1 hx u hu
  have e := GlobalTheory.SelfDualAt.symplO_smul_swap S T (GlobalTheory.SelfDualAt.cP P) x u
  rw [← algebraMap_smul (AE D), ← algebraMap_smul (AE D) _ x] at e
  exact (congrArg ψ ((congrArg (symplO S T x) (mxAt_iff.1 (latO_mxAt hu)).symm).trans e)).trans h

theorem psi_swap (x u : WO S T) : ψ (symplO S T x u) = 1 ↔ ψ (symplO S T u x) = 1 := by
  rw [GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv, inv_eq_one]

end Maps

section Sympl

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

theorem symplO_extX (a : Mx D T.rank ρ) (u : WO S T) : symplO S T (d.extX T a) u = symplO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  simp only [symplO_eq, d.hO_coordS, HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, d.pX_jX, d.pX_j0, d.pX_jY, d.pY_jX,
    d.pY_j0, d.pY_jY, Matrix.mul_zero, Matrix.mul_one, hO_eq_trace S₀, pairS, trace_zero]

theorem symplO_incX (a : Mx D ρ T.rank) (u : WO T S) : symplO T S (d.incX T a) u = symplO T S (d.incX T a) (d.incY T (d.pY ⬝ u)) := by
  simp only [symplO_eq, d.hO_coordT, HypDec.incX_apply, HypDec.incY_apply, cancel₂ d.pX_jX, cancel₂ d.p0_jX, cancel₂ d.pX_jY,
    cancel₂ d.pY_jX, cancel₂ d.p0_jY, cancel₂ d.pY_jY, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, hO_eq_trace T S₀, pairT, trace_zero]

theorem symplO_incY (a : Mx D ρ T.rank) (u : WO T S) : symplO T S (d.incY T a) u = symplO T S (d.incY T a) (d.incX T (d.pX ⬝ u)) := by
  simp only [symplO_eq, d.hO_coordT, HypDec.incX_apply, HypDec.incY_apply, cancel₂ d.pX_jX, cancel₂ d.p0_jX, cancel₂ d.pX_jY,
    cancel₂ d.pY_jX, cancel₂ d.p0_jY, cancel₂ d.pY_jY, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, hO_eq_trace T S₀, pairT, trace_zero]

end Sympl

section Pcs

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (LV₀ : Lat V₀) (LW₀ : Lat W₀)
  (𝔟 𝔠 : ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

abbrev homL (P : GlobalTheory.FinPl.Pl D → Prop) : AddSubgroup (WO V W) :=
  latO V W (splitL dV LV₀ 𝔟 : Set _) (splitL dW LW₀ 𝔠 : Set _) P

variable {dV dW LV₀ LW₀ 𝔟 𝔠} (hψ : IsStdChar D ψ (-1)) (hV : IsSelfDualC V (splitL dV LV₀ 𝔟)) (hV₀ : IsSelfDualC V₀ LV₀)
  (hW : IsSelfDualC W (splitL dW LW₀ 𝔠)) (hW₀ : IsSelfDualC W₀ LW₀) {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ}

include hψ hV hW

include hV₀ hW₀

variable (hx : idem D (fun _ => True) • dV.extX W x ∈ homL dV dW LV₀ LW₀ 𝔟 𝔠 fun _ => True)
  (hy : idem D (fun _ => True) • dW.incAdj V₀ y ∈ latO V₀ W (LV₀ : Set _) (splitL dW LW₀ 𝔠 : Set _) fun _ => True)

include hx hy

end Pcs

end GlobalTheory.AscFinWit

end
