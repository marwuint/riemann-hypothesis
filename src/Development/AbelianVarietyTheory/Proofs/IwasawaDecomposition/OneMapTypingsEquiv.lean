import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.BlockTheory.RationalLaws.RationalAdjointLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstOfConstOnDictLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCovPinNotIsXiDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OfBeforeProjector

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapRefCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem evR_one {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem evR_smul {S : Type} [CommRing S] [Algebra c.F S] (a : c.F) (f : Rul Xo c) (y : FrPt Xo c S) :
    evR Xo c (a • f) y = algebraMap c.F S a * evR Xo c f y := evalAt_smul _ _ a f y

theorem trace_value {K L : Type} [Field K] [CharZero K] [Field L] [Algebra K L] [Module.Finite K L] [Algebra K ℂ] (x : L) (c0 : ℂ)
    (h : ∀ j : L →ₐ[K] ℂ, j x = c0) : ∃ u : K, algebraMap K ℂ u = c0 := by
  have h1 := trace_eq_sum_embeddings ℂ (K := K) (L := L) (x := x)
  simp only [h, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul] at h1
  have h2 : (Module.finrank K L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  exact ⟨Algebra.trace K L x / Module.finrank K L, by rw [map_div₀, h1, map_natCast]; field_simp⟩

theorem eq_const_of_complex (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (c0 : ℂ)
    (h : ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c f y) = c0) (y : FrPt Xo c (CAt σ)) :
    ∃ u : c.F, σ u = c0 ∧ f = u • 1 := by
  have hB := GlobalTheory.firstFiveLaws.1.secBaseChange
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  haveI : Nontrivial (CAt σ) := inferInstanceAs (Nontrivial ℂ)
  obtain ⟨p, φ, y₀, -⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c _ y
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (RingHom.ker φ.toRingHom) (RingHom.ker_ne_top _)
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI := Ideal.Quotient.field m
  haveI : Module.Finite c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F _
  obtain ⟨u, hu⟩ := trace_value (K := c.F) (Ideal.Quotient.mk m (f p y₀)) c0 fun j => by
    let ψ : p.R →ₐ[c.F] CAt σ := (j.comp (Ideal.Quotient.mkₐ c.F m) : p.R →ₐ[c.F] ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ ψ y₀
    exact (GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz).symm.trans (h z)
  refine ⟨u, hu, GlobalTheory.CoverPinCompare.eq_of_complex σ hf
    (Submodule.smul_mem _ u (GlobalTheory.LevelCover.one_mem_sec_zero _ _)) fun z => ?_⟩
  rw [evR_smul, evR_one, mul_one]
  exact (h z).trans hu.symm

variable {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

end Cover

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)

set_option maxHeartbeats 1000000 in

theorem cover_const (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0)
    (hP : O.Pins κ v₀ (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    ∃ u : O.c'.F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ (O.dδ ()).cδ = (O.dδ ()).eF u • 1 := by
  have hj := GlobalTheory.LevelEquivCompare.inR i
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := (GlobalTheory.Member.exists_iotaOK D T.Q hT.pins _ hj).2
    omega
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj O.s0 rfl (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc⟩, H⟩ := hP.cxi
  obtain ⟨hU, hW, g, e, F, ik, φ, th, hth, hdl, hval⟩ := H ()
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨γ, h1, h2, h3, -⟩ := hdl.2 h
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 (γ * h)
    rw [hval h γ ⟨h1, h2, h3⟩, (hP.tuple ()).xi _ x hx,
      GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x, Circle.coe_one, mul_one]
  have hs := (hP.cov ()).1.2.2.2.2.2.2.2.1
  have hd : (O.dict₂ () 1).2 ∈ ((O.U₂ ()).X (O.dict₂ () 1).1).dom := by
    by_contra hd
    have h0 : c0 = 0 := (hv 1).symm.trans (dif_neg hd)
    rw [h0, zero_pow hm.ne'] at hc
    exact zero_ne_one hc
  obtain ⟨u, hu, hf⟩ := eq_const_of_complex _ hs c0 (GlobalTheory.Member.const_of_const_on_dictLat D _ _ _ _ _ _ _ _ _ (O.U₂ ()) (O.dict₂ ()) _ g e F ik φ th _
    hio hpos (hP.cov ()).2.1 rfl hx₀ hU hW hth hdl _ hs c0 hv) ((O.U₂ ()).un _ ⟨_, hd⟩)
  refine ⟨(O.dδ ()).eF.symm u, ⟨m, hm, (inC O.c').injective ?_⟩, by rw [AlgEquiv.apply_symm_apply]; exact hf⟩
  rw [map_pow, map_one]
  exact (congrArg (· ^ m) hu).trans hc

variable (cc : Cmp T i O.hle → ℂ)

variable (h : O.Cl' () → GA D (Vc D i))

end Clauses

section Back

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F) (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i) (jL : D.what₂.LL →+* c'.F)
  (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
  (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
  (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
  (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
  (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F) (v₀ : (R.MW i (sg0 D A)).Vec)

structure Extra : Type 1 where
  bad : ℕ
  Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)
  B : Ideal (𝓞 D.host.E) → c'.F
  epF : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F
  φ : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F
  hw : VsV D i c'.F
  U₂ : Unf dδ.Xo₂ dδ.c₂ ((inC c').comp (dδ.eF.symm : dδ.c₂.F →+* c'.F)) D.R.r
  dict₂ : GA D (Wc D i) → Σ k, Frame (U₂.X k).Ψ D.R.r

variable (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end Back

end GlobalTheory.OneMapRefCompare
