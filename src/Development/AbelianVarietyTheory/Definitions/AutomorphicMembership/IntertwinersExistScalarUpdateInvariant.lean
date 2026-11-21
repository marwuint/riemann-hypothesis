import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

open GlobalTheory.Mem.R3.Res

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

theorem baseWeight_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {F : Face D A} (h : R.BaseW F) (k l) :
    (R.upd6 k l).BaseW F :=
  ⟨h.lev, ⟨h.grp.red_R, h.grp.red_L, h.grp.levels, h.grp.record, h.grp.chiW⟩,
    ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩,
    ⟨h.models.inf, h.models.vpos, h.models.cX, h.models.cV, h.models.prX, h.models.HX, h.models.HV, h.models.HE, h.models.HW,
      h.models.gE, h.models.gW, h.models.jX, h.models.jV, h.models.νY, h.models.νY', h.models.ν0, h.models.νX, h.models.νV,
      h.models.νW, h.models.BV, h.models.order⟩, RealDat.weak_chain_of_scalar_update h.chain k l, RealDat.weak_theta_props_of_scalar_update h.thP k l⟩

set_option maxHeartbeats 2000000 in

theorem intertwinersExist_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} (e : R.ExAt) (k l) : (R.upd6 k l).ExAt :=
  ⟨e.ItY, e.ItX, e.ioY, e.ioX, e.Th, e.ioP, e.thF, e.thG⟩

set_option maxHeartbeats 2000000 in

theorem nz_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (k l) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (∃ j, NzAt (R.updS k l) F F0 j w ∨ NzAt (R.updS k l) F F0 j (Formalism.DivisionValues.conjPl w)) ↔
      ∃ j, NzAt R F F0 j w ∨ NzAt R F F0 j (Formalism.DivisionValues.conjPl w) :=
  (complexSide_nonzeroIndexPlaces_iff_self (R.updS k l) F { R.num F 0 0 with F0 := F0 } w).symm.trans
    (complexSide_nonzeroIndexPlaces_iff R F k l R.err0 F.Dc F.Sp F.Zsc { R.num F 0 0 with F0 := F0 } w)

open Classical in

def kapOf (S : RealDat3 D A3 Ks) : ℝ :=
  if h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 then h.choose else S.kap

theorem kapOf_eq (S : RealDat3 D A3 Ks) (κ : ℝ)
    (hκ : Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ)
    (hn : ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0) : kapOf S = κ := by
  have h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 := ⟨κ, hκ, hn⟩
  obtain ⟨t, p, hp, hl⟩ := hn
  unfold kapOf
  rw [dif_pos h]
  exact Lift.IsKap.unique h.choose_spec.1 hκ t p hp hl

set_option maxHeartbeats 2000000 in

theorem isScal_kapOf (S : RealDat3 D A3 Ks) (F : Face3 D A3) (h0 : S.eigenvalue_at_base_of_scalar) (h1 : S.scal_off F) (h2 : S.zero_part_eigenvalue_convention F)
    (h3 : S.scal_abs F) (h4 : S.scal_tup) : (S.updS (kapOf S) S.lam3).IsScal F := by
  refine ⟨h0, fun κ h h' => kapOf_eq S κ h h', fun i p v l hv hp he => ?_, fun i t p hp => ?_, fun i p v hv hp => ?_, h4⟩
  · exact h1 i p v l hv ((RealDat3.partAt_updS _ _ _ _ _).1 hp) ((RealDat3.sim_updS _ _ _ _ _ _).1 he)
  · rw [RealDat3.zs_updS]
    exact h2 i t p hp
  · rw [RealDat3.zs_updS]
    exact h3 i p v hv fun hl => hp ((RealDat3.partAt_updS _ _ _ _ _).2 hl)

variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 4000000 in

theorem pins_updS (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) (k l) (hs : ((dat3 f μ R mu tw).updS k l).IsScal (bare3 _ P0 ψ0 P1 ψ1)) :
    Pins ((dat3 f μ R mu tw).updS k l) (bare3 _ P0 ψ0 P1 ψ1) cG := by
  have i := isInert mu tw h.char.inert
  have u := isTup hf h.char.tup n
  have kv := keep mu tw h.keep
  exact ⟨⟨baseWeight_scalar_update_invariant (baseW (A := A3.A) mu tw hf h.char.base e) k _, ⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩,
      fun t => h.char.fullY (f t), fun t => h.char.fullX (f t), fun i t => h.char.fullP i (f t), hs,
      ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, h.char.phase, h.char.allPl⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩, h.phs, h.trSem⟩

set_option maxHeartbeats 4000000 in

theorem pins_kapOf (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) :
    Pins ((dat3 f μ R mu tw).updS (kapOf (dat3 f μ R mu tw)) (dat3 f μ R mu tw).lam3) (bare3 _ P0 ψ0 P1 ψ1) cG :=
  pins_updS hf h e n _ _ (isScal_kapOf _ _ (fun i t => h.char.scal.lam0 i (f t)) h.char.scal.off
    (fun i t => h.char.scal.abs0 i (f t)) h.char.scal.abs fun i t => h.char.scal.tup i (f t))

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl}

set_option maxHeartbeats 4000000 in

theorem exAt_res (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (e : z.R.toRealDat.ExAt) : (z.resR h).toRealDat.ExAt :=
  Res.exAt (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') e

set_option maxHeartbeats 4000000 in

theorem pins_resK (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) :
    Pins ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact pins_kapOf (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I)
    (mu := z.resMu h) (tw := z.resTw Wt') (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e (z.newTup h hc)

set_option maxHeartbeats 4000000 in

def restrictEx (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := (z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3
  cG := z.cG
  geo := (GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ _ z.core (z.resR h).toRealDat (fun _ => 1) (kapOf (z.resR h)) (z.resR h).lam
    (z.resR h).err0 (z.resGeo h)).choose
  pins := pins_resK z h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')

theorem restrictEx_core : (restrictEx z e Wt' h hc).core = z.core := rfl

end Record

end GlobalTheory.Mem.R3.ResEx

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' Wt'' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

set_option maxHeartbeats 400000 in

theorem realData_restrict_id {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {μ : T0}
    (R : RealDat3 D (A3.comap id (id μ)) Ks) : Res.dat3 id μ R R.mu R.twPl = R := rfl

end GlobalTheory.Mem.R3.ResTest

end
