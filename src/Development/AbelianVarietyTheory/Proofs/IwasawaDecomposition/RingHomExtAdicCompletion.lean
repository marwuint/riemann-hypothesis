import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetAutSelfNaut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RowPar

section Sat
open Formalism.UG GlobalTheory.SatInd

theorem satAtS_indep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv Dv' : InertDatum L n v w) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv α) : NG.SatAtS S Dv' α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
  have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
    hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
    _root_.GlobalTheory.SatInd.satU_guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
      (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
        Dv.unram Dv'.unram hm)]

end Sat

section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands

theorem ringHom_ext_adicCompletion {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {R : Type} [Ring R]
    [TopologicalSpace R] [T2Space R] (f g : v.adicCompletion K →+* R) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y : K, f (algebraMap K _ y) = g (algebraMap K _ y)) : f = g :=
  DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer hf hg (funext h))

theorem splitEmb_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (si si' : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (i i' : v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L) (hi : Continuous i) (hi' : Continuous i')
    (hix : ∀ x, i (si x) = algebraMap L _ x) (hix' : ∀ x, i' (si' x) = algebraMap L _ x) : si' = si ∧ i' = i := by
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i := by
    refine ringHom_ext_adicCompletion v _ _ hi' hi fun y => ?_
    have h1 := hix (algebraMap _ L y)
    have h2 := hix' (algebraMap _ L y)
    rw [AlgHom.commutes] at h1 h2
    exact h2.trans h1.symm
  have e' : i' = i := RingEquiv.ext fun x => congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  refine ⟨AlgHom.ext fun x => i.injective ?_, e'⟩
  rw [hix, ← hix' x, e']

theorem splitPlace_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (S S' : Submodule ℂ (GAf L n → W)) (s s' : SplitPlace L) (h : s'.w = s.w)
    (τ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (τ' : IrrRep (GL (Fin n) (s'.w.adicCompletion L)))
    (hτ : IsLocS S s τ) (hτ' : IsLocS S' s' τ') : s' = s := by
  obtain ⟨i, -, hi, hix, -⟩ := hτ
  obtain ⟨i', -, hi', hix', -⟩ := hτ'
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : s'.w = w)
      (j : s'.v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L), Continuous j →
      (∀ x, j (s'.i x) = algebraMap L _ x) → s' = s := by
    intro w hw j hj hjx
    rw [h] at hw
    subst hw
    obtain ⟨v, si⟩ := s
    obtain ⟨v', si'⟩ := s'
    dsimp only at hv
    subst hv
    obtain rfl := (splitEmb_eq _ _ si si' i j hi hj hix hjx).1
    rfl
  exact key _ rfl i' hi' hix'

theorem cl_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n) (s : SplitPlace L)
    (τ τ' : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) (hτ' : IsLocS π.S s τ') : τ.cl = τ'.cl := by
  obtain ⟨i, T, hi, hix, hTi, hTS, hTe⟩ := hτ
  obtain ⟨i', T', hi', hix', hTi', hTS', hTe'⟩ := hτ'
  obtain rfl := (splitEmb_eq s.v s.w s.i s.i i' i hi' hi hix' hix).2
  obtain ⟨hdec, hcom, huniq⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose sec hsec using fun A => (huniq A).exists
  have sec_eq : ∀ x : GAf L n, TrivOutside {s.v} x → sec (s.loc n x) = x := fun x hx =>
    (huniq _).unique (hsec _) ⟨hx, rfl⟩
  have triv_mul : ∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    have h1 := hx v hv
    have h2 := hy v hv
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.map_mul, h1, h2, one_mul]
  have triv_one : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    simp [Matrix.map_one]
  let sH : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := sec
      map_one' := (huniq 1).unique (hsec 1) ⟨triv_one, map_one _⟩
      map_mul' := fun A B => (huniq (A * B)).unique (hsec (A * B))
        ⟨triv_mul _ _ (hsec A).1 (hsec B).1, by rw [map_mul, (hsec A).2, (hsec B).2]⟩ }
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt])
      map_mul' := fun g h => LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt, mul_assoc]) }
  have hρ : ρ.IsIrreducible := by
    refine (GlobalTheory.CuspRep.isIrreducible_iff ρ).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne, fun U hU => ?_⟩
    have hst : ∀ h, ∀ f ∈ U.map π.S.subtype, NG.rt L n h f ∈ U.map π.S.subtype := by
      rintro h _ ⟨u, hu, rfl⟩
      exact ⟨ρ h u, hU h u hu, rfl⟩
    rcases π.irr _ (Submodule.map_subtype_le _ _) hst with h0 | h1
    · left
      exact Submodule.map_injective_of_injective π.S.injective_subtype (h0.trans (Submodule.map_bot _).symm)
    · right
      refine Submodule.map_injective_of_injective π.S.injective_subtype ?_
      rw [h1, Submodule.map_subtype_top]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have he : Function.Surjective e := fun B =>
    ⟨Matrix.GeneralLinearGroup.map i.symm.toRingHom B, Units.ext (Matrix.ext fun a b => by simp [e])⟩
  have hnt : ∀ τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L)), Nontrivial τ₀.V := fun τ₀ =>
    ((GlobalTheory.CuspRep.isIrreducible_iff τ₀.ρ).1 τ₀.irr).1
  have key : ∀ (τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (T₀ : τ₀.V →ₗ[ℂ] (GAf L n → ℂ)),
      Function.Injective T₀ → (∀ a, T₀ a ∈ π.S) →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
        T₀ (τ₀.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T₀ a)) →
      ∃ f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH), f ≠ 0 := by
    intro τ₀ T₀ hT₀ hS₀ he₀
    refine ⟨⟨LinearMap.codRestrict π.S T₀ hS₀, fun A => LinearMap.ext fun a => Subtype.ext ?_⟩, fun h0 => ?_⟩
    · have h1 := he₀ (sec A) (hsec A).1 a
      rw [(hsec A).2] at h1
      exact h1
    · haveI := hnt τ₀
      obtain ⟨a, ha⟩ := exists_ne (0 : τ₀.V)
      refine ha (hT₀ ?_)
      have h2 := congrArg (fun f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH) => (f a : GAf L n → ℂ)) h0
      simpa using h2
  obtain ⟨f, hf⟩ := @key τ T hTi hTS hTe
  obtain ⟨f', hf'⟩ := key τ' T' hTi' hTS' hTe'
  have hcomm : ∀ g, ∃ u, ∀ y, Commute ((sH u)⁻¹ * g) (sH y) := by
    intro g
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec g
    refine ⟨s.loc n x, fun B => ?_⟩
    rw [show sH (s.loc n x) = x from sec_eq x hx, inv_mul_cancel_left]
    exact (hcom _ _ (hsec B).1 hy).symm
  obtain ⟨φ⟩ := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ ρ sH (τ.ρ.comp e) (τ'.ρ.comp e) hρ
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr e he) (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ'.irr e he)
    hcomm f hf).2 f' hf'
  refine IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk φ.toLinearEquiv fun B => ?_⟩
  obtain ⟨A, rfl⟩ := he B
  exact φ.isIntertwining' A

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)

def LocAt (σ : D.what₂.FT) (w : PlE D.host) : Type 1 :=
  {p : (s : SplitPlace D.host.E) × IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) //
    p.1.w = w ∧ IsLocS (rep σ).S p.1 p.2}

def unrW : RowWD D :=
  RowWD.unram D (fun _ _ => Multiset.replicate D.R.r 1) (fun _ _ h => by simpa using (Multiset.eq_of_mem_replicate h))
    (fun _ _ => by simp)

end Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

def satOf (S : Submodule ℂ (GAf L n → W)) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ := by
  classical
  exact if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α then Finset.univ.val.map h.choose_spec.choose_spec.choose else 0

theorem satAtS_transfer (S : Submodule ℂ (GAf L n → W)) {w : HeightOneSpectrum (𝓞 L)}
    (v0 v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv0 : InertDatum L n v0 w) (Dv : InertDatum L n v w)
    (hv : v0 = v) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv0 α) : NG.SatAtS S Dv α := by
  subst hv
  exact satAtS_indep S Dv0 Dv α hs

theorem satOf_spec (S : Submodule ℂ (GAf L n → W)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hO : NG.OverPl w v) (Dv : InertDatum L n v w) (hα : ∃ α, NG.SatAtS S Dv α) :
    ∃ α, NG.SatAtS S Dv α ∧ satOf S w = Finset.univ.val.map α := by
  classical
  obtain ⟨α, hα⟩ := hα
  have h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α := ⟨v, Dv, α, hO, hα⟩
  have hsp := h.choose_spec.choose_spec.choose_spec
  refine ⟨h.choose_spec.choose_spec.choose, satAtS_transfer S _ v _ Dv
    (HeightOneSpectrum.ext (hsp.1.symm.trans hO)) _ hsp.2, ?_⟩
  unfold satOf
  rw [dif_pos h]

end GlobalTheory.RowPar
