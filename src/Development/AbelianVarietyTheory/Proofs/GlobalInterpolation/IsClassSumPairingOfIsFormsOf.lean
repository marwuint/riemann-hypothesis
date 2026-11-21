import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum GlobalTheory.Mem.Col2
open scoped Matrix ComplexOrder

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem Lsh_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet E n ∅ SG) : d.1.Lsh = d.1.N := by
  have e : d.1.L = d.1.N := by
    rw [Deco.L]
    simp
  rw [Deco.Lsh, e]
  exact d.2.uni

theorem emb_mem_cmMax (hX : X.Ok) (τ : X.Tau) (x : X.E) : X.emb τ x ∈ cmMax X.K := fun φ => by
  rw [← hX.emb_star]
  exact hX.conjE (φ.comp (X.emb τ)) x

theorem root_mem_cmMax (hX : X.Ok) {c : X.K} (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1) : c ∈ cmMax X.K := fun φ => by
  obtain ⟨m, hm, hc⟩ := hc
  have h1 := star_mul_root hX.conjK hm hc
  have h2 : star (φ c) * φ c = 1 := by
    have h3 : ‖φ c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hc, map_one]) hm.ne'
    rw [← starRingEnd_apply, Complex.conj_mul', h3]
    simp
  have h0 : φ c ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine mul_right_cancel₀ h0 ?_
  rw [← map_mul, h1, map_one, starRingEnd_apply, h2]

theorem row_act_rat (hX : X.Ok) (g : (mtildeGSD W Ch sel mu P).G) (i j) :
    (mtildeGSD W Ch sel mu P).bV.repr ((mtildeGSD W Ch sel mu P).ρ g ((mtildeGSD W Ch sel mu P).bV j)) i ∈ cmMax X.K := by
  rw [formGSD_rho, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (root_mem_cmMax hX (LevFam.chr_root _ _))
    (coefAction_repr_mem_subfield X.emb _ W.sgTrue (emb_mem_cmMax hX) _ i j).1

theorem isFormsOf_MtildeH (hX : X.Ok) : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)
    (MtildeH W Ch hX sel mu P) (LinearEquiv.refl _ _) :=
  isFormsOf_toH _ _ (row_act_rat W Ch sel mu P hX) (fun v => by rw [row_gramV]; exact gramB_posDef _ _) _

def rowPt (c : (stepX Ch sel mu P).Cl) : RowPt Pr R sel mu := toRow sel mu ((stepX Ch sel mu P).rep c).1.1

def rowCl (c : (stepX Ch sel mu P).Cl) : (mtildeGSD W Ch sel mu P).Cl := (mtildeGSD W Ch sel mu P).cls (rowPt Ch sel mu P c)

theorem rowCl_surjective : Function.Surjective (rowCl W Ch sel mu P) := by
  rintro ⟨d⟩
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  refine ⟨(stepX Ch sel mu P).cl () (trivPt X _ _ _ _ p), ?_⟩
  obtain ⟨g, hg⟩ := (stepX Ch sel mu P).exists_mv () (trivPt X _ _ _ _ p)
  have h1 := congrArg (fun q => toRow sel mu q.1.1) hg
  refine Eq.symm (((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).2 ⟨toRowG Ch sel mu P g, ?_⟩)
  exact (toRow_smul Ch sel mu P g _).symm.trans h1

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

include hd in

theorem exists_step_smul (a : FormG (rowTy Ch sel mu P).inv) (p q : (stepX Ch sel mu P).D ())
    (h : a • toRow sel mu p.1.1 = toRow sel mu q.1.1) :
    ∃ g : (stepX Ch sel mu P).G (), toRowG Ch sel mu P g = a ∧ (letI := (stepX Ch sel mu P).actD (); g • p) = q := by
  obtain ⟨g, h1, h2⟩ := exists_toRowG_smul Ch sel mu P hd a _ _ h
  refine ⟨g, h1, (trivPt X _ _ _ _).symm.injective h2⟩

include hd in
theorem rowCl_injective : Function.Injective (rowCl W Ch sel mu P) := by
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  obtain ⟨a, ha⟩ := ((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).1 h
  obtain ⟨g, -, hg⟩ := exists_step_smul Ch sel mu P hd a _ _ ha
  refine congrArg (Sigma.mk ()) ?_
  rw [← (stepX Ch sel mu P).rp_spec () c, ← (stepX Ch sel mu P).rp_spec () c']
  exact Quotient.sound ⟨g, hg⟩

def clEquiv : (stepX Ch sel mu P).Cl ≃ (mtildeGSD W Ch sel mu P).Cl :=
  Equiv.ofBijective _ ⟨rowCl_injective W Ch sel mu P hd, rowCl_surjective W Ch sel mu P⟩

theorem clInv_cls {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (C C' : CoefPk X n (DecoSet X.E n ST SG))
    (Λ : LevFam X.E X.K n SG) (d : DecoSet X.E n ST SG) :
    clInv C C' Λ ((formGSD C' Λ.inv).cls d) = (formGSD C Λ).cls d := rfl

include hd in

theorem card_stab (c : (stepX Ch sel mu P).Cl) : Nat.card ((stepX Ch sel mu P).Stab c) =
    Nat.card (MulAction.stabilizer (mtildeGSD W Ch sel mu P).G (rowPt Ch sel mu P c)) := by
  refine Eq.trans ?_ (card_stabilizer_toRow Ch sel mu P hd _)
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun g => ?_)
  exact (trivPt X _ _ _ _).symm.injective.eq_iff.symm

variable (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok)

end Step

section Pol

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem map_fockB {τ : Type} (f g : MvPolynomial τ K) : σ (fockB f g) = fockB (MvPolynomial.map σ f) (MvPolynomial.map σ g) := by
  rw [fockB_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), fockB, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, map_mul, map_natCast, MvPolynomial.coeff_map, MvPolynomial.coeff_map]

theorem map_pairB {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    σ (pairB lam F F') = pairB lam (MvPolynomial.map σ F) (MvPolynomial.map σ F') := by
  rw [pairB_apply, pairB_apply, map_mul, map_inv₀, map_fockB, extNormB, extNormB, map_prod]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [map_fockB, Formalism.L2.DIV.map_extremal]

theorem polOf_evV {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) (x : VV K lam) :
    polOf (Gr emb σ n) (Formalism.L2.Forms.shiftOf lam) (fr0 emb σ n) (evV emb 1 lam σ x) = MvPolynomial.map σ x.1 := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun _ => inv_one
  rw [evV_apply, ← e, polOf_fnOf]

end Pol

section Layer

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b))

@[reducible] def perOn : PerIn I where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H := H

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

include hd in

theorem row_law (z : (mtildeGSD W Ch sel mu P).EqFun) (g : (stepX Ch sel mu P).G ()) (d : (stepX Ch sel mu P).D ()) :
    MvPolynomial.map σ (z.1 (toRow sel mu (letI := (stepX Ch sel mu P).actD (); g • d : (stepX Ch sel mu P).D ()).1.1)).1 =
      (σ ((stepX Ch sel mu P).chr () g : X.K))⁻¹ • rhoP W.sgTrue (embGL (embAt σ X.emb) ((stepX Ch sel mu P).gam () g))
        (MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1) := by
  have h1 := z.2 (toRowG Ch sel mu P g) (toRow sel mu d.1.1)
  rw [mtilde_rho_toRowG W Ch sel mu P hd] at h1
  have h2 := (congrArg z.1 (toRow_smul Ch sel mu P g d.1.1)).trans h1
  refine (congrArg (fun y : VV X.K W.sgTrue => mapS σ y.1) h2).trans ?_
  refine (LinearMap.map_smulₛₗ (mapS σ) _ (actP W.sgTrue (embGL X.emb (ufGL _ _ g.1)) (z.1 (toRow sel mu d.1.1)).1)).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, mapS_apply, GlobalTheory.ValCmp.use₂]
  congr 1

def rowEmb : (mtildeGSD W Ch sel mu P).EqFun →ₛₗ[σ] (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ where
  toFun z := ⟨fun _ d => MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1, fun _ d =>
    ⟨GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ W.sgTrue _ (z.1 (toRow sel mu d.1.1)).2, fun g _ => row_law W Ch sel mu P hd σ z g d⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => map_add (mapS σ) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => LinearMap.map_smulₛₗ (mapS σ) _ _)

variable (hX : X.Ok) (hc : X.Tau → HCParam R)
  {Pl : Rows.Places X.K} (J : AtIn I) (Z : FmIn J Pl) (hI : I.Ok) (hJ : J.Ok)
  (hQ : (perOn W Ch sel mu P b0 til ext tz H).Ok) (l : J.Laws X.emb σ hc)
  (lf : FmLaws J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Pl hI hQ)
  (hT : (perOn W Ch sel mu P b0 til ext tz H).Over J)

end Layer

end GlobalTheory.PeriodOnStep
