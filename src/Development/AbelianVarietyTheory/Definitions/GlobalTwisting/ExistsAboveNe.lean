import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg

noncomputable section

namespace GlobalTheory.LvT.Built.Model

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section Split

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def offY (y : Ys X n) : Setoid (PtY ST SG Q y) where
  r p q := SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2
  iseqv := ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
    fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
    fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_mv (y : Ys X n) (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG) (h1 : SameOff ST p.1.1.deco.1.N d.1.N)
    (h2 : p.1.1.deco.1.be = d.1.be) : (offY y).r p (p.mv d) := by
  classical
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · rw [show p.mv d = ⟨(⟨(d, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ from dif_pos h]
    exact ⟨h1, h2, rfl, rfl⟩
  · rw [show p.mv d = p from dif_neg h]

theorem ok_repl {d : Deco X.E n ST SG} (hd : d.Ok) {e : Deco X.E n ST ∅} (he : e.Ok)
    (hG : ∀ w : SG, localization₂ w.1.asIdeal d.N = localization₂ w.1.asIdeal e.N) : Deco.Ok (⟨e.N, e.f, d.be⟩ : Deco X.E n ST SG) := by
  let d0 : Deco X.E n ∅ SG := ⟨d.N, fun P => absurd P.2 (Finset.notMem_empty _), d.be⟩
  have h0 : d0.Ok := ⟨hd.lat, hd.uni, fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _),
    fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _), hd.be_add, hd.be_smul, hd.be_off,
    hd.be_surj, hd.be_ker⟩
  have h1 := GlobalTheory.GO.decoration_admissible_of_localization_eq h0 he.lat he.uni (fun P => absurd P.2 (Finset.notMem_empty _)) hG
  exact ⟨he.lat, he.uni, he.f_add, he.f_smul, he.f_off, he.f_ne, h1.be_add, h1.be_smul, h1.be_off, h1.be_surj, h1.be_ker⟩

theorem exists_uf (γ : GL (Fin n) X.E) (h : (γ : Matrix (Fin n) (Fin n) X.E)ᴴ * (γ : Matrix (Fin n) (Fin n) X.E) = 1) :
    ∃ g : UF X.E n, ufGL X.E n g = γ := by
  refine ⟨⟨(Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv, fun x y => ?_⟩, ?_⟩
  · show hStd X.E n (γ.1 *ᵥ x) (γ.1 *ᵥ y) = hStd X.E n x y
    have e : ∀ a b : Fin n → X.E, hStd X.E n a b = star a ⬝ᵥ b := fun _ _ => rfl
    rw [e, e, star_mulVec, dotProduct_mulVec, vecMul_vecMul, h, vecMul_one]
  · apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, LevLaws.ufGL_mulVec]
    rfl

def splitY (T : ℕ) (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG)
    (Θ : β → LevQFam X.E X.K n Q) (pref : DecoF X.E n ST SG Q → Prop) (hP : ∀ P : ST, MoveHyp ST SG P)
    (hQ : ∀ (P : ST) (w : Q), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1)
    (hy : ∀ N N', SameOff ST N N' → y.ys N = y.ys N')
    (h1 : ∀ P ∈ ST, (T : 𝓞 X.E) ∈ P.asIdeal) (h2 : ∀ P ∈ ST, (T : 𝓞 X.E) ∉ P.asIdeal ^ 2) :
    Split (tdatY ST T y β Λ Θ pref) T where
  off _ := offY y
  off_act b g d d' h := by
    refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
    · ext x
      change x ∈ localization₂ w.asIdeal (gmap g.1.1 d.1.1.deco.1.N) ↔ x ∈ localization₂ w.asIdeal (gmap g.1.1 d'.1.1.deco.1.N)
      rw [mem_localization_gmap, mem_localization_gmap, h.1 w hw]
    · change (d.1.1.deco.1.act g.1.1 g.2.1.1).be = (d'.1.1.deco.1.act g.1.1 g.2.1.1).be
      simp only [Deco.act, h.2.1]
    · funext P
      change g.1.1 * d.1.1.fr P * _ = g.1.1 * d'.1.1.fr P * _
      rw [h.2.2.1]
    · change (fun v => g.1.1 v) '' d.1.2 = (fun v => g.1.1 v) '' d'.1.2
      rw [h.2.2.2]
  off_lat _ _ _ h := h.1
  ext b d d' h e := by
    have eN : d.1.1.deco.1.N = d'.1.1.deco.1.N := (congrArg Deco.N e :)
    have ef : d.1.1.deco.1.f = d'.1.1.deco.1.f := (congrArg Deco.f e :)
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (Subtype.ext (Deco.ext eN ef h.2.1)) h.2.2.1)) h.2.2.2)
  surj b d e he hs := by
    refine ⟨⟨(⟨(⟨_, ok_repl d.1.1.deco.2 he fun w => hs _ fun P hP' => (hP ⟨P, hP'⟩).sg w⟩, d.1.1.fr), fun P x => ?_⟩, d.1.2), ?_⟩,
      ⟨hs, rfl, rfl, rfl⟩, Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))⟩
    · have := hs P.1 fun P' hP' => hQ ⟨P', hP'⟩ P
      change _ ∈ localization₂ P.1.asIdeal e.N ↔ _
      rw [← this]
      exact d.1.1.2 P x
    · change d.1.2 ∈ y.ys e.N
      rw [← hy _ _ hs]
      exact d.2
  off_up b d P x hx hf := by
    have e := DecoSet.up_val d.1.1.deco P (hP P) (h1 _ P.2) (h2 _ P.2) hx hf
    refine off_mv y d _ (fun w hw => ?_) (by rw [e]; rfl)
    rw [e]
    exact ((upN_spec d.1.1.deco.2.lat d.1.1.deco.2.uni P.1 (hP P).ne hx).2.2.1 w (hw _ P.2).1 (hw _ P.2).2).localization_eq.symm
  off_dn b d P g _ := by
    show (offY y).r d (d.mv (d.1.1.deco.dn P g))
    unfold DecoSet.dn
    split_ifs with h
    · exact off_mv y d _ (fun w hw =>
        ((d.1.1.deco.2.dnN_spec P (hP P).ne).2.2.1 w (hw _ P.2).1 (hw _ P.2).2).localization_eq.symm) rfl
    · exact off_mv y d _ (fun _ _ => rfl) rfl
  off_dia b d P a := off_mv y d _ (fun _ _ => rfl) rfl
  dia_deco b d P P' a h := by
    classical
    show (d.mv (DecoSet.dia1 P a d.1.1.deco)).1.1.deco.1.f P' = d.1.1.deco.1.f P'
    unfold DecoSet.dia1
    rw [LevLaws.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG X.E ST) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne h, Units.val_one, one_mul]
  gam_surj b γ h := by
    obtain ⟨g, hg⟩ := exists_uf γ h
    exact ⟨(g, 1), hg⟩
  T_mem := h1
  T_nsq := h2
  nonconj P hP' Q' hQ' := (hP ⟨P, hP'⟩).st ⟨Q', hQ'⟩

end Split

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem localization_eq_of_sameOff (hPr : Pr.Ok) (u : Pr.Word) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) {n : ℕ}
    {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : SameOff (Pr.vT u) N N') (w : rowSG Pr sel mu) :
    localization₂ w.1.asIdeal N = localization₂ w.1.asIdeal N' := by
  classical
  have h2 : (Pr.T u : 𝓞 X.E) ∉ w.1.asIdeal := (Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)
  exact h w.1 fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h2

def splitAt (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) :
    Split (tdatAt sel mu cst L Tp u j) (Pr.T u) :=
  splitY _ _ _ _ _ _ (moveHyp_of_ok hPr u) (fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2))
    (fun N N' h => by
      have h1 := localization_eq_of_sameOff sel mu hPr u hQ h
      unfold ysAt
      split_ifs
      · show ybSet sel mu cst N = ybSet sel mu cst N'
        simp only [ybSet, locLat, h1]
      · rfl)
    (fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1) (fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2)

theorem splitAt_off (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)
    (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) (j : ℕ) (b) (p q : PtAt R sel mu cst u j) :
    ((splitAt sel mu cst L Tp hX hPr u hQ j).off b).r p q ↔ SameOffPt sel mu cst u p q := Iff.rfl

end Chain

namespace KerInh

end KerInh

end GlobalTheory.LvT.Built.Model
