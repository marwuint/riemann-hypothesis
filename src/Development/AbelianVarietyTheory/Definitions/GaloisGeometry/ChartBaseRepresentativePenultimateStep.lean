import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie

noncomputable section

namespace GlobalTheory.TwV.Model

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {w : Pr.Word}

open Classical in

theorem frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1 x
  · exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

private theorem mem_stdAt_iff_forall_intAt {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (w : Sp X.E n) :
    w ∈ stdAt X.E n P ↔ ∀ l, IntAt P (w l) := by
  show (∃ s ∈ P.asIdeal.primeCompl, s • w ∈ _) ↔ _
  constructor
  · rintro ⟨s, hs, hsw⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hsw l (Set.mem_univ l))
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  · intro h
    choose r s hs e using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ fun l _ => hs l, fun l _ => ?_⟩
    change ((∏ l, s l) • w) l ∈ (1 : Submodule (𝓞 X.E) X.E)
    rw [Submodule.mem_one]
    refine ⟨r l * ∏ k ∈ Finset.univ.erase l, s k, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l)]
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_prod]
    rw [← e l]
    ring

open Classical in

theorem sameCoset_iff {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (z y : Sp X.E (R.N j)) :
    SameCoset sel mu cst P ((frsF sel mu p P).symm z) ((frsF sel mu p P).symm y) ↔
      (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y)) ∈ p.deco.1.at P.1 := by
  have hc : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ =
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ := by
    split_ifs <;> simp
  have e : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y) =
      frsF sel mu p P (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ •
        ((frsF sel mu p P).symm z - (frsF sel mu p P).symm y)) := by
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, frsF_mem, mem_stdAt_iff_forall_intAt]
  unfold SameCoset
  simp only [hc, Pi.smul_apply, smul_eq_mul]

theorem sameCoset_trans {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n} (h : SameCoset sel mu cst P x y) (h' : SameCoset sel mu cst P y z) :
    SameCoset sel mu cst P x z := by
  intro l
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := h l
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := h' l
  refine ⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  simp only [Pi.sub_apply] at e₁ e₂ ⊢
  rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem sameCoset_symm {n : ℕ} {P : rowSG Pr sel mu} {x y : Sp X.E n} (h : SameCoset sel mu cst P x y) :
    SameCoset sel mu cst P y x := by
  intro l
  obtain ⟨r, s, hs, e⟩ := h l
  refine ⟨-r, s, hs, ?_⟩
  simp only [Pi.sub_apply] at e ⊢
  rw [map_neg, ← e]
  ring

end Gen

end GlobalTheory.TwV.Model

end
