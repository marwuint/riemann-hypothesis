import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

noncomputable section

namespace GlobalTheory.Cut.Check

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Mat
variable {O : Type} [CommRing O] [IsDomain O] {k : ℕ}

theorem matKO_mk (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

theorem matKO_smul_one (a : O) (x : KOG O k) :
    matKO (a • (1 : Matrix (Fin k) (Fin k) O)) x = a • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [matKO_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    funext j
    have : ∀ x, (a • (1 : Matrix (Fin k) (Fin k) O)) j x = if j = x then a else 0 := fun x => by
      simp [Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, this, Pi.smul_apply]
    simp [apply_ite, Algebra.smul_def]

theorem WKG_eq_matKO {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = matKO (M g) x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl
end Mat

variable {D : D7} (i : D.nd.Loc)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, by funext x; simp⟩

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem cocW_quad {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {v} (hq : QuadAt i r Xs v)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    matKO (ψ fun x' => rO D.nd i r (S.p x') γ) (c γ) = c γ := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, h0, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') γ :=
      ⟨1, fun _ => 1, fun _ => γ, fun _ => one_mem _, by funext x; simp⟩
    have hn : InR' D.nd r S (-1) :=
      ⟨1, fun _ => -1, fun _ => 1, fun _ => neg_mem (one_mem _), by funext x; simp⟩
    have hY : InY D.nd r S ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) :=
      ⟨2, ![fun x' => rO D.nd i r (S.p x') γ, -1], fun _ => γ,
        fun j => by fin_cases j; exacts [hg, hn], by simp [Fin.sum_univ_two, sub_eq_add_neg]⟩
    have := h0 _ hY fun x' hx => by
      have hq' := hq _ hx γ hγ
      have e : ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) x' =
          (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • (((rO D.nd i r (S.p x') γ - 1) *
            (rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i))) *
              Eel D.nd S x') := by
        simp only [yg, Pi.sub_apply, Pi.mul_apply, mul_sub, sub_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
          smul_smul, Units.inv_mul, one_smul, mul_assoc, one_mul, mul_one]
        abel
      rw [e, hq']; simp
    rw [map_sub, sub_eq_zero, h1 _ hg _ (inY_yg i r S γ)] at this
    exact this
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add]
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul]

end GlobalTheory.Cut.Check

end
