import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.LawLog

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

def twoVars (k : Type) [CommRing k] (d : ℕ) : Fin 2 × Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  fun q => X (if q.1 = 0 then Sum.inl q.2 else Sum.inr q.2)

def oneVar (k : Type) [CommRing k] (d : ℕ) : Fin 1 × Fin d → MvPowerSeries (Fin d) k :=
  fun q => X q.2

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_twoVars (q : Fin 2 × Fin d) : constantCoeff (twoVars k d q) = 0 := by simp [twoVars]

theorem cc_oneVar (q : Fin 1 × Fin d) : constantCoeff (oneVar k d q) = 0 := by simp [oneVar]

theorem hs_twoVars : HasSubst (twoVars k d) := hasSubst_of_constantCoeff_zero cc_twoVars

theorem hs_oneVar : HasSubst (oneVar k d) := hasSubst_of_constantCoeff_zero cc_oneVar

def sndEmb (d : ℕ) : Fin 1 × Fin d ↪ Fin d :=
  ⟨Prod.snd, fun _ _ h => Prod.ext (Subsingleton.elim _ _) h⟩

theorem coeff_single_oneVar (f : PS k 1 d) (b : Fin d) :
    coeff (Finsupp.single b 1) (subst (oneVar k d) f) = coeff (Finsupp.single ((0 : Fin 1), b) 1) f := by
  have h1 : subst (oneVar k d) f = rename (sndEmb d) f := by
    rw [rename_eq_subst]; rfl
  have h2 : Finsupp.single b 1 = Finsupp.embDomain (sndEmb d) (Finsupp.single ((0 : Fin 1), b) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [h1, h2, coeff_embDomain_rename]

theorem subst_oneVar {n : ℕ} {τ : Type} [Finite τ] (T : Fin n × Fin d → MvPowerSeries τ k)
    (hT : ∀ q, constantCoeff (T q) = 0) (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (f : PS k 1 d) :
    subst (fun i => subst T (a i)) (subst (oneVar k d) f) = subst T (ev ![a] f) := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h1 : HasSubst (fun i => (subst T (a i) : MvPowerSeries τ k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hTs hT (ha i)
  have h2 : HasSubst (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt k n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j; exact ha i
  unfold ev
  rw [subst_comp_subst_apply hs_oneVar h1, subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  simp only [oneVar]
  rw [subst_X h1]
  rfl

theorem add_pt (G : FGLaw k d) : G.add (pt k (n := 2) d 0) (pt k d 1) = G.F := by
  funext c
  show ev (n := 2) ![pt k d 0, pt k d 1] (G.F c) = G.F c
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  unfold ev
  rw [e, subst_self]
  rfl

end GlobalTheory.LawLog
