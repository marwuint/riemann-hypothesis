import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]

def pj (m : ℕ) (f : MvPowerSeries σ R) : JetR R σ m := Ideal.Quotient.mk _ (truncTotal (m + 1) f)

theorem pj_eq_mk {m : ℕ} {f : MvPowerSeries σ R} {q : MvPolynomial σ R} :
    pj m f = Ideal.Quotient.mk _ q ↔ ∀ e : σ →₀ ℕ, e.degree < m + 1 → coeff e f = q.coeff e := by
  rw [pj, Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
  exact forall₂_congr fun e he => by rw [MvPolynomial.coeff_sub, coeff_truncTotal _ he, sub_eq_zero]

theorem pj_coe (m : ℕ) (q : MvPolynomial σ R) : pj m (q : MvPowerSeries σ R) = Ideal.Quotient.mk _ q :=
  pj_eq_mk.2 fun _ _ => MvPolynomial.coeff_coe _ _

theorem pj_X (m : ℕ) (s : σ) : pj m (X s : MvPowerSeries σ R) = zR m s := by rw [← MvPolynomial.coe_X, pj_coe]

theorem aug_pj (m : ℕ) (f : MvPowerSeries σ R) : jetAug R σ m (pj m f) = constantCoeff f := by
  show MvPolynomial.aeval (fun _ : σ => (0 : R)) (truncTotal (m + 1) f) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal _ (by simp)]; rfl

theorem pj_ext {f g : MvPowerSeries σ R} (h : ∀ m, pj m f = pj m g) : f = g := by
  ext e
  exact (pj_eq_mk.1 (h e.degree) e (Nat.lt_succ_self _)).trans (coeff_truncTotal _ (Nat.lt_succ_self _))

def jS {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) : JetR R κ m →ₐ[R] JetR R τ m :=
  jetLift R (RingHom.ker (jetAug R τ m)) (ker_jetAug_pow τ m) (fun s => pj m (a s)) fun s => (aug_pj m _).trans (ha s)

theorem jS_zR {κ : Type} (m : ℕ) (a : κ → MvPowerSeries τ R) (ha) (s : κ) : jS m a ha (zR m s) = pj m (a s) :=
  jetLift_zR _ _ _ _ s

theorem jS_pj (m : ℕ) (a : σ → MvPowerSeries τ R) (ha) (f : MvPowerSeries σ R) : jS m a ha (pj m f) = pj m (subst a f) := by
  have e : ∀ p : MvPolynomial σ R, MvPolynomial.aeval (fun s => ((truncTotal (m + 1) (a s) : MvPolynomial τ R) :
      MvPowerSeries τ R)) p = ((MvPolynomial.aeval (fun s => truncTotal (m + 1) (a s)) p : MvPolynomial τ R) :
        MvPowerSeries τ R) := fun p => by
    induction p using MvPolynomial.induction_on with
    | C r => simp [MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p s hp => simp [hp]
  rw [pj.eq_def m (subst a f), truncTotal_subst ha, subst_coe, e]
  refine Eq.trans ?_ (pj_coe m _).symm
  have h : (jS m a ha).comp (Ideal.Quotient.mkₐ R _) =
      (Ideal.Quotient.mkₐ R _).comp (MvPolynomial.aeval fun s => truncTotal (m + 1) (a s)) :=
    MvPolynomial.algHom_ext fun s => (jS_zR m a ha s).trans (by rw [AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl)
  exact AlgHom.congr_fun h _

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}

def jP (m : ℕ) (p : Q R d n) : JetR R (Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m := jS m p.1 p.2

def jQ (m : ℕ) (b : Fin n → Q R d l) : JetR R (Fin n × Fin d) m →ₐ[R] JetR R (Fin l × Fin d) m :=
  jS m (fun s => (b s.1).1 s.2) fun s => (b s.1).2 s.2

variable {x} (hx : IsUnivChart G d x)
include hx

end ReciprocityTheory.ChartRestriction.G.Chart
