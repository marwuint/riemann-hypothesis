import Formalism.LocalToGlobal.CharacterGerms.RowTieCuts

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}

def mpt {n : ℕ} (a : Pt R n d) : Pt S n d := fun i => MvPowerSeries.map φ (a i)

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j => mpt φ (a j)) (MvPowerSeries.map φ f) := by
  unfold ev
  exact MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS R 1 d) :
    MvPowerSeries.map φ (ev ![a] f) = ev ![mpt φ a] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a] (by intro j i; fin_cases j; simp [ha]) f]
  congr 1
  funext j
  fin_cases j
  rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mpt φ a, mpt φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f]
  congr 1
  funext j
  fin_cases j <;> rfl

omit [CommRing S] in
theorem cc_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact (cc_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf

omit [CommRing S] in
@[simp] theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]

omit [CommRing S] in
@[simp] theorem cc_addOf {n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 := cc_ev ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) (F i) (hF i)

omit [CommRing S] in
@[simp] theorem cc_comp1 {n : ℕ} (ψ : Pt R 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    constantCoeff (comp1 ψ a i) = 0 := cc_ev ![a] (by intro j i; fin_cases j; simp [ha]) (ψ i) (hψ i)

omit [CommRing S] in
theorem zc_zero {n : ℕ} : ∀ i : Fin d, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp

@[simp] theorem mpt_pt {n : ℕ} (j : Fin n) : mpt φ (pt R d j) = pt S d j := by
  funext i
  simp [mpt, pt]

@[simp] theorem mpt_zero {n : ℕ} : mpt φ (0 : Pt R n d) = 0 := by
  funext i
  simp [mpt]

theorem mpt_comp1 {n : ℕ} (ψ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mpt φ (comp1 ψ a) = comp1 (mpt φ ψ) (mpt φ a) := by
  funext i
  exact map_ev1 φ a ha (ψ i)

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

end Formalism.L2.FormalSeriesBounds
