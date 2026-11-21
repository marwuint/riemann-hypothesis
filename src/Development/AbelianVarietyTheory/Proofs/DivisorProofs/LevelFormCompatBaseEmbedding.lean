import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    (κ i).LastPos := by
  intro τ a ha
  rw [(h i τ).1 a, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hs : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
  have h1 : ¬ (a : ℕ) < D.R.k - 1 := by omega
  have h2 : (a : ℕ) - (D.R.k - 1) < D.R.m := by omega
  have h3 : (⟨(a : ℕ) - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by show (a : ℕ) - (D.R.k - 1) = i; omega)
  have h4 : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = (a : ℕ) + 1 := by exact_mod_cast ha.symm
  have h5 := (D.hc τ).gap_be i
  simp only [aPl, if_pos a.2, Formalism.L2.NTheta.lamAt, dif_neg h1, dif_pos h2, h3, h4]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem lastPos_wtA_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : w.LastPos) :
    Formalism.L2.Pj.LastPos (Q.Dw j) (wtA w) := by
  intro τ hτ hm
  obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q h.1 τ hτ
  have hmult : (Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold Datum.mult
    have hτ' : (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dif_pos (by omega)]
  unfold wtA
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

section Frame

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {r : ℕ} (hr : W.rank = r)
  (X : Data D.host.E r) {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {p : ℕ}

theorem isInvOf_cart (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsInvOf W hr X (fun τ => x₀ τ.1) (cart M) := by
  intro ρ τ hτ
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  have e : mat (Ψ := X.Ψ) (fun τ => x₀ τ.1) τ = x₀ (tauE D ρ) := by rw [← hτ]; rfl
  rw [e, hx.mul, cart, Formalism.REAL.Jm, torus_x0Mat, hx ρ]
  ext a c
  have hc := c.2
  simp only [sgnM, Matrix.neg_apply, mul_diagonal, reindex_apply, submatrix_apply, hε, hq, arr, sgn,
    finCongr_symm, finCongr_apply, Fin.val_cast]
  split_ifs with h1 h2 h3
  all_goals first | (simp at *; omega) | simp

theorem isBasOf_onb (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsBasOf W hr X hp (fun τ => x₀ τ.1) (onb M) := by
  intro ρ τ hτ k i a hi
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  show _ = x₀ τ.1 _ _
  rw [hτ, hx ρ]
  simp only [x0Mat, reindex_apply, submatrix_apply, hq, finCongr_symm, finCongr_apply, id, Fin.cast_cast, Fin.cast_eq_self]
  congr 1
  apply Fin.ext
  rw [hi]
  rcases k with k | k
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inl k) : Fin r) : ℕ) = X.p0 + k := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1] at h; omega
    · simp only [Fin.val_cast, h1, Sum.elim_inl]; omega
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inr k) : Fin r) : ℕ) = X.p0 - (k + 1) := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1, Sum.elim_inr]; omega
    · simp only [Fin.val_cast, h1] at h; omega

end Frame

end GlobalTheory.AdTh
