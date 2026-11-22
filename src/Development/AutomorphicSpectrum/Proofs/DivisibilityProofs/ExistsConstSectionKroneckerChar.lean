import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopen
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeight
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSections
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionPlaceValuation
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CovEx

theorem exists_padic_emb (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : Nonempty (K →+* ℂ_[p]) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[p]) : K →ₐ[ℚ] ℂ_[p]).toRingHom⟩

theorem goodOf_or {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (σ : c.F →+* ℂ) : Formalism.L2.Pj.goodOf c σ = σ ∨ (starRingEnd ℂ).comp (Formalism.L2.Pj.goodOf c σ) = σ := by
  unfold Formalism.L2.Pj.goodOf
  split_ifs
  · exact Or.inl rfl
  · right; ext x; simp

theorem exists_constSec : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H),
    ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0,
      s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hR hG E _ _ _ H D l Xo c r U x hL _ χ hχ Z τ
  have hpos := hL.pos
  obtain ⟨κ⟩ := exists_padic_emb c.F (⟨2, Nat.prime_two⟩ : Nat.Primes)
  obtain ⟨O, _, _, _, β, Y, hβ, -, -, -⟩ :=
    _root_.PositivityTheory.Ar2.exists_local_model_dvr E H D l Xo c ⟨2, Nat.prime_two⟩ κ hpos (hL.good 2 Nat.prime_two)
  obtain ⟨hclopen, hcpt, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.cptOver_any E H D l Xo c (Z : Set (Xo.XF c)) Z.2
  obtain ⟨Z'⟩ := hcpt O β Y hβ
  have hgeom : Z'.IsGeom := _root_.GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed E H D l Xo c O β Y Z Z' hβ hL.geo
  obtain ⟨φ, hline, hflat, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 hβ hpos τ.2 hgeom
  obtain ⟨hnorm, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 φ hβ hpos τ.2 hgeom hline hflat
  choose t ht ht' using fun σ => hnorm (Formalism.L2.Pj.goodOf c σ)
  have hInf : ∀ σ, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ (t σ) := fun σ => by
    rcases goodOf_or c σ with h | h
    · have := ht σ
      rwa [h] at this
    · have := ht' σ
      rwa [h] at this
  have hFinEx : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ t :=
    fun p κ => _root_.GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood hR hG E H D l Xo c O β Y Z Z' τ.1 φ p κ hβ hpos τ.2 Z.2 hgeom hflat (hL.good p p.2)
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho E H D l Xo c Z τ.1 φ hFinEx
  obtain ⟨hex, ⟨N, hNinf, hNfin⟩, hdict⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.Dd.deg_dict c.F (fun σ => Real.exp (t σ)) ρ
  have hinfN : ∀ s, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ s (N.inf s) := fun s => by
    rw [hNinf s, Real.log_exp]
    exact hInf s
  have hfinN : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (N.fin p κ) :=
    fun p κ => by
      obtain ⟨la, π, h1, h2⟩ := hex p κ
      rw [hNfin p κ la π h1 h2]
      exact hρ p κ la π h1 h2
  obtain ⟨hadel, hdeg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel hR hG E H D l Xo c O β Y _ Z' τ.1 φ N χ hχ hβ hpos τ.2 hclopen hgeom hflat
    hinfN hfinN
  obtain ⟨hsupp, hline'⟩ := hdict N hNinf hNfin
  obtain ⟨s, s', hs, hs', hi, hi', hm, hread⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec E H D l Xo c O β Y Z Z' τ φ hflat
  have hval := _root_.PositivityTheory.Xgn.line_function_place_valuation E H D l Xo c Z τ s φ ρ hline hread hρ
  have hPts := GlobalTheory.FlatLine.hasPts U hpos hL.good hL.unf Z
  refine ⟨{ sig := s, inv := s', sig_mem := hs, inv_mem := hs', idem_sig := hi, idem_inv := hi', mul_inv := hm,
            cInf := fun σ => Real.exp (t σ), cInf_pos := fun σ => Real.exp_pos _,
            norm_inf := fun σ => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨(hPts.1 σ).1, fun z hz =>
              _root_.GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge E H D l Xo c r (Formalism.L2.Pj.goodOf c σ) (U (Formalism.L2.Pj.goodOf c σ)) x Z τ s φ (t σ)
                (Formalism.L2.Pj.goodEmb_goodOf c σ) (hL.unf _ (Formalism.L2.Pj.goodEmb_goodOf c σ))
                (hL.xi _ (Formalism.L2.Pj.goodEmb_goodOf c σ)) hs hline hread (ht σ) z hz ((hPts.1 σ).2 z hz)⟩,
            rho_vw := ρ,
            val_fin := fun w => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨hPts.2 w, fun v hv => by
              simpa using hval w v hv⟩,
            finite_rho := hsupp.1 hadel }, ?_⟩
  exact (hline' hadel).symm.trans hdeg

end GlobalTheory.CompanionTheory.Ar.Br.CovEx
