import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AllWt
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

section Action

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

abbrev Rs (l : Level H) : Type := 𝓞 E ⧸ l.Mb

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := fun h => by
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h1
  have := l.three_le
  omega

instance (l : Level H) : Finite (Rs l) := Ideal.finiteQuotientOfFreeOfNeBot _ (half_ne_bot l)

abbrev Gz (l : Level H) (r : ℕ) : Type := GL (Fin r) (Rs l)

instance (l : Level H) (r : ℕ) : Fintype (Gz l r) := Fintype.ofFinite _

variable {l l' : Level H} {r : ℕ}

variable (Xo' : Moduli Dw l') (c' : Coeff l') {K : Type} [Field K] (ι : K →+* c'.F)
  (e : Basis (Fin r) (Rs l) (LaMod Dw l))

variable {Xo' c'} {n : ℕ} (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ n)

end Action

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnifAt {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ D.R.r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r)
    (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  IsUnf U ∧ ∃ (hr : V.rank = D.R.r) (Kf : Subgroup (GA D V))
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ),
    (∀ k, ModelW V hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧ IsLevelK V l.M Kf ∧
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr ∧
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) ∧
      LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) ∧
      DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) e F ik φ th x₀

variable (T : CoreJ D) (i : Fin D.R.m)

variable {T i} {l' : Level T.Q.H} {Xo' : Moduli (T.Q.Dw ((i : ℕ) + 1)) l'} {c' : Coeff l'}

abbrev incl (hle : T.Q.c.F ≤ c'.F) : T.Q.c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def ringCost (K : Type) [Field K] [NumberField K] : ℝ := Real.log (finrank ℚ K) + Real.log (rootDiscr K)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes
