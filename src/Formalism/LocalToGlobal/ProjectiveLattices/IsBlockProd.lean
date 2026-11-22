import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import Formalism.LocalToGlobal.ProjectiveLattices.ContDiffAtOfDiff

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

section GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

structure LetterBlock where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col

variable {Dw n}

def LetterBlock.poly (K : Type) [CommRing K] (B : LetterBlock Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c

def IsBlockProd {K : Type} [CommRing K] (P₁ : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → LetterBlock Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P₁ = ∏ j, (bs j).poly K

end GlobalTheory

section HeadContinuityAtZero

variable {D : D7} (T : Top D) (j : ℕ)

open Classical in

def FrameTie (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th : ℝ) {n : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  IsBlockProd P₁ → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
    x ∈ ((T.U j σ).X k).dom →
    ∃ x' : ((T.U j σ).X k).dom, (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x'.1 τ' i'‖ = 1) ∧
      (∀ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 = recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x) ∧
      ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x'.1 = ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x ∧
      ∃ (W : UnfAt (T.U j σ) k x') (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x'.1)
        (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
        TorusPins W Wu A L ∧
        A.T.l2 1 A.s = 1 ∧
        ∃ ρ : (Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) → ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim,
          (∀ y, L (Pi.single (W.e.symm y) 1) = EuclideanSpace.single (ρ y) 1) ∧
          ∃ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n A.T.dim),
            ReciprocityTheory.ChartRestriction.G.I2.Disj bs ∧
            MvPolynomial.rename (fun l : LtN (T.Q.Dw j) n =>
              ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter n A.T.dim)) (MvPolynomial.map ((starRingEnd ℂ).comp σ) P₁) =
              ReciprocityTheory.ChartRestriction.G.I2.P1 bs ∧
            ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree ∧
            ∃ K, ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T (T.Q.l.M ^ 2) n ((T.Q.l.M : ℂ) • LinearMap.id) K

end HeadContinuityAtZero

end Formalism.L2.Pj
