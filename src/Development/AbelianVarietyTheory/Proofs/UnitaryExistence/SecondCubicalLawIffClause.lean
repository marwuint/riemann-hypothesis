import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {d : ℕ}

def ptsOf (j : JetPts t.G x0 d) : ∀ m, jOG x0 d m 1 ⟶ t.G := fun m => jPt t.G x0 j 1 m 0

theorem jptG_ptsOf (j : JetPts t.G x0 d) {n : ℕ} (m : ℕ) (k : Fin n) :
    jptG t x0 d (ptsOf t x0 j) m k = jPt t.G x0 j n m k := by
  show homAt x0 _ ≫ homAt x0 _ ≫ j m = homAt x0 _ ≫ j m
  rw [← Category.assoc, homAt_comp]
  refine congrArg (fun g => homAt x0 g ≫ j m) (jet_hom_ext fun s => ?_)
  rw [AlgHom.comp_apply, jetIn, jetIn, jetCopy, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X,
    jetMap_mk, MvPolynomial.aeval_X]

theorem pair_eq (j : JetPts t.G x0 d) (m : ℕ) : jPt t.G x0 j 2 m =
    ![jptG t x0 d (ptsOf t x0 j) m (0 : Fin 2), jptG t x0 d (ptsOf t x0 j) m (1 : Fin 2)] :=
  funext fun k => by fin_cases k <;> exact (jptG_ptsOf t x0 j m _).symm

def castGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) :
    LB.Gen (cubeLB t.G p t.PP.L) ≃ LB.Gen (cubeLB t.G q t.PP.L) :=
  Equiv.cast (congrArg (fun p => LB.Gen (cubeLB t.G p t.PP.L)) h)

attribute [irreducible] castGen

def frEquiv (j : JetPts t.G x0 d) : FrameFam t.G x0 t.PP.L j ≃ ∀ m, FrTyG t x0 d (ptsOf t x0 j) m where
  toFun := fun e m => castGen t (pair_eq t x0 j m) (e m)
  invFun := fun e m => (castGen t (pair_eq t x0 j m)).symm (e m)
  left_inv := fun e => funext fun m => (castGen t (pair_eq t x0 j m)).symm_apply_apply (e m)
  right_inv := fun e => funext fun m => (castGen t (pair_eq t x0 j m)).apply_symm_apply (e m)

theorem frEquiv_apply (j : JetPts t.G x0 d) (e : FrameFam t.G x0 t.PP.L j) (m : ℕ) :
    frEquiv t x0 j e m = castGen t (pair_eq t x0 j m) (e m) := rfl

variable {t x0} {j : JetPts t.G x0 d} (e : FrameFam t.G x0 t.PP.L j)

end GlobalTheory.FrameCompare
