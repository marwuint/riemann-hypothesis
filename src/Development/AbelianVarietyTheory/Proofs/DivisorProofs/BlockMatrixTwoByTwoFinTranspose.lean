import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

def cat {R : Type} (p y : Matrix (Fin m) (Fin n) R) : Matrix (Fin m) (Fin (n + n)) R :=
  (Matrix.fromCols p y).submatrix id finSumFinEquiv.symm

def cj (x : Mx D m n) : Mx D m n := x.map (cA D)

def pt (T : GL (Fin (n + n)) D.host.E) (q x : Mx D m n) : Mx D m (n + n) :=
  cat (cj q) (cj x) ⬝ (rat T.1 : Mx D (n + n) (n + n))ᵀ

abbrev Dbx (V : HSp D) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) : Type :=
  Darboux (symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂)) (Fin V.rank × Fin n × Fin d)

def IsCoord (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (T : GL (Fin (n + n)) D.host.E) {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (co : Dbx V J₂ d) : Prop :=
  ∀ q x : Mx D V.rank n, (co.e (pt T q x)).1 = coord ε x ∧
    ∀ x' : Mx D V.rank n, coord ε x' ⬝ᵥ (co.e (pt T q x)).2 = -StdUnn.trA (Matrix.trace (StdUnn.inner V x' q))

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

theorem map_cAl {k l : ℕ} (x : Mx D k l) : x.map (cAl D) = cj x := by
  funext i j; exact cAl_eq _

theorem incM_eq {k l : ℕ} (J : Matrix (Fin k) (Fin l) D.host.E) : incM D.host.F J = rat J := rfl

theorem blk_eq {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : blk a b c d = StdUnn.blk4 a b c d := rfl

theorem adj_eq (x : Mx D m n) : adj x = (cj x)ᵀ := rfl

@[simp] theorem cj_cj (x : Mx D m n) : cj (cj x) = x := by
  funext i j; exact congrFun (congrFun (adj_adj x) i) j

@[simp] theorem cj_zero : cj (0 : Mx D m n) = 0 := by funext i j; exact map_zero (cA D)

@[simp] theorem cj_neg (x : Mx D m n) : cj (-x) = -cj x := by funext i j; exact map_neg (cA D) _

@[simp] theorem cj_add (x y : Mx D m n) : cj (x + y) = cj x + cj y := by funext i j; exact map_add (cA D) _ _

@[simp] theorem cj_one : cj (1 : Mx D n n) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cj_transpose (x : Mx D m n) : cj xᵀ = (cj x)ᵀ := rfl

theorem cj_rat (M : Matrix (Fin m) (Fin n) D.host.E) : cj (rat M : Mx D m n) = rat (M.map D.sp.cm.sig) := rfl

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

section Witt

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

def coordL {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (m n : ℕ) :
    Mx D m n ≃ₗ[AF D.host.F] (Fin m × Fin n × Fin d → AF D.host.F) where
  toFun := coord ε
  map_add' x y := by funext p; simp [coord]
  map_smul' a x := by funext p; simp [coord]
  invFun c := Matrix.of fun i j => (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.symm fun k => c (i, j, k)
  left_inv y := by
    funext i j
    exact (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.symm_apply_apply (y i j)
  right_inv c := by
    funext p
    exact congrFun ((Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.apply_symm_apply fun k => c (p.1, p.2.1, k)) p.2.2

theorem coordL_apply {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) : coordL ε m n x = coord ε x := rfl

end GlobalTheory.SWLink

end
