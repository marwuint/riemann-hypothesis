import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

noncomputable section

namespace GlobalTheory.SWLink.Conj

variable {D : D7}

def cjG (D : D7) (k : ℕ) : GL (Fin k) (AE D) →* GL (Fin k) (AE D) := Matrix.GeneralLinearGroup.map (cA D)

theorem cjG_cjG {k : ℕ} (g : GL (Fin k) (AE D)) : cjG D k (cjG D k g) = g := Units.ext (cj_cj g.1)

theorem continuous_cj {m n : ℕ} : Continuous (cj : Mx D m n → Mx D m n) :=
  continuous_id.matrix_map GlobalTheory.FockCompare.ThetaCont.continuous_conj

theorem continuous_cjG (k : ℕ) : Continuous (cjG D k) := by
  refine Units.continuous_iff.2 ⟨continuous_cj.comp Units.continuous_val, ?_⟩
  exact continuous_cj.comp Units.continuous_coe_inv

theorem mem_iff (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F (-V.gram)) ↔ cjG D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  show (g.1ᵀ * incM D.host.F (-V.gram) * g.1.map (cAl D) : Mx D V.rank V.rank) = incM D.host.F (-V.gram) ↔
    (adj (cj g.1) * rat V.gram * cj g.1 : Mx D V.rank V.rank) = rat V.gram
  rw [map_cAl, incM_eq, rat_neg, adj_eq, cj_cj, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def conjEquiv (V : HSp D) : UD D (-V.gram) ≃ₜ* GA D V where
  toFun h := (⟨cjG D V.rank h.1, (mem_iff V h.1).1 h.2⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)
  invFun g := ⟨cjG D V.rank (matHom V g), (mem_iff V _).2 (by
    rw [cjG_cjG]; exact (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2)⟩
  left_inv h := Subtype.ext (cjG_cjG h.1)
  right_inv g := Subtype.ext (cjG_cjG (matHom V g))
  map_mul' h h' := Subtype.ext (map_mul (cjG D V.rank) h.1 h'.1)
  continuous_toFun := ((continuous_cjG V.rank).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_cjG V.rank).comp continuous_subtype_val).subtype_mk _

end GlobalTheory.SWLink.Conj

end
