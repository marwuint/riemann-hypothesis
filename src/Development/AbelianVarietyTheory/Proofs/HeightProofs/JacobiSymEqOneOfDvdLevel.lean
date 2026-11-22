import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.Cover

theorem zeta_mul_mem (F : IntermediateField ℚ ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n.Coprime m)
    (h1 : zeta m ∈ F) (h2 : zeta n ∈ F) : zeta (m * n) ∈ F := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : zeta (m * n) = zeta m ^ u * zeta n ^ v := by
    unfold zeta
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * huv'
  rw [e]
  exact mul_mem (zpow_mem h1 u) (zpow_mem h2 v)

theorem FO_le_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem half_of_split (D : D7) {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K))
    (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (I : Ideal (𝓞 D.host.E))
    (hI : I = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {w0E D}} ∧
      I * I.map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} ∧ I ⊔ I.map (bH D) = ⊤ := by
  obtain ⟨e, he1, he2, hpb⟩ := LPb.pb_eq_JK D hp P hP
  rw [hpb, LPb.map_JK] at hI
  subst hI
  refine ⟨fromK_of_gen ⟨_, rfl, ?_⟩, ?_, ?_⟩
  · rintro y (rfl | hy)
    · exact Subalgebra.natCast_mem _ _
    · rw [Set.mem_singleton_iff.1 hy]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [LPb.QE_map_bar, LPb.QE_mul D _ _ he1 he2]
  · rw [LPb.QE_map_bar, ← Ideal.isCoprime_iff_sup_eq]
    exact LPb.QE_cop_self D _ _ he2

end GlobalTheory.FinalJoin.Cover
