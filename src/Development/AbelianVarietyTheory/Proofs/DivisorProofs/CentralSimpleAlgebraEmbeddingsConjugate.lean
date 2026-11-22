import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyAlgHomEqMapMinpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdPowOfAevalEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCharpolyNotSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIdxRatio
open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.VanishNonEll

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd

section Transport

variable {A B : Type} [Group A] [Group B]

theorem map_twCent_id (e : A ≃* B) (δ : A) :
    (twCent (MonoidHom.id A) δ).map e.toMonoidHom = twCent (MonoidHom.id B) (e δ) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a * δ = δ * a := ha
    show e a * e δ = e δ * e a
    rw [← map_mul, ha', map_mul]
  · intro hb
    have hb' : b * e δ = e δ * b := hb
    refine ⟨e.symm b, ?_, by simp⟩
    show e.symm b * δ = δ * e.symm b
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb']

theorem map_conj_equiv (e : A ≃* B) (K : Subgroup A) (x : A) :
    (K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

theorem orbK_congr_equiv (e : A ≃* B) (K : Subgroup A) (δ : A) (F : A → ℂ)
    (hinv : ∀ t ∈ twCent (MonoidHom.id B) (e δ), ∀ k ∈ K.map e.toMonoidHom, ∀ x,
      oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) (t * x * k) =
        oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) x) :
    orbK (MonoidHom.id A) K δ F = orbK (MonoidHom.id B) (K.map e.toMonoidHom) (e δ) (fun z => F (e.symm z)) := by
  unfold orbK
  rw [orbC_eq, orbC_eq]
  set TB := twCent (MonoidHom.id B) (e δ)
  set KB := K.map e.toMonoidHom
  have hmemT : ∀ a ∈ TB, e.symm a ∈ twCent (MonoidHom.id A) δ := by
    intro a ha
    rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ] at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    simpa using ha'
  have hmemK : ∀ b ∈ KB, e.symm b ∈ K := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    simpa using hb'
  have hpt : ∀ x : A, oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F x =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (e x) := by
    intro x
    unfold oTerm
    congr 1
    · have h1 : TB ⊓ KB = (twCent (MonoidHom.id A) δ ⊓ K).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id]
      have h2 : TB ⊓ KB.map (MulAut.conj (e x)).toMonoidHom =
          (twCent (MonoidHom.id A) δ ⊓ K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id, map_conj_equiv]
      rw [h1, h2]
      unfold vol
      rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective,
        Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    · simp
  let Φ : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A) →
      DoubleCoset.Quotient (TB : Set B) (KB : Set B) := fun q => DoubleCoset.mk TB KB (e (Quotient.out q))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro q1 q2 h
      obtain ⟨a, ha, b, hb, h'⟩ := (DoubleCoset.eq _ _ _ _).mp h
      calc q1 = DoubleCoset.mk _ K (Quotient.out q1) := (DoubleCoset.out_eq' _ _ q1).symm
        _ = DoubleCoset.mk _ K (Quotient.out q2) := by
          rw [DoubleCoset.eq]
          refine ⟨e.symm a, hmemT a ha, e.symm b, hmemK b hb, ?_⟩
          apply e.injective
          simp [h']
        _ = q2 := DoubleCoset.out_eq' _ _ q2
    · intro p
      refine ⟨DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p)), ?_⟩
      obtain ⟨a, b, ha, hb, h'⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))
      show DoubleCoset.mk TB KB (e (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))))) = p
      rw [h']
      conv_rhs => rw [← DoubleCoset.out_eq' TB KB p]
      rw [DoubleCoset.eq]
      have ha' : e a ∈ TB := by rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ]; exact Subgroup.mem_map_of_mem _ ha
      have hb' : e b ∈ KB := Subgroup.mem_map_of_mem _ hb
      refine ⟨(e a)⁻¹, TB.inv_mem ha', (e b)⁻¹, KB.inv_mem hb', ?_⟩
      simp [mul_assoc]
  have hz : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A), oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F (Quotient.out q) =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (Equiv.ofBijective Φ hΦ q)) := by
    intro q
    rw [hpt]
    obtain ⟨a, b, ha, hb, h'⟩ := DoubleCoset.mk_out_eq_mul TB KB (e (Quotient.out q))
    show _ = oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (DoubleCoset.mk TB KB (e (Quotient.out q))))
    rw [h', hinv a ha b hb]
  rw [finsum_congr hz]
  exact finsum_comp_equiv (Equiv.ofBijective Φ hΦ)
    (f := fun q => oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out q))

end Transport

theorem natDegree_minpoly_le (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ) (hn : 0 < n)
    (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (a : C) : (minpoly F a).natDegree ≤ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have h1 := GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  rw [← hmin] at h1
  have h2 : (minpoly L (ι a)).natDegree ≤ (ι a).charpoly.natDegree :=
    Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly _) (Matrix.charpoly_monic _).ne_zero
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  omega

theorem not_irreducible_map {F L : Type} [Field F] [Field L] (φ : F →+* L) (p : Polynomial F) (hp : p.Monic)
    (hirr : ¬ Irreducible p) : ¬ Irreducible (p.map φ) :=
  fun h => hirr (Polynomial.Monic.irreducible_of_irreducible_map φ p hp h)

end GlobalTheory.VanishNonEll
