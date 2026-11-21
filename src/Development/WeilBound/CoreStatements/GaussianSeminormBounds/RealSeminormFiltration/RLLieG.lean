import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieE
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieF

noncomputable section

open scoped TensorProduct Matrix Classical RealInnerProductSpace Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealWeil Complex

namespace PositivityTheory.RL.Up

section Inv

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hTens_actB [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actB c g x) (actB c g y) = hTens c JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  rw [hTens_eq, hTens_eq]
  have : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB
    rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E)ᵀ).map c from
      Matrix.map_mul (f := c.toRingHom), Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    conv_rhs => rw [← hg]
    simp only [Matrix.mul_assoc]
  rw [this]

end Inv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ext_at (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m n : Type} {X X' : Matrix m n (AE F E)}
    (hx : At (evI F) (X - X')) (hinf : ∀ w, X.map (piInf (τ w)) = X'.map (piInf (τ w))) : X = X' := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf h τ _ (fun u hu => congrFun (congrFun (hx u hu) i) j) fun w => ?_)
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (hinf w) i) j

theorem At.sub' {M : Type} [AddCommGroup M] [Module (AF F) M] {a b : M} (ha : At (evI F) a) (hb : At (evI F) b) :
    At (evI F) (a - b) := fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_zero]

theorem exists_lf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (m n : Type) :
    ∃ L : (InfinitePlace F → Matrix m n ℂ) → Matrix m n (AE F E), Continuous L ∧ (∀ z, At (evI F) (L z)) ∧
      ∀ z w, (L z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hs'⟩ := exists_section h τ
  refine ⟨fun z => Matrix.of fun i j => s fun w => z w i j,
    continuous_matrix fun i j => hs.comp (continuous_pi fun w => (continuous_apply w).matrix_elem i j),
    fun z a ha => ?_, fun z w => ?_⟩
  · ext i j
    exact (hs' _).1 a ha
  · ext i j
    exact (hs' _).2 w

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem exists_iota (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E))
    (K : InfinitePlace F → Matrix β β ℂ)
    (hK : ∀ w (g : Matrix β β ℂ), gᴴ * K w * g = K w → gᵀ * J.map (piInf (τ w)) * g.map star = J.map (piInf (τ w))) :
    ∃ ι : SG K →* UG (cA σ) J, Continuous ι ∧ (∀ g, At (evI F) (((ι g).1 : Matrix β β (AE F E)) - 1)) ∧
      ∀ g w, ((ι g).1 : Matrix β β (AE F E)).map (piInf (τ w)) = g.1.1 w := by
  obtain ⟨L, hc, hL, hL'⟩ := exists_lf h τ β β
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hG : ∀ (a : InfinitePlace F → Matrix β β ℂ) w, (1 + L (a - 1)).map (piInf (τ w)) = a w := fun a w => by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hL']
    simp
  let G : (InfinitePlace F → Matrix β β ℂ) →* Matrix β β (AE F E) :=
    { toFun := fun a => 1 + L (a - 1)
      map_one' := ext_at h τ (fun u hu => by rw [add_sub_cancel_left, hL _ u hu]) fun w => by
        rw [hG, Matrix.map_one _ (map_zero _) (map_one _)]
        rfl
      map_mul' := fun a c => ext_at h τ (fun u hu => by
        have e : (1 + L (a * c - 1)) - (1 + L (a - 1)) * (1 + L (c - 1)) =
            L (a * c - 1) - L (c - 1) - L (a - 1) * (1 + L (c - 1)) := by noncomm_ring
        rw [e, smul_sub, smul_sub, ← Matrix.smul_mul, hL _ u hu, hL _ u hu, hL _ u hu]
        simp) fun w => by
        rw [Matrix.map_mul, hG, hG, hG]
        rfl }
  have hGc : Continuous G := continuous_const.add (hc.comp (continuous_id.sub continuous_const))
  have hGU : ∀ g : SG K, (G g.1.1)ᵀ * J * (G g.1.1).map (cA σ) = J := fun g => by
    refine ext_at h τ (fun u hu => ?_) fun w => ?_
    · set N := L (g.1.1 - 1)
      have hN : u • N = 0 := hL _ u hu
      have e0 : (G g.1.1).map (cA σ) = 1 + N.map (cA σ) := by
        show (1 + N).map _ = _
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      have e : (G g.1.1)ᵀ * J * (G g.1.1).map (cA σ) - J = Nᵀ * (J * (G g.1.1).map (cA σ)) + J * N.map (cA σ) := by
        rw [e0]
        show (1 + N)ᵀ * _ * _ - _ = _
        simp only [Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
      have e1 : u • N.map (cA σ) = 0 := by
        ext i j
        have := congrArg (cA σ) (congrFun (congrFun hN i) j)
        simpa using this
      rw [e, smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, e1, ← Matrix.transpose_smul, hN]
      simp
    · rw [map_form h, show (G g.1.1).map (piInf (τ w)) = _ from hG _ w]
      exact hK w _ (congrFun (show star g.1.1 * K * g.1.1 = K from g.2) w)
  refine ⟨((Units.map G).comp (SG K).subtype).codRestrict _ hGU,
    ((Continuous.units_map G hGc).comp continuous_subtype_val).subtype_mk _, fun g u hu => ?_, fun g w => hG _ w⟩
  show u • (1 + L (g.1.1 - 1) - 1) = 0
  rw [add_sub_cancel_left, hL _ u hu]

variable (σ) in

def sB (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (u v : Matrix α β (AE F E)) : ℝ :=
  -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u v))

def IsD {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)) : Prop :=
  ∀ u, At (evI F) u → ∀ f x, D u f x = fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

variable {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}

theorem at_e {u : Matrix α β (AE F E)} (hu : At (evI F) u) : At (evI F) (d.e u) := fun s hs => by
  rw [← map_smul, hu s hs, map_zero]

theorem at_symm {p} (hp : At (evI F) p) : At (evI F) (d.e.symm p) := fun s hs => by
  rw [← map_smul, hp s hs, map_zero]

theorem sympl_e {l : Type} [Fintype l] (c : Co F κ l) (u v : Matrix α β (AE F E)) :
    sympl (c.vec (d.e u)) (c.vec (d.e v)) = sB σ JA JB u v := by
  rw [c.sympl_vec, sB, d.form]

theorem IsD.P {D} (hD : IsD d D) {l : Type} [Fintype l] (c : Co F κ l) {u : Matrix α β (AE F E)} (hu : At (evI F) u)
    (f : Sch l) : c.P (dRho (c.vec (d.e u)) f) = D u (c.P f) := by
  ext x
  rw [c.P_dRho, hD u hu]

theorem IsD.comm {D} (hD : IsD d D) {u v : Matrix α β (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v) (f : SInf F κ) :
    D u (D v f) = D v (D u f) + (2 * π * I * sB σ JA JB u v) • f := by
  obtain ⟨n, ⟨c⟩⟩ := exists_co F κ
  have := congrArg (fun L => c.P (L (c.P' f))) (dRho_comm (c.vec (d.e u)) (c.vec (d.e v)))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, map_sub, map_smul, hD.P c hu, hD.P c hv, c.P_P', sympl_e] at this
  rw [← this]
  abel

end PositivityTheory.RL.Up

end
