import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

namespace GlobalTheory.AutFunCompare

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

theorem HA_ext {g h : HA R σ J} (e : ∀ r s, (HA.mat R σ J g).1 r s = (HA.mat R σ J h).1 r s) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext e))

theorem map_tensNU_zero (φ : R' →ₐ[F] R'') (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = 0) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (tensNU j hj z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem map_tensNU_self (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = a) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (tensNU j hj z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mat_mapH (φ : R →ₐ[F] R') (g : HA R σ J) (r s : Fin M) :
    (HA.mat R' σ J (mapH σ J φ g)).1 r s =
      Algebra.TensorProduct.map φ (AlgHom.id F E) ((HA.mat R σ J g).1 r s) := rfl

theorem mat_extH (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (g : HA R σ J) (r s : Fin M) :
    (HA.mat R' σ J (extH σ J j hj g)).1 r s =
      (1 - tensNU (E := E) j hj 1) * (1 : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) r s +
        tensNU j hj ((HA.mat R σ J g).1 r s) := rfl

theorem mapH_extH_zero (φ : R' →ₐ[F] R'') (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = 0) (g : HA R σ J) : mapH σ J φ (extH σ J j hj g) = 1 := by
  refine HA_ext σ J fun r s => ?_
  rw [mat_mapH, mat_extH, map_add, map_mul, map_sub, map_tensNU_zero φ j hj h, map_tensNU_zero φ j hj h]
  show _ = (1 : Matrix (Fin M) (Fin M) (R'' ⊗[F] E)) r s
  by_cases e : r = s <;> simp [Matrix.one_apply, e]

theorem mapH_extH_self (φ : R' →ₐ[F] R) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (h : ∀ a, φ (j a) = a) (g : HA R σ J) : mapH σ J φ (extH σ J j hj g) = g := by
  refine HA_ext σ J fun r s => ?_
  rw [mat_mapH, mat_extH, map_add, map_mul, map_sub, map_tensNU_self φ j hj h, map_tensNU_self φ j hj h]
  simp

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R'] [IsTopologicalRing R']

theorem continuous_tensNU (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (hc : Continuous j)
    [FiniteDimensional F E] : Continuous (tensNU (E := E) j hj) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology R' (R' ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  have : IsTopologicalRing (R' ⊗[F] E) := IsModuleTopology.isTopologicalRing R' _
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis R b).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : (tensNU (E := E) j hj : _ → _) = fun z => ∑ i, j (e z i) • ((1 : R') ⊗ₜ[F] b i) := by
    funext z
    conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_equivFun z, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, TensorProduct.smul_tmul']
  rw [h2]
  refine continuous_finsetSum _ fun i _ => ?_
  have h3 : Continuous fun z => j (e z i) := hc.comp ((continuous_apply i).comp h1)
  exact Continuous.fun_smul h3 continuous_const

theorem continuous_mapH [FiniteDimensional F E] (φ : R →ₐ[F] R') (hc : Continuous φ) :
    Continuous (mapH σ J φ) := by
  have h : Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) :=
    continuous_tensNU (E := E) φ.toLinearMap (map_mul φ) hc
  refine Continuous.subtype_mk (Continuous.comp (g := bc _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_id.matrix_map h)

theorem continuous_extH [FiniteDimensional F E] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)
    (hc : Continuous j) : Continuous (extH σ J j hj) := by
  have : IsModuleTopology R' (R' ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R' ⊗[F] E) := IsModuleTopology.isTopologicalRing R' _
  have h := continuous_tensNU (E := E) j hj hc
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map h))

end Points

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

theorem projFin_ofFin (y : GFin hc V) : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V (ofFin hc V y) = y :=
  mapH_extH_self _ _ _ _ _ (fun _ => rfl) y
theorem projInf_ofFin (y : GFin hc V) : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V (ofFin hc V y) = 1 :=
  mapH_extH_zero _ _ _ _ _ (fun _ => rfl) y
theorem eq_of_proj {g h : GA hc V} (h1 : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V g = IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V h)
    (h2 : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g = IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V h) : g = h := by
  rw [← mul_inv_eq_one]
  have a : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projInf hc V (g * h⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have b : IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V (g * h⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  exact Subtype.ext (Units.ext (GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) _
    (congrArg (fun x => (HA.mat _ _ _ x).1) a) (congrArg (fun x => (HA.mat _ _ _ x).1) b)))

theorem ofFin_projFin {g : GA hc V} (h : g ∈ finPts hc V) : ofFin hc V (IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g) = g :=
  eq_of_proj hc V ((projInf_ofFin hc V _).trans (Eq.symm h)) (projFin_ofFin hc V _)

def infEmb (τ : E →+* ℂ) : Ainf F ⊗[F] E →+* ℂ :=
  (locMap hc τ).comp (Algebra.TensorProduct.map
    (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) (placeOf F τ) :
      Ainf F →ₐ[F] (placeOf F τ).Completion) (AlgHom.id F E)).toRingHom

theorem isInfEmb_infEmb (τ : E →+* ℂ) : Formalism.MainNotions.StandardLattice.IsInfEmb τ (infEmb hc τ) := by
  refine ⟨fun x => ?_, ?_⟩
  · show locMap hc τ ((1 : (placeOf F τ).Completion) ⊗ₜ[F] x) = _
    simp
  · have : (fun a : Ainf F => infEmb hc τ (a ⊗ₜ[F] (1 : E))) =
        fun a => InfinitePlace.Completion.extensionEmbedding (placeOf F τ) (a (placeOf F τ)) := by
      funext a
      show locMap hc τ (a (placeOf F τ) ⊗ₜ[F] (1 : E)) = _
      simp
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp (continuous_apply _)

theorem isInfEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h' : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ') : θ = θ' := by
  have key : (fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))) = fun a : Ainf F => θ' (a ⊗ₜ[F] (1 : E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h.2 h'.2 ?_
    funext x
    have e : (algebraMap F (Ainf F) x) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    show θ (algebraMap F (Ainf F) x ⊗ₜ[F] (1 : E)) = θ' (algebraMap F (Ainf F) x ⊗ₜ[F] (1 : E))
    rw [e, h.1, h'.1]
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h.1, h'.1, congrFun key a]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def evW (w : InfinitePlace F) : Ainf F →ₐ[F] w.Completion :=
  Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w

open Classical in

def sgW (w : InfinitePlace F) : w.Completion →ₗ[F] Ainf F :=
  LinearMap.single F (fun w : InfinitePlace F => w.Completion) w

omit [NumberField F] in
theorem sgW_mul (w : InfinitePlace F) (a b : w.Completion) : sgW w (a * b) = sgW w a * sgW w b := by
  classical
  exact Pi.single_mul w a b

omit [NumberField E] [StarRing E] in
theorem infTens_ext {z z' : Ainf F ⊗[F] E} (h : ∀ w : InfinitePlace F,
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z =
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z') : z = z' := by
  classical
  have key : ∀ z : Ainf F ⊗[F] E, z = ∑ w : InfinitePlace F,
      LinearMap.rTensor E (sgW w) (Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : a = ∑ w, sgW w (evW w a) := (Finset.univ_sum_single a).symm
      conv_lhs => rw [this]
      exact TensorProduct.sum_tmul _ _ _
    | add x y hx hy =>
      simp only [map_add, Finset.sum_add_distrib]
      rw [← hx, ← hy]
  rw [key z, key z']
  exact Finset.sum_congr rfl fun w _ => by rw [h w]

end Groups

end GlobalTheory.AutFunCompare
