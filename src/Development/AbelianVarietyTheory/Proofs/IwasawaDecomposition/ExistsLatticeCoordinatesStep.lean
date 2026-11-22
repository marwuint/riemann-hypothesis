import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull ev_res ev_appLE le_preimage_inf le_preimage_map le_preimage_mono)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.GrCl

section Frames

variable {X Z : Scheme.{0}} {F : X.Modules} {S : Type} [CommRing S]

def frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') : Matrix (Fin n) (Fin n') Γ(X, U) :=
  ((hm'.basis h').toMatrix (hm.basis h)).transpose

theorem sum_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (l : Fin n) :
    resM F h (m l) = ∑ l', frMat hm hm' h h' l l' • resM F h' (m' l') := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, ← hm'.basis_apply h']
  rw [Module.Basis.sum_repr, hm.basis_apply]

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Lin

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens}

def tanLin (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) : TanM x t.G →ₗ[S] (Fin n → S) where
  toFun v l := tanEv t (isTan_tv v) h (s l)
  map_add' v w := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 2 (fun i => (tv (![v, w] i)).left) (fun i => isTan_tv _) ![1, 1] _
      (isTan_tv (v + w)) ((LieMet.isComb_iff _ _ _).2 (by simp)) (s l)
    simpa using this
  map_smul' a v := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 1 (fun _ => (tv v).left) (fun _ => isTan_tv _) (fun _ => a) _
      (isTan_tv (a • v)) ((LieMet.isComb_iff (fun _ => v) _ _).2 (by simp)) (s l)
    simpa using this

theorem tanLin_apply (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) (l : Fin n) :
    tanLin t h s v l = tanEv t (isTan_tv v) h (s l) := rfl

theorem tanEv_sum_smul (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ l, a l • s l) = ∑ l, ev x V h (a l) * tanEv t hv h (s l) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have := tanEv_smul t hv h 0 0
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tanEv_add, tanEv_smul, ih]; rfl

theorem tanLin_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ x' ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) :
    tanLin t h' s (tanPull φ e v) = φ ∘ tanLin t h s v := by
  subst e
  exact funext fun l => GlobalTheory.LocM.tanEv_baseChange E H X t S x V h _ (isTan_tv v) S' φ _ h' (s l)

theorem tanLin_injective (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) {U : X.Opens} (e : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hs : VB.IsFrame fun l => resM _ e (s l)) : Function.Injective (tanLin t h s) := fun v w hvw =>
  tan_ext ((GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x U hU n _ hs (tanLin t h s w)).unique
    ⟨isTan_tv v, fun l => (tanEv_resM t _ hU e _).trans (congrFun hvw l)⟩
    ⟨isTan_tv w, fun l => tanEv_resM t _ hU e _⟩)

end Lin

end GlobalTheory.GrCl
