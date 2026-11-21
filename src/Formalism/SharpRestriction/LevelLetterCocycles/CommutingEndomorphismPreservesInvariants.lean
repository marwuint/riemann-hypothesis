import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

namespace Idx

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section BaseChange

variable {R R' W W' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W']

def ext (R' : Type) {R W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] (ι : W →ₗ[R] W') (N : Submodule R W) :
    Submodule R' W' :=
  Submodule.span R' (ι '' N)

variable {ι : W →ₗ[R] W'}

variable (hι : IsBaseChange R' ι)

def th (P : Submodule R W) : R' ⊗[R] P →ₗ[R'] W' :=
  hι.equiv.toLinearMap ∘ₗ P.subtype.baseChange R'

variable {ϖ : R} {ϖ' : R'} {u : R'ˣ} {e : ℕ}

end BaseChange

end Idx

namespace Idx

end Idx

namespace Idx

end Idx

instance neZero_g (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

instance finite_levelGroup (N : NData D.R D.host D.what₂) : Finite (G0g N) := by
  unfold G0g
  infer_instance

def repG (i : X.Tw) (j : ℕ) (b : Bool) : Representation (FractionRing (X.O i)) (G0g N) (Y.Fm i j b) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)

theorem repG_apply (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    repG Y i j b g x = Y.actG i j b g x := rfl

theorem eG_eq (i : X.Tw) (j : ℕ) (b : Bool) : eG Y i j b = (repG Y i j b).asAlgebraHom (Y.eAlg i b) := rfl

theorem mem_typeSubspace_iff_unipotent_character {i : X.Tw} {j : ℕ} {b : Bool} (x : Y.Fm i j b) :
    x ∈ Fm0 Y i j b ↔ ∀ u : Y.U, Y.actG i j b u x =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  unfold Fm0
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]

theorem card_ne_zero (i : X.Tw) [CharZero (FractionRing (X.O i))] :
    ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 :=
  Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'

section Lat

open Formalism.IrreducibleCountingLemmas

theorem sIdx_eq {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (l : ℕ) (M N' : Submodule R W) :
    sIdx l M N' = (TW.sIdx M N' : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  unfold sIdx lenR TW.sIdx TW.relLen
  push_cast
  rw [sub_div]

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {U : Type} [AddCommGroup U]
  [Module R U]

abbrev LocV (V : Submodule R U) : Type := LocalizedModule (nonZeroDivisors R) ↥V

def toLoc (V : Submodule R U) : ↥V →ₗ[R] LocV V := LocalizedModule.mkLinearMap (nonZeroDivisors R) ↥V

instance isLoc_toLoc (V : Submodule R U) : IsLocalizedModule (nonZeroDivisors R) (toLoc V) :=
  inferInstanceAs (IsLocalizedModule (nonZeroDivisors R)
    (LocalizedModule.mkLinearMap (nonZeroDivisors R) ↥V))

end Lat

section BC

open Formalism.IrreducibleCountingLemmas

variable {O : Type} [CommRing O] [IsDomain O] {W : Type} [AddCommGroup W] [Module O W]
  [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W]

variable {Ok O' : Type} [CommRing Ok] [CommRing O'] [Algebra O Ok] [Algebra O O'] [Algebra Ok O']
  [IsScalarTower O Ok O']

variable (O W Ok O') in

abbrev rho : Ok ⊗[O] W →ₗ[O] O' ⊗[O] W :=
  LinearMap.rTensor W (IsScalarTower.toAlgHom O Ok O').toLinearMap

end BC

section Tw

open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt PsiOk)

theorem TwOK_inv {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : TwOK i k Q ψ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hk : (ψ⁻¹).ker = ψ.ker := by
    ext g
    simp [MonoidHom.mem_ker]
  refine ⟨h1, h2, by rw [hk]; exact h3, ?_, ?_, ?_, ?_⟩
  · intro g g' hg
    simp only [MonoidHom.inv_apply]
    rw [h4 g g' hg]
  · intro g
    rw [MonoidHom.inv_apply]
    exact Subgroup.inv_mem _ (h5 g)
  · intro v A hA
    rw [← h6 v A hA]
    simp
  · intro v hv A' hA' σ hσ
    rw [MonoidHom.inv_apply, h7 v hv A' hA' σ hσ, inv_one]

theorem TwOK_psiAt {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (b : Bool) (h : TwOK i k Q ψ) : TwOK i k Q (psiAt b ψ) := by
  cases b
  · exact TwOK_inv h
  · exact h

theorem TwOK_of_PsiOk {i : X.Tw} {A Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}
    (h : PsiOk i A Q k' ψ') : TwOK i k' Q (ψ'.comp (X.art i Q)) := by
  classical
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun P hP => (h1 P hP).1, (Finset.disjoint_union_right.1 h2).1, h4, h5, h6, h7, h8⟩

end Tw

instance charZero_K (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) : CharZero (FractionRing (D.ntw.O i)) :=
  (D.nth.iC i).charZero

end Formalism.MainNotions.IntegralHeckeForms

end
