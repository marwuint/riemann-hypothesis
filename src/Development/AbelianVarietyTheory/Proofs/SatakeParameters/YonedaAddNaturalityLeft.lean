import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

namespace GlobalTheory.Et.H0

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem sh : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)]
  have h : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf R)
  have h2 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1}) := by
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor _) h
  exact h2

def yonedaAdd (X : Scheme.{0}) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) ≃+ P.obj (op X) where
  toEquiv := (((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P).trans
    uliftYonedaEquiv
  map_add' _ _ := rfl

def eAdd (X : Scheme.{0}) : H R 0 X ≃+ C(X, R) :=
  (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R)).trans <|
  ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homAddEquiv _ (coef R)).trans <|
  (yonedaAdd R X (coef R).obj).trans <|
  ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift)

theorem eAdd_smul (X : Scheme.{0}) (r : R) (x : H R 0 X) : eAdd R X (r • x) = r • eAdd R X x := by
  have h1 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x) =
      ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x :=
    (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (freeOn R).obj X) (Y := coef R)).map_smul (ULift.up r) x
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x))))) =
    r • AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x))))
  rw [h1]
  have h2 : yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
      (ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) =
      ULift.up r • yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) := rfl
  rw [h2]
  exact (congrArg AddEquiv.ulift (LinearEquiv.map_smul (((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv) (ULift.up r) _)).trans rfl

def e (X : Scheme.{0}) : H R 0 X ≃ₗ[R] C(X, R) :=
  { eAdd R X with map_smul' := eAdd_smul R X }

end GlobalTheory.Et.H0
