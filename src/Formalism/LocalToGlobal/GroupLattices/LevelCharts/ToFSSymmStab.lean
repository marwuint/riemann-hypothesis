import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfCh
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

structure StepG (I : LocId L p nV W Qq) (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  hJ : IsHerm (sp.cm.sig : E →+* E) J
  hdet : IsUnit J.det
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : FrS I Lb
  U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

variable {I : LocId L p nV W Qq} {N : ℕ}

def StepG.uGL (S : StepG I N) (v : Fin nV) :
    UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  locGL sp.cm.sig S.J S.hJ S.hdet _ (I.spl (I.plc v) (I.pl v).2) (I.spl_sig (I.plc v) (I.pl v).2)

def jPS (S : StepG I N) :
    (∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) →* UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F) :=
  (secAll F E sp.cm.sig S.J I.plc I.plc_inj).comp
    (MonoidHom.pi fun v => (S.uGL v).symm.toMonoidHom.comp (Pi.evalMonoidHom _ v))

abbrev frVS (S : StepG I N) (v : Fin nV) : GL (Fin N) ((I.plc v).adicCompletion F) := S.fr.fr (I.plc v) (I.pl v).2

def toFS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV) :
    GL (Fin (m + 1)) Qq ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  ((castGL hk Qq).trans (bcE (I.eQ v))).trans (MulAut.conj (frVS S v))

theorem toFS_symm (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV)
    (X : GL (Fin N) ((I.plc v).adicCompletion F)) :
    (toFS S hk v).symm X = (castGL hk Qq).symm ((bcE (I.eQ v)).symm ((frVS S v)⁻¹ * X * frVS S v)) := rfl

abbrev GAS (S : StepG I N) : Type := UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)

def prPS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : GAS S →* (Fin nV → GL (Fin (m + 1)) Qq) :=
  MonoidHom.pi fun v => (toFS S hk v).symm.toMonoidHom.comp
    ((bc (fstV I v)).comp ((bc (prV (E := E) (I.plc v))).comp (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)).subtype))

theorem prPS_apply (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (x : GAS S) (v : Fin nV) :
    prPS S hk x v = (toFS S hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (x : GL (Fin N) _))) := rfl

def jQS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : (Fin nV → GL (Fin (m + 1)) Qq) →* GAS S :=
  (jPS S).comp (MonoidHom.pi fun v => (toFS S hk v).toMonoidHom.comp (Pi.evalMonoidHom _ v))

def HypAtPS (S : StepG I N) : Prop :=
  ∀ (v : Fin nV) (x : GL (Fin N) (E ⊗[F] (I.plc v).adicCompletion F)),
    x ∈ UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) →
    (x ∈ S.Uloc (I.plc v) ↔
      (∀ a b, (((frVS S v)⁻¹ * bc (fstV I v) x * frVS S v : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frVS S v)⁻¹ * bc (fstV I v) x * frVS S v)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F)

end Formalism.L2.G
