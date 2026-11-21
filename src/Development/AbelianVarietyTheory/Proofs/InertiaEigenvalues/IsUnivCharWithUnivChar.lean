import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet

namespace GlobalTheory.UnivChar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

section Chosen

def IsUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ i Q M, Y.delU i Q M = GalChar.delU D.host X.cc (X.l i) Q M

def withUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => GalChar.delU D.host X.cc (X.l i) Q M
    delU_unr := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).1
    delU_l := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.1
    delU_anti := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.1
    delU_open := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.1
    delU_res := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.1
    delU_conj := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.1 }

end Chosen

section Family

variable (X) in

abbrev Fam (i : X.Tw) (M : ℕ) : Type := PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))

def admitted (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (P : PlE D.host) : Prop :=
  P ∉ S ∧ IsSplitPl D.host P ∧ DecV N P ≤ H

variable {i : X.Tw} {M : ℕ} (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (d : Fam X i M)

open Classical in

def setChar (T : Set (PlE D.host)) : GE N →* Multiplicative (ZMod (X.l i ^ M)) :=
  if h : ∃ v, v ∈ T ∧ admitted H S v then d h.choose else 1

open Classical in

def famCoord (Q : Finset (PlE D.host)) (P : PlE D.host) : GE N →* Multiplicative (ZMod (X.l i ^ M)) :=
  if GalChar.pair D.host P ⊆ ↑Q then setChar H S d (GalChar.pair D.host P) else 1

def famDel (Q : Finset (PlE D.host)) : GE N →* Multiplicative (DelQM D.host (X.l i) Q M) :=
  delAll X i M fun P : ↥Q => famCoord H S d Q P.1

theorem famDel_apply (Q : Finset (PlE D.host)) (σ : GE N) (P : ↥Q) :
    Multiplicative.toAdd (famDel H S d Q σ) P = Multiplicative.toAdd (famCoord H S d Q P.1 σ) := rfl

variable {H S d}

end Family

theorem delUTie_of_isUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : K1 X → IsUnivChar Y → DelUTie Y :=
  fun hK hY => GalChar.delUTie_of_exists Y hY hK

end GlobalTheory.UnivChar

end
