import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SatakeDualWeyl.DefsCS

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lbVec (k : ℕ) (pz : 𝓞 E) (i : Fin k) : Fin k → E :=
  Pi.single i (if i.1 = 0 then (pz : E) else 1)

def LbOf (k : ℕ) (pz : 𝓞 E) : Submodule (𝓞 E) (Fin k → E) :=
  Submodule.span (𝓞 E) (Set.range (lbVec k pz))

structure SplitAt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) where
  φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)
  alg : ∀ c : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] c) = (c, c)
  int : ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F
  ori : Valued.v (φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1

structure Par (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) where
  σ : E →ₐ[F] E
  J : Matrix (Fin k) (Fin k) E
  gp : Fin 2 → ℕ
  T : ℕ
  pz : 𝓞 E
  a : Fin 2 → E

namespace Par

variable {k : ℕ} (P : Par F E k)

def Lb : Submodule (𝓞 E) (Fin k → E) := LbOf k P.pz

def Ld : Submodule (𝓞 E) (Fin k → E) := Submodule.span (𝓞 E) (dualSet (P.σ : E →+* E) P.J P.Lb)

def LbV (v : HeightOneSpectrum (𝓞 F)) : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) P.Lb

def LdV (v : HeightOneSpectrum (𝓞 F)) : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) P.Ld

def pzV (v : HeightOneSpectrum (𝓞 F)) : intV E v :=
  ⟨((P.pz : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F), Subring.subset_closure (Or.inl ⟨⟨_, ⟨P.pz, rfl⟩⟩, rfl⟩)⟩

def fKer (v : HeightOneSpectrum (𝓞 F)) : Submodule (intV E v) (P.LdV v) :=
  (P.LbV v).comap (P.LdV v).subtype ⊔ LinearMap.range (P.pzV v • (LinearMap.id : P.LdV v →ₗ[intV E v] P.LdV v))

abbrev fM (v : HeightOneSpectrum (𝓞 F)) : Type := P.LdV v ⧸ P.fKer v

def fT (v : HeightOneSpectrum (𝓞 F)) : P.LdV v →ₗ[intV E v] P.fM v := (P.fKer v).mkQ

abbrev Splits : Type :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (P.gp i : 𝓞 F) ∈ v.asIdeal → SplitAt P.σ v (P.a i)

def iwPre (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) :
    Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)) :=
  UPts P.σ P.J (v.adicCompletion F) ⊓ (iwU F k v).comap (bc ((RingHom.fst _ _).comp φ.toRingHom))

open Classical in

def Uloc (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)) :=
  if (P.T : 𝓞 F) ∈ v.asIdeal then levelVL P.σ P.J v P.Lb ⊓ stabFun _ (P.fT v)
  else if h0 : (P.gp 0 : 𝓞 F) ∈ v.asIdeal then P.iwPre v (S 0 v h0).φ
  else if h1 : (P.gp 1 : 𝓞 F) ∈ v.asIdeal then P.iwPre v (S 1 v h1).φ
  else levelVL P.σ P.J v P.Lb

abbrev GA : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := UPts P.σ P.J (FiniteAdeleRing (𝓞 F) F)

def U (S : P.Splits) : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  P.GA ⊓ ⨅ v : HeightOneSpectrum (𝓞 F), (P.Uloc S v).comap (bc (prV (E := E) v))

end Par

end Gen

end Formalism.MainNotions.Gaps.LG

end
