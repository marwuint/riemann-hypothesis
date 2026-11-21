import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OmegaDensity

noncomputable section

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

variable (R : Type) [CommRing R] [Algebra F R]

def sigR (σ : E →ₐ[F] E) : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (inclR R)

def HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (GL (Fin M) (R ⊗[F] E)) :=
  HcS.UG.UJ (sigR R σ) (JR R J)

end Alg

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)

scoped instance measTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    MeasurableSpace (R ⊗[F] E) := borel (R ⊗[F] E)

def HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Type := HR R σ J

variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

instance : Group (HA R σ J) := inferInstanceAs (Group (HR R σ J))
instance [TopologicalSpace R] : TopologicalSpace (HA R σ J) :=
  inferInstanceAs (TopologicalSpace (HR R σ J))
instance [TopologicalSpace R] : MeasurableSpace (HA R σ J) := borel (HA R σ J)

def HA.mat (h : HA R σ J) : GL (Fin M) (R ⊗[F] E) := let h' : HR R σ J := h; h'.1

end Top

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev AF := AdeleRing (𝓞 F) F

abbrev Ainf := InfiniteAdeleRing F

abbrev Af := FiniteAdeleRing (𝓞 F) F

end Adeles

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

section AdeleAnalysis

variable {F : Type} [Field F] [NumberField F]

scoped instance measAF : MeasurableSpace (AF F) := borel _
scoped instance measAinf : MeasurableSpace (Ainf F) := borel _
scoped instance measAf : MeasurableSpace (Af F) := borel _

variable (F)

end AdeleAnalysis

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes

end HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes
