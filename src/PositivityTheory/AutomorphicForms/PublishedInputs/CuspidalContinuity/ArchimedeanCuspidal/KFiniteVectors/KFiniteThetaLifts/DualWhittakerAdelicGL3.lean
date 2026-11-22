import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.AdmInv
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.LocalFunctionalEquationGL3GL2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable {K : Type} [Field K] [NumberField K]

def nrm (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : (Kv K w)ˣ →* (Qv v)ˣ :=
  Units.map (Algebra.norm (Qv v) : Kv K w →* Qv v)

structure IsBC (D : Dat) (DK : DatK K) : Prop where
  k : DK.k = D.k
  nu : ∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], DK.ν w = (D.ν v).comp (nrm v w)
  bad : ∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal],
    w ∈ DK.bad ↔ (v ∈ D.bad ∨ w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1)

def cAt (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : (Qv v)ˣ →* ℂˣ :=
  (localChar c w).comp (Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom)

end Ad3.K.QuadraticBaseChangeGL3
