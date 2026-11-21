import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Imports
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoPlace

theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : A) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : A) ∈ P :=
  _root_.GlobalTheory.ExistsPrimeMem.exists_prime_mem P hP n hn h

theorem exists_prime_mem_pl {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ PP.asIdeal :=
  exists_prime_mem PP.asIdeal PP.isPrime _ (fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)

end GlobalTheory.XGeoPlace

