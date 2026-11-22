import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal

theorem exists_hodgeTate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (hπ : π.IsRegAlg) (v : InfinitePlace F) :
    ∃ H : Multiset ℤ, ∃ m, π.HasInfChar v m ∧
      H.map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
  obtain ⟨m, hm, -, hz⟩ := hπ v
  refine ⟨m.attach.map fun z => -(hz z.1 z.2).choose, m, hm, ?_⟩
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.attach_map_val m, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  have h := (hz z.1 z.2).choose_spec
  simp only [Function.comp_apply, Int.cast_neg]
  linear_combination h

theorem complexConj_algebraMap {F K : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (x : F) :
    IsCMField.complexConj K (algebraMap F K x) = algebraMap F K x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp
    (IsTotallyReal.isReal (InfinitePlace.mk (φ.comp (algebraMap F K)))))
  rw [RCLike.star_def, ← ComplexEmbedding.conjugate_coe_eq]
  exact RingHom.congr_fun h x

end GlobalTheory.RealGal

end
