import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.DiscOfCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR UpperTheory.V.TR Topology
open GlobalTheory.CuspRep (Af GA Ad finGL finId pFin sFin cornerGL corner ratGL chiDet)
open private orb orb_comm annPart exists_type decomp continuous_pInf from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
open private UpperTheory.V.Lit.JL.abs_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.DiscOfCusp

namespace UpperTheory.V.Lit.UnitaryTwistAlt

section Scal

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

private abbrev sc (a : ℕ) (y : Rˣ) : GL (Fin a) R := GeneralLinearGroup.scalar (Fin a) y

end Scal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private def Scal (π : CuspSub F a) (z : Ideles F) : Prop := ∃ c : ℂ, ∀ φ ∈ π.V, rt F a (sc a z) φ = c • φ

private theorem Scal.mul {π : CuspSub F a} {z z' : Ideles F} (h : Scal π z) (h' : Scal π z') : Scal π (z * z') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c' * c, fun φ hφ => ?_⟩
  rw [sc, map_mul, map_mul, Module.End.mul_apply, hc' φ hφ, map_smul, hc φ hφ, smul_smul]

end UpperTheory.V.Lit.UnitaryTwistAlt

