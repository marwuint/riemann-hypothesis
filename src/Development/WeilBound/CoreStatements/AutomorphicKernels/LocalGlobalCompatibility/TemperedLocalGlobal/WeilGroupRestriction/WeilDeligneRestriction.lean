import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent
open GlobalTheory.WeilDeligne PositivityTheory.Pf1.CLGD.DescRes
open scoped Pointwise

namespace PositivityTheory.Pf1.CLGD.K

namespace WeilDeligneRestriction

section

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω}

variable (E A) in

def resIne : Ine (F := E') A →* Ine (F := E) A where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

@[simp] theorem coe_resIne (σ : Ine (F := E') A) : ((resIne E A σ : Ine (F := E) A) : G E Ω) = resG E (σ : G E' Ω) :=
  rfl

variable {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

end

end WeilDeligneRestriction

end PositivityTheory.Pf1.CLGD.K

end
