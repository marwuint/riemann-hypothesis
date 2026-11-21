import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace AlgT

variable (d : Data K ι Ω WT A)

def phiS (c : ι) : MvPolynomial (TVar d.D d.N) (Ω c) →+* OmS (Ω c) d.D d.N :=
  (MvPolynomial.aeval (R := Ω c) (sImg (D := d.D) (d.jc c) (d.x c))).toRingHom

def pS (c : ι) : Ideal (MvPolynomial (TVar d.D d.N) (Ω c)) := RingHom.ker (phiS d c)

instance pS_isPrime (c : ι) : (pS d c).IsPrime := RingHom.ker_isPrime _

end AlgT

open AlgT

def TrdegD (d : Data K ι Ω WT A) (c : ι) : Prop :=
  Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j =>
    ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) = d.D

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
