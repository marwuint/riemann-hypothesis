import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLawsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Pre

variable (B : Pre)

theorem splitsC_level {p : ℕ} (hp : p ∈ B.host.levelPrimes) : SplitsC B.host.E p :=
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem splitsC_g (k : Fin 2) : SplitsC B.host.E (B.host.g k) := B.splitsC_level (B.host.g_level k)

theorem splitsC_pde : SplitsC B.host.E B.host.pde := B.splitsC_level B.host.pde_level.1

theorem splitsC_pde' : SplitsC B.host.E B.host.pde' := B.splitsC_level B.host.pde_level.2

def EvenExp : Prop := ∀ j, UpperTheory.MUQ (embPsi B.host) (fun τ : B.R.Psi => (B.hc τ).e j)

theorem nonempty_hframe (h : B.EvenExp) : Nonempty (HFrame B.host fun j τ => (B.hc τ).e j) :=
  _root_.GlobalTheory.nonempty_hFrame B.R B.host _ B.splitsC_g B.splitsC_pde B.splitsC_pde' (fun j τ => (B.hc τ).e_int j) h

end GlobalTheory.Mem.Pre

namespace GlobalTheory.Mem.Chr

end GlobalTheory.Mem.Chr

end
