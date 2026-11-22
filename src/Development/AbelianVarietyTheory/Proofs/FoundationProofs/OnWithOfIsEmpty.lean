import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeafDepthAllRunUnconditional
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndexAssembly

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.OntoChain GlobalTheory.RunDepth GlobalTheory.TraceLattice GlobalTheory.TraceClassRank
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {L : SizeData₂ D} {Pm : ParameterChoice' D L}

abbrev kap (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m) : WeightFamilies.Wt D ((i : ℕ) + 1) := kaR Tp hK ((i : ℕ) + 1)

abbrev LevelMaps (J : CoreJ D) (G : Type) (i : Fin D.R.m) : Type :=
  G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)

section Comparison₂

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (fw : FWTie J R (kap Tp hK) v₀) (F : Face D A)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J) (hr : ∀ v, LawsFull (r v).full)
  (ι : Bs.J → Fin D.R.m) (ℓ : ∀ i, LevelMaps J G i) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)

variable {Tp hK hinj EX fw F r hr ι ℓ ph} {O : OnObj S (Mir R) c}

end Comparison₂

end GlobalTheory.IndexAssembly
