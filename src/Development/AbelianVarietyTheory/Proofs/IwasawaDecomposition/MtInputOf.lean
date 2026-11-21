import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsSt

theorem mtInput_of {D : D7} {cf : CharFrame D} {M : MtFam D} {ch : NChoice D} (tp : TupTied D cf ch)
    {xi : D.what₂.Tup → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (h : MtInput D M (fun μ j => cf.mu0 j * xi μ) Q) (hx : tp.xi = xi) (hQ : ch.Q = Q) : MtInput D M tp.tup ch.Q := by
  subst hx hQ
  exact h

end GlobalTheory.HeightCounting.JumpsSt
