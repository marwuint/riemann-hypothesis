import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.DiscreteGroups.GlobalIrreducibility.DzRankBound

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

theorem le_of_sigmaEquiv {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) : d a ≤ n := by
  have h1 := Fintype.card_le_of_injective _ (sigma_mk_injective (β := fun a => Fin (d a)) (i := a))
  simpa [Fintype.card_congr e] using h1

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end DiscreteGroups.sglob.DzType.Rt

end
