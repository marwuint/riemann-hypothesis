import Formalism.LocalToGlobal.ProjectiveLattices.PerFrLact

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem smul_coord (x : 𝓞 E) (w : Fin r → E) (a : Fin r) : (x • w) a = (x : E) * w a := by
  simp [Algebra.smul_def]

end Lat

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G (c • u) w = (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G u (c • w) = cc (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Herm

end Formalism.L2.Pj
