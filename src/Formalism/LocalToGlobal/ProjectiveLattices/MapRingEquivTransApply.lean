import Formalism.LocalToGlobal.ProjectiveLattices.XcLat

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coeff_ext {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c c' : Coeff l} (h : c.F = c'.F) : c = c' := by
  obtain ⟨F, _, _, _, _⟩ := c
  obtain ⟨F', _, _, _, _⟩ := c'
  simp only at h
  subst h
  rfl

end Ext

variable {D : D7}

namespace Par

end Par

end Formalism.L2.Pj
