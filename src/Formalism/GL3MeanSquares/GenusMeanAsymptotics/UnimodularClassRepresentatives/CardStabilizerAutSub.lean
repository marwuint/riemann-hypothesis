import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtAdjoinIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtOfSymmApply
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbitRepresentatives

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · constructor
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact hLat.fg.map _
    · unfold Formalism.HermitianLatticesTheory.gmap
      rw [Submodule.map_coe]
      show Submodule.span K (⇑(g : V →ₗ[K] V) '' L) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr g.surjective]
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]

end OrbitRepresentatives

end Formalism.HermitianLattices.Ext.L3
