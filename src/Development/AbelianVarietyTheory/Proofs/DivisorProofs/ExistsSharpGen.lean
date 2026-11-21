import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.SiegLev GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegSharpCover

theorem smoothDim {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) (hu : IsUnit (k : o)) : SmoothOfRelativeDimension h c.A.hom := by
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ S := spMap (algebraMap κ K) ≫ S.fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast (Spec.preimage (x ≫ s)).hom k
    rw [← this]
    exact (hu.map _).ne_zero
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (SiegDim.dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegSharpCover

namespace GlobalTheory.SiegSharpCover

end GlobalTheory.SiegSharpCover
