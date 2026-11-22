import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapPderiv
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroup
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtension
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsHodgeTateDatumPolarisedAbelianCharacters
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataUnramifiedLengthBoundStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJ
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentCharts

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem unramified_companion_chart_characters : ∀ (p : ℕ) [Fact p.Prime], UpFSt p := by
  intro p hp T _ _ _ _ _ hT hpT G _ _ D A U d F x hx hp2 OE _ _ _ _ _ _ _ io oD oA hlin hdisc act hact
    C _ _ _ v O _ _ hv _ hO _ _ iota hio w _ t _ hfrob r W hW j
  obtain ⟨X, hX, hXr⟩ := _root_.GlobalTheory.ChF.nilChart_of_isChartJ T G U.smooth d F x hx
  have hreadG := hXr OE io act hact
  obtain ⟨FB, XB, hXB⟩ := _root_.GlobalTheory.ChF.exists_nilChart T D.toPre.P.A D.toPre.P.g D.toPre.P.smoothDim
  have hB : ∀ a : OE, ∃ φ, Reads XB XB (oD.onB.act a) φ := fun a =>
    _root_.GlobalTheory.ChF.exists_reads T _ _ _ _ _ _ XB XB hXB hXB _ (oD.onB.hom a)
  choose αB hαB using hB
  obtain ⟨rk, J, Q, hext, heq⟩ := _root_.GlobalTheory.unif_extSer_equivariant T _ D A G U d _ F FB X XB hX hXB
  obtain ⟨N, hN⟩ := heq OE io oD oA hlin act.act αB hreadG hαB
  obtain ⟨hlaw, hlinmap, hextmap⟩ := _root_.GlobalTheory.ChF.changeCoeff_law_lin_extSer T O iota
  obtain ⟨F', hF'⟩ := hlaw d F
  obtain ⟨FB', hFB'⟩ := hlaw _ FB
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.ChF.linPart_act_ringHom T d F OE act O iota
  have hFH : FH p F'.F := by
    intro k
    rw [hF']
    obtain ⟨h1, h2, -, h4⟩ :=
      GlobalTheory.FormalTorsion.fhSt p T hpT G D A U d F x hx C v O hv iota hio k
    exact ⟨h1, h2, h4⟩
  have hext' : ExtSer F'.F FB'.F (fun j => MvPowerSeries.map iota (J j))
      (fun j => MvPowerSeries.map iota (Q j)) := by
    rw [hF', hFB']
    exact hextmap _ _ _ F FB J Q hext
  have hht := _root_.GlobalTheory.ChF.exists_htd_characters_base p C v O hv T iota D.toPre.P _ rfl OE oD.onB FB XB hXB αB hαB
  rw [← hFB'] at hht
  obtain ⟨cp, hset, H, B, m, u, hu, hdat⟩ := _root_.GlobalTheory.ChF.exists_linDat_of_extSer p C v O hv OE d _ rk F' FB' _ _ hext' hFH ρ N
    (fun a j => MvPowerSeries.map iota (αB a j))
    (fun a => by
      rw [hlinmap, hlinmap, (hρ a).2, ← Matrix.map_mul, ← Matrix.map_mul, (hN a).1])
    (fun a => by
      rw [hlinmap, (hρ a).2, ← Matrix.map_mul, (hN a).2, Matrix.map_mul, Matrix.map_map]
      congr 2
      ext z
      simp)
    hht
  have hρ' : (ρ : OE → Matrix (Fin d) (Fin d) O) = fun a => linPart (actMap iota act a) :=
    funext fun a => (hρ a).1
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.T.linearData_unramified_length_bound p C v O hv OE cp hset _ H d rk m _ B ρ N _ hdat hp2 hdisc w t hfrob r W
    (fun τ => by rw [hρ']; exact (isEigBasis_iff _ _ _).1 (hW τ)) j
  refine ⟨xs, ⟨m, u, ?_, hxs⟩, hle⟩
  rw [← hF']
  exact hu

end GlobalTheory.ChF
