import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.PolFrames

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)

theorem exists_pullSec [GrpObj G] (s : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s' : LB.Sec (LPow G L (N : ℤ) T'),
    IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s' ∧
    ∀ (z : (T' ⊗ G).left) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s', h0, h1⟩ := SectionLimit.exists_pull (K := Fin 1) s (h ▷ G).left (fun _ => (snd T' G).left)
    (fun _ => congrArg CommaMorphism.left (whiskerRight_snd h G))
  exact ⟨s', fun j => h0 j _, fun z J hJ => (h1 _ _ z J hJ).trans (by rw [Category.id_comp])⟩

theorem sval_of_isPullSec [GrpObj G] {s : LB.Sec (LPow G L (N : ℤ) T)} {s' : LB.Sec (LPow G L (N : ℤ) T')}
    (hs : IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) s s') (z : (T' ⊗ G).left) (J) (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s' (𝟙 _) z J =
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s (h ▷ G).left z J := by
  obtain ⟨s'', h0, h1⟩ := exists_pullSec G L N h s
  obtain rfl : s' = s'' := SecOps.sec_ext fun j => (hs j).trans (h0 j).symm
  exact h1 z J hJ

theorem lin_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i))
    (c : Fin n → Γ(T'.left, ⊤)) (s : LB.Sec (LPow G L (N : ℤ) T')) :
    Lin G L N h b c s ↔ ∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T') = SecM.ofSec G s := by
  let σ := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b'
  have ev : ∀ j, (∑ i, c i • (SecM.ofSec G (b' i) : SecM G L N T')).1 j = σ.f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hv : Lin G L N h b c σ := fun z J hJ => by
    rw [SectionScalarValuation.sval_lin (s := σ) (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (sval_of_isPullSec G L N h (hb i) z J hJ)
    exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  constructor
  · intro H
    refine Subtype.ext (funext fun j => (ev j).trans ?_)
    exact sec_ext_val hL (fun y J hJ => (hv y J hJ).trans (H y J hJ).symm) j
  · intro H
    obtain rfl : s = σ := SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val H) j).symm.trans (ev j)
    exact hv

theorem basisAlong_iff [GrpObj G] (hL : L.IsLB) {n : ℕ} {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow G L (N : ℤ) T')} (hb : ∀ i, IsPullSec G L N (h ▷ G) (whiskerRight_snd h G) (b i) (b' i)) :
    BasisAlong G L N h b ↔
      LinearIndependent Γ(T'.left, ⊤) (fun i => (SecM.ofSec G (b' i) : SecM G L N T')) ∧
        Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec G (b' i) : SecM G L N T')) = ⊤ := by
  unfold BasisAlong
  simp only [lin_iff G L N h hL hb]
  constructor
  · intro H
    refine ⟨Fintype.linearIndependent_iffₛ.2 fun c c' e i => ?_, eq_top_iff.2 fun x _ => ?_⟩
    · exact congrFun ((H (SecM.toSec G (∑ i, c' i • (SecM.ofSec G (b' i) : SecM G L N T')))).unique e rfl) i
    · exact (Submodule.mem_span_range_iff_exists_fun _).2 (H (SecM.toSec G x)).exists
  · rintro ⟨hli, hsp⟩ s
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : SecM.ofSec G s ∈ ⊤))
    exact ⟨r, hr, fun r' hr' => funext fun i => Fintype.linearIndependent_iffₛ.1 hli _ _ (hr'.trans hr.symm) i⟩

theorem exists_local_basisAlong (hS : SecBaseChangeSt) [IsLocallyNoetherian S] (P : PolAV S) (hN : 1 ≤ N) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk V.ι)),
      ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ V.ι) ⟶ Over.mk V.ι) b := by
  obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
  have key : ∀ f : V.toScheme ⟶ S, (overRes (T := baseOver S) V).hom = f →
      ∃ b : Fin (N ^ P.g) → LB.Sec (LPow P.A P.L (N : ℤ) (Over.mk f)), ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ V.toScheme),
        BasisAlong P.A P.L N (Over.homMk χ rfl : Over.mk (χ ≫ f) ⟶ Over.mk f) b := by
    rintro _ rfl
    refine ⟨b, fun R _ χ => ?_⟩
    choose b' hb' _ using fun i => exists_pullSec P.A P.L N (homAt χ) (b i)
    exact (basisAlong_iff P.A P.L N (homAt χ) P.isLB hb').2 (hb R χ b' hb')
  exact ⟨V, hV, key V.ι (Category.comp_id _)⟩

end GlobalTheory.LN.PolFrames
end
