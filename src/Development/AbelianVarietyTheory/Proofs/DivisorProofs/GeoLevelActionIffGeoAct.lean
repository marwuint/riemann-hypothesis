import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Half

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem exists_half (a : Dw.La) : ∃ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ b = (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a := by
  have h : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at h
  obtain ⟨x, hx, b, hb, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  rw [map_add, show (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx, zero_add]

theorem map_mem_smul_top {I : Ideal (𝓞 E)} (f : Dw.La →ₗ[𝓞 E] Dw.La) {a : Dw.La}
    (ha : a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)) : f a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  intro h
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
  have := l.three_le
  have h2 : l.M = 0 := by exact_mod_cast h1
  omega

theorem graph_iff {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) :
    (∀ q, φ (γ q) = Y.mulVec (φ q)) ↔
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) → C a a' := by
  constructor
  · intro hg a ha a' ha' e
    rw [hC a ha a' ha', e, hg]
  · intro hg q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha, e⟩ := exists_half (l := l) x
    have ha' := map_mem_smul_top (liftLa γ) ha
    rw [← e, ← liftLa_spec]
    exact (hC a ha _ ha').1 (hg a ha _ ha' (liftLa_spec _ a))

end Half

theorem exists_coord_of {O S La : Type} [CommRing O] [CommRing S] [AddCommGroup La] [Module O La] (o : O →+* S)
    {I J : Ideal O} {M r : ℕ} (hIJ : I * J = Ideal.span {(M : O)}) (hco : I ⊔ J = ⊤) (π : S →+* O ⧸ I)
    (hπ : ∀ a, π (o a) = Ideal.Quotient.mk I a) (hπ0 : ∀ s, π s = 0 ↔ s ∈ I.map o) (ρ : La →+ (Fin r → S))
    (hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a)
    (hsur : ∀ s : Fin r → S, ∃ (a : La) (s' : Fin r → S), s = ρ a + M • s')
    (hker : ∀ a : La, (∀ i, ρ a i ∈ I.map o) → a ∈ I • (⊤ : Submodule O La)) :
    ∃ φ : (La ⧸ (I • (⊤ : Submodule O La))) ≃ₗ[O] (Fin r → O ⧸ I), ∀ y : Matrix (Fin r) (Fin r) S,
      ∀ a ∈ J • (⊤ : Submodule O La), ∀ a' ∈ J • (⊤ : Submodule O La),
        (∃ s : Fin r → S, y.mulVec (ρ a) - ρ a' = M • s) ↔
          φ ((I • (⊤ : Submodule O La)).mkQ a') = (y.map π).mulVec (φ ((I • (⊤ : Submodule O La)).mkQ a)) := by
  have hMb : (M : O) ∈ I :=
    Ideal.mul_le_left (I := I) (J := J) (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)
  have hπM : ∀ s : S, π (M • s) = 0 := fun s => (hπ0 _).2 (by
    rw [nsmul_eq_mul, ← map_natCast o]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hMb))
  have hmem : ∀ K : Ideal O, ∀ a ∈ K • (⊤ : Submodule O La), ∀ i, ρ a i ∈ K.map o := fun K a ha i => by
    refine Submodule.smul_induction_on (p := fun a => ρ a i ∈ K.map o) ha ?_ ?_
    · intro b hb x _
      rw [hlin]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  let f : La →ₗ[O] (Fin r → O ⧸ I) :=
    { toFun := fun a i => π (ρ a i)
      map_add' := fun a b => funext fun i => by simp
      map_smul' := fun b a => funext fun i => by
        rw [hlin, Pi.smul_apply, smul_eq_mul, map_mul, hπ]
        rfl }
  have hk : LinearMap.ker f = I • (⊤ : Submodule O La) := by
    ext a
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hker a fun i => (hπ0 _).1 (congrFun h i), fun h => funext fun i => (hπ0 _).2 (hmem _ a h i)⟩
  have hs : Function.Surjective f := fun x => by
    choose b hb using fun i => Ideal.Quotient.mk_surjective (x i)
    obtain ⟨a, s', e⟩ := hsur fun i => o (b i)
    refine ⟨a, funext fun i => ?_⟩
    have := congrArg π (congrFun e i)
    rw [Pi.add_apply, map_add, Pi.smul_apply, hπM, add_zero, hπ, hb] at this
    exact this.symm
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs), fun y a ha a' ha' => ?_⟩
  change _ ↔ f a' = (y.map π).mulVec (f a)
  have hv : ∀ i, ((y.map π).mulVec (f a)) i = π (y.mulVec (ρ a) i) := fun i =>
    (RingHom.map_mulVec π y (ρ a) i).symm
  constructor
  · rintro ⟨s, e⟩
    funext i
    have := congrArg π (congrFun e i)
    rw [Pi.sub_apply, map_sub, Pi.smul_apply, hπM, sub_eq_zero] at this
    rw [hv]
    exact this.symm
  · intro e
    have h1 : ∀ i, (y.mulVec (ρ a) - ρ a') i ∈ Ideal.span {(M : S)} := fun i => by
      have hb : (y.mulVec (ρ a) - ρ a') i ∈ I.map o := by
        rw [← hπ0, Pi.sub_apply, map_sub, sub_eq_zero, ← hv, ← e]
        rfl
      have hc : (y.mulVec (ρ a) - ρ a') i ∈ J.map o := by
        refine sub_mem ?_ (hmem _ a' ha' i)
        exact Ideal.sum_mem _ (t := Finset.univ) (f := fun k => y i k * ρ a k) fun k _ =>
          Ideal.mul_mem_left _ _ (hmem _ a ha k)
      have hco' : I.map o ⊔ J.map o = ⊤ := by rw [← Ideal.map_sup, hco, Ideal.map_top]
      have hi := Submodule.mem_inf.2 ⟨hb, hc⟩
      rwa [← Ideal.mul_eq_inf_of_coprime hco', ← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton,
        map_natCast] at hi
    choose s hs using fun i => Ideal.mem_span_singleton'.1 (h1 i)
    exact ⟨s, funext fun i => by rw [← hs i, Pi.smul_apply, nsmul_eq_mul, mul_comm]⟩

variable {D : D7}

section Dict

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Cong (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (κ : GA D V) (a a' : Dw.La) : Prop :=
  ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w

set_option maxHeartbeats 800000 in

theorem exists_coord (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) :
    ∃ φ : LaMod Dw l ≃ₗ[𝓞 D.host.E] (Fin r → 𝓞 D.host.E ⧸ l.Mb),
      ∀ (κ : GA D V) (h : LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        Cong V ι l.M κ a a' ↔
          φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a') =
            ((Formalism.L2.DIV.pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec
              (φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a)) := by
  obtain ⟨ρ, hlin, hsur, hker, hcong⟩ := _root_.GlobalTheory.GeoActCompare.exists_lattice_coord D V r hr β hβ Dw.La ι hι l.M (by have := l.three_le; omega)
  obtain ⟨φ, hφ⟩ := exists_coord_of (Formalism.L2.DIV.oToS D.host.F D.host.E) l.prod l.coprime
    (resI D.host.F l.Mb (half_ne_bot l)) (resI_oToS _ _) (resI_eq_zero_iff _ _) ρ hlin hsur (hker _ _ l.prod)
  refine ⟨φ, fun κ h a ha a' ha' => ?_⟩
  have h1 := hcong κ _ (Formalism.L2.DIV.frGL_pullFr β ⟨_, h⟩).symm a a'
  have h2 := hφ (Formalism.L2.DIV.pullFr β ⟨_, h⟩).1 a ha a' ha'
  have h3 := h1.trans h2
  exact h3

end Dict

end GlobalTheory.GeoActCompare
