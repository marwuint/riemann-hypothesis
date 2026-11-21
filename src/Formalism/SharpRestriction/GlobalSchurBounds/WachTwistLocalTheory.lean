import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

section Gen

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

instance glvModFin (i : ℕ) (v : A.vT) (c : C.cls i) : Module.Finite (A.Fv v) (M.lv i v c) :=
  Module.finite_of_finrank_pos (by rw [M.lv_rank]; exact R.N_pos i)

instance glvFintype (i : ℕ) (v : A.vT) (c : C.cls i) : Fintype (M.lv i v c) :=
  haveI : Finite (M.lv i v c) := Module.finite_of_finite (A.Fv v)
  Fintype.ofFinite _

instance glkModFin (i : ℕ) (v : A.vT) (c : C.cls i) : Module.Finite (A.Fv v) (M.lk i v c) :=
  Module.finite_of_finrank_pos (by rw [M.lk_rank]; exact R.N_pos i)

instance glkDualFintype (i : ℕ) (v : A.vT) (c : C.cls i) : Fintype (Module.Dual (A.Fv v) (M.lk i v c)) :=
  haveI : Finite (Module.Dual (A.Fv v) (M.lk i v c)) := Module.finite_of_finite (A.Fv v)
  Fintype.ofFinite _

def gUop (i : ℕ) (v : A.vT) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : M.lv i v c => M.fv i v c x = 1),
    (M.upT i v c x).toLinearMap ∘ₗ LinearMap.proj (M.up i v c x)

def gDop (i : ℕ) (v : A.vT) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (A.Fv v) (M.lk i v c) => g (M.te i v c) = 1),
    (M.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (M.dn i v c g)

def gdia (i : ℕ) (v : A.vT) (a : (A.Fv v)ˣ) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  LinearMap.pi fun c => (M.dilT i v a c).toLinearMap ∘ₗ LinearMap.proj (M.dil i v a c)

def gNm (i : ℕ) (v : A.vT) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) := ∑ a : (A.Fv v)ˣ, gdia M i v a

def gMramI (i : ℕ) : Submodule ℂ (C.cls i → C.Y i → ℂ) := M.Fi i ⊓ ⨅ v, LinearMap.ker (gNm M i v)

def gVV (tp : Finset Tau) (w : Pl.Pl) : Finset A.vT :=
  if M.seenP w then Finset.univ.filter (fun v => M.tauOf w v ∈ tp) else ∅

def gUprod (tp : Finset Tau) (i : ℕ) (w : Pl.Pl) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  (gVV M tp w).toList.foldr (fun v g => (gUop M i v).comp g) LinearMap.id

def gInto {i j : ℕ} (w : Pl.Pl) (f : (C.cls i → C.Y i → ℂ) → (C.cls j → C.Y j → ℂ))
    (X : Submodule (intW Pl w) (M.lat i).V) (Y : Submodule (intW Pl w) (M.lat j).V) : Prop :=
  ∀ x ∈ X, ∃ y ∈ Y, M.emb j y = f (M.emb i x)

def gIsBfam (tp : Finset Tau) (W : Tau → ℕ) (i : ℕ) (w : Pl.Pl)
    (BV : Finset A.vT → Submodule (intW Pl w) (M.lat i).V) : Prop :=
  BV ∅ = M.S i w ∧ (∀ v, BV {v} = M.Bw i w v) ∧
  (∀ V v, v ∈ V → gInto M w (gUop M i v) (BV V) (BV (V.erase v)) ∧
    gInto M w (gDop M i v) (BV (V.erase v)) (BV V)) ∧
  (∀ V v, v ∈ V → M.tauOf w v ∉ tp →
    gInto M w (fun φ => ((A.T : ℂ) ^ (2 * W (M.tauOf w v) + R.t)) • φ) (BV V) (BV (V.erase v)))

def glossK (W : Tau → ℕ) (Cc : ℝ) : ℕ := ⌊∑ τ, (2 * (W τ : ℝ) + Cc * R.N R.m)⌋₊

def gT3withWeights (tp : Finset Tau) (W : Tau → ℕ) (Cc : ℝ) : Prop :=
  ∀ w, Pl.resChar w = A.T →
    (∀ i, i < R.m →
      (M.seenP w = false →
        gInto M w (fun φ => ((A.T : ℂ) ^ (glossK (R := R) W Cc)) • C.Klin i φ) (M.S i w) (M.S (i + 1) w)) ∧
      (M.seenP w = true → ∃ BV, gIsBfam M tp W (i + 1) w BV ∧
        gInto M w (fun φ => ((A.T : ℂ) ^ (glossK (R := R) W Cc)) • C.Klin i φ) (M.S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (W τ : ℝ) + Cc * R.f * R.N R.m ∧
        gInto M w (fun φ => ((A.T : ℂ) ^ e1) • gUprod M tp (i + 1) w (C.Klin i φ))
          (M.S i w) (M.S (i + 1) w))) ∧
    (∀ i, i ≤ R.m → M.seenP w = true → ∀ v, M.tauOf w v ∉ tp →
      gInto M w (fun φ => ((A.T : ℂ) ^ (2 * W (M.tauOf w v) + R.t)) • φ) (M.Bw i w v) (M.S i w))

def gT4with (bd : Pl.Pl → A.vT → ℝ) : Prop :=
  ∀ i, i < R.m → ∀ v : A.vT,
    (∃ c : LL,
      (∀ φ ∈ M.Fi i, gUop M (i + 1) v (C.Klin i φ) = embLL c • C.Klin i (gUop M i v φ)) ∧
      (∀ σ : LL →+* ℂ, ‖σ c‖ = (A.T : ℝ) ^ (((R.t : ℝ) + 1) / 2)) ∧
      (∀ w, Pl.resChar w = A.T → ∃ n : ℤ, Pl.val w c = ((n : ℤ) : WithTop ℤ) ∧
        |(n : ℝ)| ≤ (Pl.ramIdx w : ℝ) * bd w v)) ∧
    (∀ a, ∀ φ ∈ M.Fi i, C.Klin i (gdia M i v a φ) = gdia M (i + 1) v a (C.Klin i φ)) ∧
    ∀ φ ∈ gMramI M i, C.Klin i φ ∈ gMramI M (i + 1)

def gT4withWeights (W : Tau → ℕ) (Cc : ℝ) : Prop :=
  gT4with M (fun w v => (R.t : ℝ) + 1 + 2 * W (M.tauOf w v) + Cc * R.N R.m)

def klinIntertwinesUop : Prop :=
  ∀ i, i < R.m → ∀ v : A.vT, ∀ φ ∈ M.Fi i,
    gUop M (i + 1) v (C.Klin i φ) = ((((A.T : ℝ) ^ (((R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) • C.Klin i (gUop M i v φ)

def gadm0 : Prop := M.DnUp ∧ M.DnFv

def gRoundUp : Prop :=
  ∀ i, i ≤ R.m → ∀ v c (x : M.lv i v c), M.fv i v c x = 1 →
    ∃ e : M.lk i v (M.up i v c x) ≃ₗ[A.Fv v] M.lv i v c,
      e (M.te i v (M.up i v c x)) = x ∧
      M.dn i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap) = c ∧
      ∀ φ ∈ M.Fi i,
        M.upT i v c x (M.dnT i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap)
          (φ (M.dn i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap)))) = φ c

def gRoundDn : Prop :=
  ∀ i, i ≤ R.m → ∀ v c (g : Module.Dual (A.Fv v) (M.lk i v c)), g (M.te i v c) = 1 →
    ∃ e : M.lv i v (M.dn i v c g) ≃ₗ[A.Fv v] M.lk i v c,
      M.fv i v (M.dn i v c g) = g.comp e.toLinearMap ∧
      M.up i v (M.dn i v c g) (e.symm (M.te i v c)) = c ∧
      ∀ φ ∈ M.Fi i,
        M.dnT i v c g (M.upT i v (M.dn i v c g) (e.symm (M.te i v c))
          (φ (M.up i v (M.dn i v c g) (e.symm (M.te i v c))))) = φ c

def gTrIso : Prop :=
  ∀ i, i ≤ R.m → ∀ v c, ∀ φ ∈ M.Fi i, ∀ ψ ∈ M.Fi i,
    (∀ x : M.lv i v c, M.fv i v c x = 1 →
      M.ipV i c (M.upT i v c x (φ (M.up i v c x))) (M.upT i v c x (ψ (M.up i v c x))) =
        M.ipV i (M.up i v c x) (φ (M.up i v c x)) (ψ (M.up i v c x))) ∧
    (∀ g : Module.Dual (A.Fv v) (M.lk i v c), g ≠ 0 →
      M.ipV i c (M.dnT i v c g (φ (M.dn i v c g))) (M.dnT i v c g (ψ (M.dn i v c g))) =
        M.ipV i (M.dn i v c g) (φ (M.dn i v c g)) (ψ (M.dn i v c g))) ∧
    ∀ a : (A.Fv v)ˣ,
      M.ipV i c (M.dilT i v a c (φ (M.dil i v a c))) (M.dilT i v a c (ψ (M.dil i v a c))) =
        M.ipV i (M.dil i v a c) (φ (M.dil i v a c)) (ψ (M.dil i v a c))

def gDiaMul : Prop :=
  ∀ i, i ≤ R.m → ∀ v, ∀ φ ∈ M.Fi i,
    gdia M i v 1 φ = φ ∧ ∀ a b, gdia M i v (a * b) φ = gdia M i v a (gdia M i v b φ)

def gadmT : Prop := gRoundUp M ∧ gRoundDn M ∧ gTrIso M ∧ gDiaMul M

end Gen

section Fm

variable (D : D7) (u : D.what₂.Word)

theorem gUop_fm (i : ℕ) (v : (D.mem u).A.vT) : gUop (D.fm u) i v = Uop D u i v := rfl
theorem gDop_fm (i : ℕ) (v : (D.mem u).A.vT) : gDop (D.fm u) i v = Dop D u i v := rfl
theorem gdia_fm (i : ℕ) (v : (D.mem u).A.vT) (a) : gdia (D.fm u) i v a = dia D u i v a := rfl
theorem gMramI_fm (i : ℕ) : gMramI (D.fm u) i = MramI D u i := rfl
theorem gUprod_fm (i : ℕ) (w) : gUprod (D.fm u) (tops D) i w = Uprod D u i w := rfl
theorem general_t3_of_forms_iff (Cc : ℝ) : gT3withWeights (D.fm u) (tops D) (Wt D u) Cc ↔ PointsLemma D u Cc := Iff.rfl
theorem general_t4_of_forms_iff (Cc : ℝ) : gT4withWeights (D.fm u) (Wt D u) Cc ↔ Conclusion4 D u Cc := Iff.rfl
theorem general_t4_exact_of_forms_iff : klinIntertwinesUop (D.fm u) ↔ LevelChainUOperatorCommutation D u := Iff.rfl
theorem general_adm0_of_forms_iff : gadm0 (D.fm u) ↔ UpDownIncidenceInverse D u := Iff.rfl
theorem gadmT_fm : gadmT (D.fm u) ↔ admT D u := Iff.rfl

end Fm

section Tw

variable (D : D7)

variable {D}

variable (D)

def BaseConventionGeneral (u : D.what₂.Word) (cl : ℕ → Type)
    (lat : letI := D.host.cmStar; ∀ i, cl i → Submodule (𝓞 D.host.E) (D.sp.X i).V) (det : ∀ i, cl i → D.Dt) : Prop :=
  letI := D.host.cmStar
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧
    (∀ w, OverT D u w → ((D.fm u).seenP w = true ↔ 0 < D.what₂.places.val w (D.embE (π : D.host.E)))) ∧
    ∀ i, i ≤ D.R.m →
      ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
        (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
        (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
        ∀ c : cl i, ∃ Ln : SDLat D.host.E (D.R.N i),
          (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ lat i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (lat i c),
            y = a + D.host.conj (π : D.host.E) • b) ∧
          (QuotientGroup.mk (det i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln

theorem base_convention_general_of_forms_iff (u : D.what₂.Word) :
    BaseConventionGeneral D u (fun i => (D.mem u).C.cls i) (D.clsLat u) (D.detCls u) ↔ admB D u := Iff.rfl

variable {D}

end Tw

end Formalism.MainNotions.product_first_zeroth_parts
