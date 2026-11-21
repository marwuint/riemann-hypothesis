import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Reading (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ) where

  Rg : Subring (A c)
  w_mem : ∀ j, d.w j c ∈ Rg
  rd : Rg →+* (Frame X.Ψ r → ℂ)

  WE : AddSubgroup WT
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ r

  Gen : Set (Frame X.Ψ r)
  Gen_sub : Gen ⊆ X.dom
  Gen_dense : X.dom ⊆ closure Gen
  pt : Frame X.Ψ r → (Ω c →+* ℂ)
  pt_mem : ∀ x ∈ Gen, pt x ∈ PT (Ω := Ω c) sg
  pt_onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x ∈ Gen, pt x = P

  w_nz : ∀ x ∈ X.dom, ∃ j, rd ⟨d.w j c, w_mem j⟩ x ≠ 0
  sec : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → X.IsSec (wt ⟨G, hG⟩) (rd ⟨f, hf⟩)
  inj : ∀ G, ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → (∀ x ∈ X.dom, rd ⟨f, hf⟩ x = 0) → f = 0
  norm : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → ∀ x ∈ Gen,
    X.pnorm (wt ⟨G, hG⟩) (rd ⟨f, hf⟩) x = d.nrm c G f (pt x)
  ratio_rd : ∀ G, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 → ∀ x ∈ Gen,
    rd ⟨f, hf⟩ x = pt x (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x

  Gen_inv : ∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x
  orbit_inj : ∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x' = lact γ (rmul x b)

  Gen_max : ∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Ω c) sg,
    (∀ G ∈ WE, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 →
      rd ⟨f, hf⟩ x = P (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P

  bir : ∀ a : Ω c, ∃ (G : WT) (f p : A c), f ∈ Rg ∧ p ∈ Rg ∧ f ∈ 𝒜 c G ∧ p ∈ 𝒜 c G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin K (Set.range fun j => d.w j c) ∧ a = ratio (Ω := Ω c) f p

  coordAt : ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    rd ⟨d.w j0 c, w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      rd ⟨d.w (jj k) c, w_mem (jj k)⟩ (cpt X x z) / rd ⟨d.w j0 c, w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0

structure BeData (d : Data K ι Ω WT A) (c : ι) {r : ℕ} {X : FD.Data E r} {sg : K →+* ℂ}
    (R : Reading (𝒜 := 𝒜) d c X sg) where
  k : ℕ
  be : A c
  be_mem : be ∈ R.Rg
  be_in : be ∈ 𝒜 c (k • d.wL)
  be_ne : be ≠ 0
  w_pos : ∀ x ∈ X.dom, 0 < ∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2
  be1 : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (R.wt ⟨k • d.wL, R.WE.nsmul_mem R.wL_mem k⟩) (R.rd ⟨be, be_mem⟩) x ≤
    C * (∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2) ^ ((k : ℝ) / 2)
  be2 : ∀ δ : ℝ, 0 < δ → ∃ Cs : Set (Frame X.Ψ r), IsCompact Cs ∧ Cs ⊆ X.dom ∧
    ∀ x ∈ X.dom, δ * (∑ j, X.pnorm (R.wt ⟨d.wL, R.wL_mem⟩) (R.rd ⟨d.w j c, R.w_mem j⟩) x ^ 2) ^ ((k : ℝ) / 2) ≤
      X.pnorm (R.wt ⟨k • d.wL, R.WE.nsmul_mem R.wL_mem k⟩) (R.rd ⟨be, be_mem⟩) x →
      ∃ y ∈ Cs, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul y b)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
