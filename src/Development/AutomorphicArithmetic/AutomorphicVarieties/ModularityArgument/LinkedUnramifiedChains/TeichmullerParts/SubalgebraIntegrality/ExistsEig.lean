import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCker
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
open ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.PRep UpperTheory.V.Hi

namespace UpperTheory.V.Z.J.D.OrdinaryOrderOne

section General

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

private theorem gen_map {V' : Type} [AddCommGroup V'] [Module ℂ V'] (F : Submodule ℂ V) {f : Module.End ℂ V}
    {g : Module.End ℂ V'} (p : V →ₗ[ℂ] V') (hF : ∀ v ∈ F, f v ∈ F) (h : ∀ v ∈ F, p (f v) = g (p v)) {c : ℂ} {v : V}
    (hv : v ∈ F) (hc : v ∈ f.maxGenEigenspace c) : p v ∈ g.maxGenEigenspace c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hc
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, ?_⟩
  have key : ∀ (m : ℕ), ∀ v ∈ F, ((g - c • (1 : Module.End ℂ V')) ^ m) (p v) =
      p (((f - c • (1 : Module.End ℂ V)) ^ m) v) := by
    intro m
    induction m with
    | zero => intro v _; simp
    | succ m ih =>
      intro v hv
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      · simp [h v hv]
      · exact sub_mem (hF v hv) (F.smul_mem c hv)
  rw [key m v hv, hm, map_zero]

private theorem pow_eig {f : Module.End ℂ V} {v : V} {a : ℂ} (h : f v = a • v) (c : ℂ) (m : ℕ) :
    ((f - c • (1 : Module.End ℂ V)) ^ m) v = (a - c) ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, pow_succ, mul_smul, sub_smul]
    rfl

private theorem eq_of_gen {f : Module.End ℂ V} {v : V} {a c : ℂ} (h : f v = a • v) (h0 : v ≠ 0)
    (hv : v ∈ f.maxGenEigenspace c) : a = c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [pow_eig h] at hm
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right h0)).1

private theorem exists_eig [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V) (hE0 : E ≠ ⊥)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) : ∃ χ : G →* ℂˣ, ∃ v ∈ E, v ≠ 0 ∧ ∀ t, ρ t v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hSE, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min
    {S | S ≠ ⊥ ∧ S ≤ E ∧ ∀ t, ∀ v ∈ S, ρ t v ∈ S} ⟨E, hE0, le_rfl, hE⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, ρ t v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((ρ t).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : ρ t w = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (ρ t) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hSE, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : G →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul, mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  exact ⟨c'.toHomUnits, v, hSE hv, hv0, fun t => hc t v hv⟩

private theorem le_gen [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) (μ : G →* ℂˣ)
    (h : ∀ χ : G →* ℂˣ, ∀ v ∈ E, v ≠ 0 → (∀ t, ρ t v = (χ t : ℂ) • v) → χ = μ) (t : G) :
    E ≤ Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) := by
  rw [Submodule.eq_iSup_inf_genEigenspace (p := E) (f := ρ t) ⊤ (hE t)
    (Module.End.iSup_maxGenEigenspace_eq_top (ρ t))]
  refine iSup_le fun c => ?_
  by_cases h0 : E ⊓ Module.End.genEigenspace (ρ t) c ⊤ = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_eig ρ _ h0 fun s v hv => ⟨hE s v hv.1,
    gen_map ⊤ (ρ s) (fun _ _ => trivial) (fun v _ => by
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) trivial hv.2⟩
  rw [← h χ v hv.1 hv0 hχ, eq_of_gen (hχ t) hv0 hv.2]
  exact inf_le_right

private theorem eq_of_prod {n : ℕ} {a b : Fin n → ℂ} (hb : ∀ i, b i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, a i = ∏ i with i ≤ j, b i) (j : Fin n) : a j = b j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : (Finset.univ.filter fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (Finset.mem_filter.1 hi).2] at this
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hb i) this

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    {x : V} (hx : x ≠ 0) : ∃ μ : G →* ℂˣ, IsSmoothChar μ ∧
      ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := by
  have hT : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
    hx ((Submodule.mem_bot ℂ).1 (show x ∈ (⊥ : Subrepresentation ρ).toSubmodule by rw [h]; trivial))
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom ⊥).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hl0 (LinearMap.ext hn)
  refine ⟨μ, ?_, l, hl0, hle⟩
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : ρ g v = v := hg
    have h := hle g v
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))

end General

private theorem inj {G M J : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M)
    (hs : I.Smooth π) (a : J → G) (ha : ∀ j, a j ∈ I.P) (μ : J → ℂ) (hμ : ∀ j, μ j ≠ 0) (l : List G)
    (hz : I.z = l.prod) (hl : ∀ x ∈ l, x = 1 ∨ ∃ j, x = a j) {v : M} (hv : v ∈ fixd π I.N)
    (hv' : ∀ j, v ∈ (I.uOp π (a j)).maxGenEigenspace (μ j)) (h0 : v ∈ I.jacKer π) : v = 0 := by
  let S : M → Prop := fun v => v ∈ fixd π I.N ∧ ∀ j, v ∈ (I.uOp π (a j)).maxGenEigenspace (μ j)
  have st : ∀ x ∈ I.P, ∀ v, S v → S (I.uOp π x v) := fun x hx v hv =>
    ⟨(uOpMul G I ℂ M π _ _ hx hx v hv.1).1, fun j =>
      gen_map (fixd π I.N) (I.uOp π x) (fun w hw => (uOpMul G I ℂ M π _ _ (ha j) hx w hw).1) (fun w hw => by
        rw [(uOpMul G I ℂ M π _ _ hx (ha j) w hw).2.1, (uOpMul G I ℂ M π _ _ (ha j) hx w hw).2.1,
          I.comm x (I.P_le x hx) _ (I.P_le _ (ha j))]) hv.1 (hv.2 j)⟩
  have h1 : (1 : G) ∈ I.P ∧ ∀ v, S v → I.uOp π 1 v = 0 → v = 0 := ⟨one_mem _, fun v hv h => by
    rwa [(uOpMul G I ℂ M π _ _ (one_mem _) (one_mem _) v hv.1).2.2.1] at h⟩
  have hg : I.z ∈ I.P ∧ ∀ v, S v → I.uOp π I.z v = 0 → v = 0 := by
    rw [hz]
    refine List.prod_induction (fun x => x ∈ I.P ∧ ∀ v, S v → I.uOp π x v = 0 → v = 0) ?_ h1 ?_
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      refine ⟨mul_mem hx hy, fun v hv h => hy' v hv (hx' _ (st y hy v hv) ?_)⟩
      rw [(uOpMul G I ℂ M π _ _ hx hy v hv.1).2.1, h]
    · intro x hx
      obtain rfl | ⟨j, rfl⟩ := hl x hx
      · exact h1
      · exact ⟨ha j, fun v hv h => by_contra fun hn =>
          hμ j (eq_of_gen (h.trans (zero_smul ℂ v).symm) hn (hv.2 j)).symm⟩
  obtain ⟨m, hm⟩ := (propCker G I ℂ M π hs v hv).1 h0
  have key : ∀ (m : ℕ) (v : M), S v → (I.uOp π I.z ^ m) v = 0 → v = 0 := by
    intro m
    induction m with
    | zero => intro v _ h; simpa using h
    | succ m ih =>
      intro v hv h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hg.2 v hv (ih _ (st _ hg.1 v hv) h)
  exact key m v ⟨hv, hv'⟩ hm

section Num

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem num (ω : Fin n → kˣ →* ℂˣ) {j : ℕ} (hj : j ≤ n) :
    ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) *
      ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
        (torusChar (fun i => ω i * absPow k (((n : ℂ) - 1) / 2))
          (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = psEig ω j := by
  have hd : ∀ (t : Fin n → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have hq : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : ((nabs k (unif k) : ℝ) : ℂ) = (Nat.card 𝓀[k] : ℂ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one GlAx.unif_spec]
    simp [resCard]
  have h1 : ∀ i : Fin n, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2)
        (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
      ((ω i * absPow k (((n : ℂ) - 1) / 2)) (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) =
      (if (i : ℕ) < j then (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ else 1) *
        (Nat.card 𝓀[k] : ℂ) ^ (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) := by
    intro i
    split_ifs
    · rw [zpow_one, MonoidHom.mul_apply, Units.val_mul, mul_left_comm, ← Units.val_mul, ← MonoidHom.mul_apply,
        ← absPow_add, modExp_fin _ (fun _ => by simp), mul_assoc, val_absPow, hn,
        show ((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2 + ((n : ℂ) - 1) / 2) = (((n : ℤ) - 1 - (i : ℕ) : ℤ) : ℂ) by
          push_cast; ring, Complex.cpow_intCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hq, _root_.inv_zpow']
      congr 2
      ring
    · simp
  have hp : ∀ (s : Finset (Fin n)) (e : Fin n → ℤ),
      ∏ i ∈ s, (Nat.card 𝓀[k] : ℂ) ^ e i = (Nat.card 𝓀[k] : ℂ) ^ ∑ i ∈ s, e i := by
    intro s e
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]
  have h2 : ∑ i : Fin n, (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) = -((j * (n - j) : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < j then -((n : ℤ) - 1 - 2 * i) else 0), ← Finset.sum_filter,
      show (Finset.range n).filter (· < j) = Finset.range j by ext; simp; omega, Nat.cast_mul, Nat.cast_sub hj]
    clear h1
    generalize (n : ℤ) = N
    clear hj
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  simp only [hd, h1]
  rw [Finset.prod_mul_distrib, hp, h2, psEig, Finset.prod_filter, Nat.cast_pow, _root_.zpow_neg, zpow_natCast]
  field_simp

end Num

end UpperTheory.V.Z.J.D.OrdinaryOrderOne

open UpperTheory.V.Z.J.D

