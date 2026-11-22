import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColength
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := _root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k H G g hg
  have hpG := ((_root_.GlobalTheory.Dieu.isog_basics p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := _root_.GlobalTheory.Dieu.hasLogDeg_comp_le p k G H G q g e e' _ he he' hpG
  have h1 := _root_.GlobalTheory.Dieu.le_length_coker_of_hasLogDeg p T k G H q e hq' he
  have h2 := _root_.GlobalTheory.Dieu.le_length_coker_of_hasLogDeg p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := _root_.GlobalTheory.Dieu.isog_finrank_omega p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := _root_.GlobalTheory.Dieu.isog_finrank_omega p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := _root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
