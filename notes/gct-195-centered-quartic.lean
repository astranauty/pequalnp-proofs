import Mathlib
import PEqualNP.Gct.L171

namespace Gct195.Centered

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def distinct3 (a b c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i * b j * c k

def distinct4 (a b c d : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l
    then 0 else a i * b j * c k * d l

def pair (a b : ι → ℂ) : ℂ := ∑ i, a i * b i

private theorem distinct3_swap_first (a b c : ι → ℂ) : distinct3 a b c = distinct3 b a c := by
  unfold distinct3
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp [eq_comm, or_comm, mul_comm]

private theorem distinct3_swap_last (a b c : ι → ℂ) : distinct3 a b c = distinct3 a c b := by
  unfold distinct3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp [eq_comm, or_left_comm, mul_left_comm, mul_comm]

private theorem sum_if_outside (S : Finset ι) (f : ι → ℂ) :
    (∑ i, if i ∈ S then 0 else f i) = (∑ i, f i) - ∑ i ∈ S, f i := by
  have h (i : ι) : (if i ∈ S then 0 else f i) + (if i ∈ S then f i else 0) = f i := by
    split_ifs <;> simp
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset ι)) rfl (fun i _ => h i)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hs
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hs
  exact eq_sub_of_add_eq hs

private theorem sum_except_one (f : ι → ℂ) (i : ι) :
    (∑ j, if i = j then 0 else f j) = (∑ j, f j) - f i := by
  simpa [eq_comm] using sum_if_outside {i} f

private theorem sum_except_two (f : ι → ℂ) {i j : ι} (h : i ≠ j) :
    (∑ k, if i = k ∨ j = k then 0 else f k) = (∑ k, f k) - f i - f j := by
  have hs := sum_if_outside {i, j} f
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rw [Finset.sum_pair h] at hs
  simpa only [eq_comm, sub_sub] using hs

private theorem sum_except_three (f : ι → ℂ) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : (∑ l, if i = l ∨ j = l ∨ k = l then 0 else f l) =
      (∑ l, f l) - f i - f j - f k := by
  have hs := sum_if_outside {i, j, k} f
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk] at hs
  simpa only [eq_comm, sub_sub, add_assoc] using hs

/-- With two centred rows, the terms in the cubic distinct-column sum are
the single-column triple product and one pair moment. -/
theorem distinct3_of_two_centered (a b c : ι → ℂ) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0) :
    distinct3 a b c = 2 * (∑ i, a i * b i * c i) - (∑ i, a i) * pair b c := by
  have hinner (i j : ι) :
      (∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i * b j * c k) =
        if i = j then 0 else -(a i * c i * b j + a i * (b j * c j)) := by
    by_cases h : i = j
    · simp [h]
    · simp only [h, false_or, ite_false]
      have hf (k : ι) : (if i = k ∨ j = k then 0 else a i * b j * c k) =
          (a i * b j) * (if i = k ∨ j = k then 0 else c k) := by
        split_ifs <;> simp
      simp_rw [hf, ← Finset.mul_sum, sum_except_two c h, hc]
      ring
  have hsplit (i j : ι) : (if i = j then 0 else -(a i * c i * b j + a i * (b j * c j))) =
      -(a i * c i * (if i = j then 0 else b j) + a i * (if i = j then 0 else b j * c j)) := by
    split_ifs <;> simp
  have houter (i : ι) : (∑ j, ∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i * b j * c k) =
      2 * (a i * b i * c i) - a i * pair b c := by
    simp_rw [hinner, hsplit, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_except_one, hb]
    unfold pair
    ring
  unfold distinct3
  simp_rw [houter, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- For four centred rows the quartic is a sum over the three pairings of
the rows, minus six times the sum of the within-column products. -/
theorem distinct4_of_centered (a b c d : ι → ℂ) (ha : ∑ i, a i = 0)
    (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0) (hd : ∑ i, d i = 0) :
    distinct4 a b c d = pair a b * pair c d + pair a c * pair b d + pair a d * pair b c -
      6 * (∑ i, a i * b i * c i * d i) := by
  let A : ι → ℂ := fun i => a i * d i
  let B : ι → ℂ := fun i => b i * d i
  let C : ι → ℂ := fun i => c i * d i
  have hinner (i j k : ι) :
      (∑ l, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l
        then 0 else a i * b j * c k * d l) =
      if i = j ∨ i = k ∨ j = k then 0 else
        -(A i * b j * c k + a i * B j * c k + a i * b j * C k) := by
    by_cases hf : i = j ∨ i = k ∨ j = k
    · rcases hf with h | h | h <;> simp [h]
    · push Not at hf
      obtain ⟨hij, hik, hjk⟩ := hf
      simp only [hij, hik, hjk, false_or, ite_false]
      have hg (l : ι) : (if i = l ∨ j = l ∨ k = l then 0 else a i * b j * c k * d l) =
          (a i * b j * c k) * (if i = l ∨ j = l ∨ k = l then 0 else d l) := by
        split_ifs <;> simp
      simp_rw [hg, ← Finset.mul_sum, sum_except_three d hij hik hjk, hd]
      dsimp [A, B, C]
      ring
  have hsplit (i j k : ι) :
      (if i = j ∨ i = k ∨ j = k then 0 else
        -(A i * b j * c k + a i * B j * c k + a i * b j * C k)) =
      -((if i = j ∨ i = k ∨ j = k then 0 else A i * b j * c k) +
        (if i = j ∨ i = k ∨ j = k then 0 else a i * B j * c k) +
        (if i = j ∨ i = k ∨ j = k then 0 else a i * b j * C k)) := by
    split_ifs <;> simp
  have hcollapse : distinct4 a b c d = -(distinct3 A b c + distinct3 a B c + distinct3 a b C) := by
    unfold distinct4 distinct3
    simp_rw [hinner, hsplit, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hswap₁ := distinct3_swap_first a B c
  have hswap₂ := (distinct3_swap_last a b C).trans (distinct3_swap_first a C b)
  rw [hcollapse, hswap₁, hswap₂, distinct3_of_two_centered _ _ _ hb hc,
    distinct3_of_two_centered _ _ _ ha hc, distinct3_of_two_centered _ _ _ ha hb]
  simp only [A, B, C, pair]
  have hm₁ : (∑ i, a i * d i * b i * c i) = ∑ i, a i * b i * c i * d i :=
    Finset.sum_congr rfl fun i _ => by ring
  have hm₂ : (∑ i, b i * d i * a i * c i) = ∑ i, a i * b i * c i * d i :=
    Finset.sum_congr rfl fun i _ => by ring
  have hm₃ : (∑ i, c i * d i * a i * b i) = ∑ i, a i * b i * c i * d i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hm₁, hm₂, hm₃]
  ring

section ColumnProducts

variable {ρ : Type} [Fintype ρ]

def columnProduct (t : ρ × ι → ℂ) (j : ι) : ℂ := ∏ i, (1 + t (i, j))

private def entry (V : Submodule ℂ (ρ × ι → ℂ)) (i : ρ) (j : ι) : Module.Dual ℂ V :=
  (LinearMap.proj (i, j)).comp V.subtype

private def columnSpan (V : Submodule ℂ (ρ × ι → ℂ)) (U : Finset ι) :
    Submodule ℂ (Module.Dual ℂ V) :=
  Submodule.span ℂ {φ | ∃ j ∈ U, ∃ i : ρ, entry V i j = φ}

omit [Fintype ι] [DecidableEq ι] [Fintype ρ] in
private theorem mem_column_ker {V : Submodule ℂ (ρ × ι → ℂ)} (U : Finset ι) (x : V) :
    x ∈ (columnSpan V U).dualCoannihilator ↔ ∀ i : ρ, ∀ j ∈ U, x.1 (i, j) = 0 := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hx i j hj
    exact hx (entry V i j) (Submodule.subset_span ⟨j, hj, i, rfl⟩)
  · intro hx f hf
    have h : columnSpan V U ≤ (Module.Dual.eval ℂ V x).ker := by
      apply Submodule.span_le.2
      rintro _ ⟨j, hj, i, rfl⟩
      exact LinearMap.mem_ker.2 (hx i j hj)
    exact LinearMap.mem_ker.1 (h hf)

private theorem eval_surjective {α V : Type*} [Fintype α] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (f : α → Module.Dual ℂ V) (hf : LinearIndependent ℂ f) :
    Function.Surjective (LinearMap.pi f) := by
  classical
  let E := LinearMap.pi f
  have hk : E.ker = (Submodule.span ℂ (Set.range f)).dualCoannihilator := by
    ext x
    rw [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
    constructor
    · intro hx φ hφ
      have hs : Submodule.span ℂ (Set.range f) ≤ (Module.Dual.eval ℂ V x).ker := by
        apply Submodule.span_le.2
        rintro _ ⟨i, rfl⟩
        exact LinearMap.mem_ker.2 (congrFun hx i)
      exact LinearMap.mem_ker.1 (hs hφ)
    · intro hx
      funext i
      exact hx (f i) (Submodule.subset_span ⟨i, rfl⟩)
  have h₁ := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (Set.range f))
  have h₂ := LinearMap.finrank_range_add_finrank_ker E
  have h₃ := finrank_span_eq_card hf
  rw [hk] at h₂
  rw [h₃] at h₁
  change Module.finrank ℂ (LinearMap.range (LinearMap.pi f)) +
    Module.finrank ℂ (Submodule.span ℂ (Set.range f)).dualCoannihilator = Module.finrank ℂ V at h₂
  apply LinearMap.range_eq_top.1
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card]
  omega

/-- Rado's theorem bounds a space when the shifted products in its supported
columns sum to the size of the support. The argument works for any row count. -/
theorem finrank_lt_of_columnProducts : ∀ (n : ℕ) (C : Finset ι)
    (V : Submodule ℂ (ρ × ι → ℂ)), C.card = n → C.Nonempty →
    (∀ t ∈ V, (∀ i : ρ, ∀ j ∉ C, t (i, j) = 0) ∧
      ∑ j ∈ C, columnProduct t j = (C.card : ℂ)) → Module.finrank ℂ V < n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C V hcard hne hV
    by_contra hdim
    have hdim' := Nat.le_of_not_gt hdim
    have hHall (U : Finset ι) (hUC : U ⊆ C) (hneU : U.Nonempty) :
        U.card ≤ Module.finrank ℂ (columnSpan V U) := by
      let Kc := (columnSpan V U).dualCoannihilator
      have hf := Subspace.finrank_add_finrank_dualCoannihilator_eq (columnSpan V U)
      change Module.finrank ℂ (columnSpan V U) + Module.finrank ℂ Kc = Module.finrank ℂ V at hf
      by_cases hU : U = C
      · subst U
        have hb : Kc = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          apply (Submodule.mem_bot ℂ).2
          apply Subtype.ext
          funext ⟨i, j⟩
          by_cases hj : j ∈ C
          · exact (mem_column_ker C x).1 hx i j hj
          · exact (hV _ x.2).1 i j hj
        rw [hb, finrank_bot] at hf
        rw [hcard]
        omega
      · let K := Kc.map V.subtype
        have hK : Module.finrank ℂ K = Module.finrank ℂ Kc :=
          (Submodule.equivMapOfInjective V.subtype V.injective_subtype Kc).finrank_eq.symm
        have hlt : (C \ U).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card (Finset.sdiff_ssubset hUC hneU)
        have hsub : (C \ U).Nonempty := by
          rw [Finset.sdiff_nonempty]
          intro h
          exact hU (Finset.Subset.antisymm hUC h)
        have hSmall := ih _ hlt (C \ U) K rfl hsub (by
          intro t ht
          obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 ht
          have hzero := (mem_column_ker U x).1 hx
          obtain ⟨hSupport, hprod⟩ := hV x.1 x.2
          refine ⟨?_, ?_⟩
          · intro i j hj
            by_cases hjC : j ∈ C
            · exact hzero i j (by simpa [Finset.mem_sdiff, hjC] using hj)
            · exact hSupport i j hjC
          · have hUprod : (∑ j ∈ U, columnProduct x.1 j) = (U.card : ℂ) := by
              calc
                _ = ∑ j ∈ U, (1 : ℂ) := Finset.sum_congr rfl (fun j hj => by simp [columnProduct, hzero _ j hj])
                _ = _ := by simp
            have hsum := Finset.sum_sdiff hUC (f := fun j => columnProduct x.1 j)
            rw [hUprod, hprod] at hsum
            change (∑ j ∈ C \ U, columnProduct x.1 j) = ((C \ U).card : ℂ)
            rw [Finset.card_sdiff_of_subset hUC, Nat.cast_sub (Finset.card_le_card hUC)]
            exact eq_sub_of_add_eq hsum)
        rw [hK, Finset.card_sdiff_of_subset hUC] at hSmall
        omega
    let J := {j // j ∈ C}
    let A : J → Finset (Module.Dual ℂ V) := fun j => Finset.univ.image (fun i : ρ => entry V i j.1)
    have hA (U : Finset J) : U.card ≤
        Module.finrank ℂ (Submodule.span ℂ (⋃ j ∈ U, (A j : Set (Module.Dual ℂ V)))) := by
      let W : Finset ι := U.map (Function.Embedding.subtype _)
      have hW : W ⊆ C := by
        intro j hj
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hj
        exact a.2
      have hcardW : W.card = U.card := Finset.card_map _
      have hspan : Submodule.span ℂ (⋃ j ∈ U, (A j : Set (Module.Dual ℂ V))) = columnSpan V W := by
        congr 1
        ext φ
        simp only [Set.mem_iUnion, Finset.coe_image, Finset.coe_univ, Set.image_univ,
          Set.mem_range, Set.mem_ofPred_eq, Finset.mem_map, Function.Embedding.coe_subtype, A, W]
        constructor
        · rintro ⟨j, hj, i, rfl⟩
          exact ⟨j.1, ⟨j, hj, rfl⟩, i, rfl⟩
        · rintro ⟨_, ⟨j, hj, rfl⟩, i, rfl⟩
          exact ⟨j, hj, i, rfl⟩
      rw [hspan, ← hcardW]
      rcases W.eq_empty_or_nonempty with he | hw
      · simp [he]
      · exact hHall W hW hw
    obtain ⟨f, hfA, hfi⟩ := PEqualNP.Gct.L171 ℂ _ J A hA
    have hf (j : J) : ∃ i : ρ, entry V i j.1 = f j := by simpa [A] using hfA j
    obtain ⟨x, hx⟩ := eval_surjective f hfi (fun _ => (-1 : ℂ))
    have hxj (j : ι) (hj : j ∈ C) : columnProduct x.1 j = 0 := by
      obtain ⟨i, hi⟩ := hf ⟨j, hj⟩
      have he := congrFun hx ⟨j, hj⟩
      change f ⟨j, hj⟩ x = -1 at he
      rw [← hi] at he
      change x.1 (i, j) = -1 at he
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [he]; simp)
    have hprod := (hV x.1 x.2).2
    simp only [Finset.sum_eq_zero hxj] at hprod
    exact (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne) : (C.card : ℂ) ≠ 0) hprod.symm

end ColumnProducts

section FourRows

abbrev Mat4 (ι : Type*) := Fin 4 × ι → ℂ

def rook2 (t : Mat4 ι) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
    if a < b then t (a, j) * t (b, l) else 0

def rook3 (t : Mat4 ι) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0

abbrev row (t : Mat4 ι) (i : Fin 4) : ι → ℂ := fun j => t (i, j)

def pairingCorrection (t : Mat4 ι) : ℂ :=
  pair (row t 0) (row t 1) * pair (row t 2) (row t 3) +
  pair (row t 0) (row t 2) * pair (row t 1) (row t 3) +
  pair (row t 0) (row t 3) * pair (row t 1) (row t 2)

private theorem zeroElse_add (P : Prop) [Decidable P] (a b : ℂ) :
    (if P then 0 else a + b) = (if P then 0 else a) + (if P then 0 else b) := by
  by_cases h : P <;> simp [h]

private def distinct2 (a b : ι → ℂ) : ℂ := ∑ i, ∑ j, if i = j then 0 else a i * b j

private theorem distinct2_of_centered (a b : ι → ℂ) (hb : ∑ j, b j = 0) :
    distinct2 a b = -pair a b := by
  unfold distinct2 pair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h (j : ι) : (if i = j then 0 else a i * b j) = a i * (if i = j then 0 else b j) := by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h j), ← Finset.mul_sum, sum_except_one, hb]
  ring

private theorem rook2_as_row_pairs (t : Mat4 ι) :
    rook2 t = distinct2 (row t 0) (row t 1) + distinct2 (row t 0) (row t 2) +
      distinct2 (row t 0) (row t 3) + distinct2 (row t 1) (row t 2) +
      distinct2 (row t 1) (row t 3) + distinct2 (row t 2) (row t 3) := by
  simp (config := {decide := true}) only [rook2, distinct2, Fin.sum_univ_four, ite_true, ite_false,
    zero_add, add_zero, zeroElse_add, Finset.sum_add_distrib, add_assoc, row]
  ring

theorem rook2_of_centered (t : Mat4 ι) (h : ∀ i : Fin 4, ∑ j, t (i, j) = 0) :
    rook2 t = -(pair (row t 0) (row t 1) + pair (row t 0) (row t 2) +
      pair (row t 0) (row t 3) + pair (row t 1) (row t 2) +
      pair (row t 1) (row t 3) + pair (row t 2) (row t 3)) := by
  rw [rook2_as_row_pairs]
  simp only [distinct2_of_centered _ _ (h 1), distinct2_of_centered _ _ (h 2),
    distinct2_of_centered _ _ (h 3)]
  ring

private theorem rook3_as_row_triples (t : Mat4 ι) :
    rook3 t = distinct3 (row t 0) (row t 1) (row t 2) +
      distinct3 (row t 0) (row t 1) (row t 3) + distinct3 (row t 0) (row t 2) (row t 3) +
      distinct3 (row t 1) (row t 2) (row t 3) := by
  simp (config := {decide := true}) only [rook3, distinct3, Fin.sum_univ_four, ite_true, ite_false,
    zero_add, add_zero, zeroElse_add, Finset.sum_add_distrib, add_assoc]

theorem rook3_of_centered (t : Mat4 ι) (h : ∀ i : Fin 4, ∑ j, t (i, j) = 0) :
    rook3 t = 2 * (∑ j, (
      t (0, j) * t (1, j) * t (2, j) + t (0, j) * t (1, j) * t (3, j) +
        t (0, j) * t (2, j) * t (3, j) + t (1, j) * t (2, j) * t (3, j))) := by
  rw [rook3_as_row_triples, distinct3_of_two_centered _ _ _ (h 1) (h 2),
    distinct3_of_two_centered _ _ _ (h 1) (h 3),
    distinct3_of_two_centered _ _ _ (h 2) (h 3), distinct3_of_two_centered _ _ _ (h 2) (h 3)]
  simp only [row, h, zero_mul, sub_zero, Finset.sum_add_distrib]
  ring

private theorem distinct2_last_one (a : Fin 6 → ℂ) :
    distinct2 a 1 = 5 * ∑ j, a j := by
  unfold distinct2
  have h (j : Fin 6) : (∑ l, if j = l then 0 else a j * (1 : Fin 6 → ℂ) l) = 5 * a j := by
    simp only [Pi.one_apply, mul_one]
    rw [sum_except_one (fun _ => a j) j]
    simp [nsmul_eq_mul]
    ring
  simp_rw [h, ← Finset.mul_sum]

private theorem distinct3_last_one (a b : Fin 6 → ℂ) : distinct3 a b 1 = 4 * distinct2 a b := by
  unfold distinct3 distinct2
  have h (j l : Fin 6) :
      (∑ m, if j = l ∨ j = m ∨ l = m then 0 else a j * b l * (1 : Fin 6 → ℂ) m) =
        4 * (if j = l then 0 else a j * b l) := by
    by_cases hjl : j = l
    · simp [hjl]
    · simp only [hjl, false_or, ite_false, Pi.one_apply, mul_one]
      rw [sum_except_two (fun _ => a j * b l) hjl]
      simp [nsmul_eq_mul]
      ring
  simp_rw [h, ← Finset.mul_sum]

/-- The first three gap equations already exclude two complementary all-ones rows. -/
theorem not_both_rows_one_of_cubic_level (x : Mat4 (Fin 6))
    (hTotal : ∑ a, ∑ j, x (a, j) = 0) (h2 : rook2 x = 0) (h3 : rook3 x = 0)
    (hrow2 : row x 2 = 1) (hrow3 : row x 3 = 1) : False := by
  let a := row x 0
  let b := row x 1
  have hs : (∑ j, a j) + (∑ j, b j) + 12 = 0 := by
    rw [Fin.sum_univ_four] at hTotal
    change (∑ j, a j) + (∑ j, b j) + (∑ j, row x 2 j) + (∑ j, row x 3 j) = 0 at hTotal
    rw [hrow2, hrow3] at hTotal
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hTotal
    linear_combination hTotal
  rw [rook2_as_row_pairs, hrow2, hrow3] at h2
  rw [rook3_as_row_triples, hrow2, hrow3] at h3
  change distinct2 a b + distinct2 a 1 + distinct2 a 1 + distinct2 b 1 + distinct2 b 1 +
    distinct2 1 1 = 0 at h2
  change distinct3 a b 1 + distinct3 a b 1 + distinct3 a 1 1 + distinct3 b 1 1 = 0 at h3
  simp only [distinct3_last_one, distinct2_last_one, Pi.one_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2 h3
  have h : (480 : ℂ) = 0 := by linear_combination h3 - 8 * h2 + 60 * hs
  exact (by norm_num : (480 : ℂ) ≠ 0) h

/-!
The doubly centred slice gives a diagonal cubic and a quartic with an explicit row-pairing
term. For the general complete-intersection perspective on spaces of linear subspaces, see
Olivier Debarre and Laurent Manivel, *Sur la variété des espaces linéaires contenus dans une
intersection complète*, Math. Ann. 312 (1998), 549–574, https://www.math.ens.psl.eu/~debarre/36.pdf.
Their generic dimension theorem does not certify this fixed system. The identities below
follow by expanding the four entries in each column and using their sum-zero relation.
-/

theorem twice_rook2_of_double_centered (t : Mat4 ι)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    2 * rook2 t = ∑ j, ∑ i, t (i, j) ^ 2 := by
  have h (j : ι) : (∑ i, t (i, j) ^ 2) = -2 *
      (t (0, j) * t (1, j) + t (0, j) * t (2, j) + t (0, j) * t (3, j) +
        t (1, j) * t (2, j) + t (1, j) * t (3, j) + t (2, j) * t (3, j)) := by
    have hz := hc j
    simp only [Fin.sum_univ_four] at hz ⊢
    linear_combination (t (0, j) + t (1, j) + t (2, j) + t (3, j)) * hz
  rw [rook2_of_centered t hr]
  simp only [h, ← Finset.mul_sum, Finset.sum_add_distrib, pair]
  ring

theorem three_mul_rook3_of_double_centered (t : Mat4 ι)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    3 * rook3 t = 2 * ∑ j, ∑ i, t (i, j) ^ 3 := by
  have h (j : ι) : (∑ i, t (i, j) ^ 3) = 3 *
      (t (0, j) * t (1, j) * t (2, j) + t (0, j) * t (1, j) * t (3, j) +
        t (0, j) * t (2, j) * t (3, j) + t (1, j) * t (2, j) * t (3, j)) := by
    have hz := hc j
    simp only [Fin.sum_univ_four] at hz ⊢
    have hd : t (3, j) = -(t (0, j) + t (1, j) + t (2, j)) := by
      linear_combination hz
    rw [hd]
    ring
  rw [rook3_of_centered t hr]
  simp only [h, ← Finset.mul_sum]
  ring

theorem four_mul_rook4_of_double_centered (t : Mat4 ι)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    4 * distinct4 (row t 0) (row t 1) (row t 2) (row t 3) = 4 * pairingCorrection t -
      3 * (∑ j, (∑ i, t (i, j) ^ 2) ^ 2) + 6 * (∑ j, ∑ i, t (i, j) ^ 4) := by
  have h (j : ι) : 8 * (t (0, j) * t (1, j) * t (2, j) * t (3, j)) =
      (∑ i, t (i, j) ^ 2) ^ 2 - 2 * ∑ i, t (i, j) ^ 4 := by
    have hz := hc j
    simp only [Fin.sum_univ_four] at hz ⊢
    have hd : t (3, j) = -(t (0, j) + t (1, j) + t (2, j)) := by
      linear_combination hz
    rw [hd]
    ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => h j)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  rw [distinct4_of_centered _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3)]
  change 4 * (pairingCorrection t - 6 * (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j))) = _
  linear_combination -3 * hs

private theorem cube_moment_of_mem {V : Submodule ℂ (Mat4 ι)}
    (hV : ∀ t ∈ V, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0) ∧ rook3 t = 0)
    {t : Mat4 ι} (ht : t ∈ V) : (∑ j, ∑ i, t (i, j) ^ 3) = 0 := by
  obtain ⟨hr, hc, h3⟩ := hV t ht
  have h := three_mul_rook3_of_double_centered t hr hc
  rw [h3, mul_zero, eq_comm, mul_eq_zero] at h
  exact h.resolve_left (by norm_num)

/-- Multiplication by any direction of the doubly centred space sends it into the
annihilator for the entrywise bilinear dot product. -/
theorem triple_moment_eq_zero {V : Submodule ℂ (Mat4 ι)}
    (hV : ∀ t ∈ V, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0) ∧ rook3 t = 0)
    {x y z : Mat4 ι} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V) :
    ∑ j, ∑ i, x (i, j) * y (i, j) * z (i, j) = 0 := by
  let moment (t : Mat4 ι) : ℂ := ∑ j, ∑ i, t (i, j) ^ 3
  have h : ∀ t ∈ V, moment t = 0 := fun _ ht => cube_moment_of_mem hV ht
  have heq :
      moment (x + y + z) - moment (x + y) - moment (x + z) - moment (y + z) +
        moment x + moment y + moment z = 6 * (∑ j, ∑ i, x (i, j) * y (i, j) * z (i, j)) := by
    simp only [moment, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h _ (V.add_mem (V.add_mem hx hy) hz), h _ (V.add_mem hx hy), h _ (V.add_mem hx hz),
    h _ (V.add_mem hy hz), h _ hx, h _ hy, h _ hz] at heq
  have hSix : (6 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp (by simpa using heq.symm)).resolve_left hSix

/-!
Mixed cubic equations capture how one doubly centred direction interacts with the full level
space. For the use of tangent equations to constrain linear spaces on permanental loci, see
Melody Chan and Nathan Ilten, *Fano schemes of determinants and permanents*, Algebra & Number
Theory 9 (2015), 629–679, §3, https://msp.org/ant/2015/9-3/ant-v9-n3-p05-s.pdf.
Here the needed mixed equation follows directly from polarization and inclusion–exclusion.
-/

def mixedRook3 (x y z : Mat4 ι) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    if a = b ∨ a = c ∨ b = c then 0 else distinct3 (row x a) (row y b) (row z c)

private theorem mixedRook3_swap_first (x y z : Mat4 ι) :
    mixedRook3 x y z = mixedRook3 y x z := by
  unfold mixedRook3
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [eq_comm (a := a) (b := b), or_comm (a := a = c) (b := b = c), distinct3_swap_first]

private theorem mixedRook3_swap_last (x y z : Mat4 ι) :
    mixedRook3 x y z = mixedRook3 x z y := by
  unfold mixedRook3
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [or_left_comm (a := a = b) (b := a = c), eq_comm (a := b) (b := c), distinct3_swap_last]

private theorem mixedRook3_add_first (w x y z : Mat4 ι) :
    mixedRook3 (w + x) y z = mixedRook3 w y z + mixedRook3 x y z := by
  simp only [mixedRook3, distinct3, Pi.add_apply, add_mul, zeroElse_add, Finset.sum_add_distrib]

private theorem mixedRook3_add_second (w x y z : Mat4 ι) :
    mixedRook3 w (x + y) z = mixedRook3 w x z + mixedRook3 w y z := by
  rw [mixedRook3_swap_first w, mixedRook3_add_first,
    mixedRook3_swap_first x, mixedRook3_swap_first y]

private theorem mixedRook3_add_third (w x y z : Mat4 ι) :
    mixedRook3 w x (y + z) = mixedRook3 w x y + mixedRook3 w x z := by
  rw [mixedRook3_swap_last w x, mixedRook3_add_second,
    mixedRook3_swap_last w y, mixedRook3_swap_last w z]

private theorem mixedRook3_diagonal (t : Mat4 ι) : mixedRook3 t t t = 6 * rook3 t := by
  rw [rook3_as_row_triples]
  simp (config := {decide := true}) only [mixedRook3, Fin.sum_univ_four, ite_true, ite_false,
    zero_add, add_zero, distinct3_swap_first, distinct3_swap_last]
  ring

/-- Vanishing of the gap cubic on a subspace forces all its mixed coefficients to vanish. -/
theorem mixedRook3_eq_zero {V : Submodule ℂ (Mat4 ι)} (hV : ∀ t ∈ V, rook3 t = 0)
    {x y z : Mat4 ι} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V) : mixedRook3 x y z = 0 := by
  have h (t : Mat4 ι) (ht : t ∈ V) : mixedRook3 t t t = 0 := by
    rw [mixedRook3_diagonal, hV t ht, mul_zero]
  have hp :
      mixedRook3 (x + y + z) (x + y + z) (x + y + z) - mixedRook3 (x + y) (x + y) (x + y) -
      mixedRook3 (x + z) (x + z) (x + z) - mixedRook3 (y + z) (y + z) (y + z) +
      mixedRook3 x x x + mixedRook3 y y y + mixedRook3 z z z = 6 * mixedRook3 x y z := by
    simp only [mixedRook3_add_third,
      mixedRook3_swap_first, mixedRook3_swap_last]
    ring
  rw [h _ (V.add_mem (V.add_mem hx hy) hz), h _ (V.add_mem hx hy), h _ (V.add_mem hx hz),
    h _ (V.add_mem hy hz), h _ hx, h _ hy, h _ hz] at hp
  have hSix : (6 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp (by simpa using hp.symm)).resolve_left hSix

private theorem centered_rectangle_sum (t : Mat4 ι)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0)
    {a b : Fin 4} {j l : ι} (hab : a ≠ b) (hjl : j ≠ l) :
    (∑ c : Fin 4, ∑ m, if (a = c ∨ b = c) ∨ (j = m ∨ l = m) then 0 else t (c, m)) =
      t (a, j) + t (a, l) + t (b, j) + t (b, l) := by
  have hrow (c : Fin 4) :
      (∑ m, if (a = c ∨ b = c) ∨ (j = m ∨ l = m) then 0 else t (c, m)) =
        if a = c ∨ b = c then 0 else -t (c, j) - t (c, l) := by
    by_cases heq : a = c ∨ b = c
    · simp [heq]
    · simp only [heq, false_or, ite_false]
      rw [sum_except_two (row t c) hjl, hr c, zero_sub]
  simp_rw [hrow]
  rw [sum_except_two (fun c : Fin 4 => -t (c, j) - t (c, l)) hab]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hc, neg_zero, sub_zero]
  ring

/-- The mixed cubic at one doubly centred direction is a bilinear sum weighted by
the sums of the corresponding two-by-two rectangles. -/
theorem mixedRook3_of_double_centered (x y t : Mat4 ι)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    mixedRook3 x y t = ∑ a : Fin 4, ∑ b : Fin 4, ∑ j, ∑ l,
      if a = b ∨ j = l then 0
      else x (a, j) * y (b, l) * (t (a, j) + t (a, l) + t (b, j) + t (b, l)) := by
  unfold mixedRook3
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, false_or, distinct3, row]
    have houter (c : Fin 4) :
        (if a = c ∨ b = c then 0 else ∑ j, ∑ l, ∑ m,
          if j = l ∨ j = m ∨ l = m then 0 else x (a, j) * y (b, l) * t (c, m)) =
        ∑ j, ∑ l, if j = l then 0 else ∑ m,
          if (a = c ∨ b = c) ∨ (j = m ∨ l = m) then 0 else x (a, j) * y (b, l) * t (c, m) := by
      by_cases heq : a = c ∨ b = c
      · simp [heq]
      · simp only [heq, ite_false, false_or]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        by_cases hjl : j = l <;> simp [hjl]
    simp_rw [houter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hjl : j = l
    · simp [hjl]
    · have hfactor (c : Fin 4) (m : ι) :
          (if (a = c ∨ b = c) ∨ (j = m ∨ l = m) then 0 else x (a, j) * y (b, l) * t (c, m)) =
            (x (a, j) * y (b, l)) * (if (a = c ∨ b = c) ∨ (j = m ∨ l = m) then 0 else t (c, m)) := by
        split_ifs <;> simp
      simp only [hjl, ite_false, hfactor, ← Finset.mul_sum]
      rw [centered_rectangle_sum t hr hc hab hjl]

/-- The rectangle-weighted equation holds for arbitrary directions `x`, `y` in a
candidate space whenever it contains the doubly centred direction `t`. -/
theorem rectangle_sum_eq_zero {V : Submodule ℂ (Mat4 ι)} (hV : ∀ t ∈ V, rook3 t = 0)
    {x y t : Mat4 ι} (hx : x ∈ V) (hy : y ∈ V) (ht : t ∈ V)
    (hr : ∀ i, ∑ j, t (i, j) = 0) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ j, ∑ l,
      if a = b ∨ j = l then 0
      else x (a, j) * y (b, l) * (t (a, j) + t (a, l) + t (b, j) + t (b, l))) = 0 := by
  rw [← mixedRook3_of_double_centered x y t hr hc]
  exact mixedRook3_eq_zero hV hx hy ht

private def rowSum (x : Mat4 ι) (a : Fin 4) : ℂ := ∑ j, x (a, j)

private def colSum (x : Mat4 ι) (j : ι) : ℂ := ∑ a, x (a, j)

def marginCorrected (x : Mat4 ι) (a : Fin 4) (j : ι) : ℂ :=
  2 * x (a, j) - rowSum x a - colSum x j

private def offRectangle (f : Fin 4 → Fin 4 → ι → ι → ℂ) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ j, ∑ l, if a = b ∨ j = l then 0 else f a b j l

private theorem offRectangle_add (f g : Fin 4 → Fin 4 → ι → ι → ℂ) :
    offRectangle (fun a b j l => f a b j l + g a b j l) = offRectangle f + offRectangle g := by
  simp only [offRectangle, zeroElse_add, Finset.sum_add_distrib]

private theorem offRectangle_swap_rows (f : Fin 4 → Fin 4 → ι → ι → ℂ) :
    offRectangle (fun a b j l => f b a j l) = offRectangle f := by
  unfold offRectangle
  rw [Finset.sum_comm]
  simp only [eq_comm (α := Fin 4)]

private theorem offRectangle_swap_cols (f : Fin 4 → Fin 4 → ι → ι → ℂ) :
    offRectangle (fun a b j l => f a b l j) = offRectangle f := by
  unfold offRectangle
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [eq_comm (α := ι)]

private theorem sum_off_row_col (x : Mat4 ι) (a : Fin 4) (j : ι) :
    (∑ b : Fin 4, ∑ l, if a = b ∨ j = l then 0 else x (b, l)) =
      (∑ b, rowSum x b) - rowSum x a - colSum x j + x (a, j) := by
  have he (b : Fin 4) :
      (∑ l, if a = b ∨ j = l then 0 else x (b, l)) =
        if a = b then 0 else rowSum x b - x (b, j) := by
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, false_or, ite_false]
      exact sum_except_one (fun l => x (b, l)) j
  simp_rw [he]
  rw [sum_except_one (fun b : Fin 4 => rowSum x b - x (b, j)) a]
  simp only [Finset.sum_sub_distrib, colSum]
  ring

private theorem sum_rectangle_anchors (x y : Mat4 ι) (a : Fin 4) (j : ι)
    (hx : ∑ b, rowSum x b = 0) (hy : ∑ b, rowSum y b = 0) :
    (∑ b : Fin 4, ∑ l, if a = b ∨ j = l then 0 else
      x (a, j) * y (b, l) + x (a, l) * y (b, j) + x (b, j) * y (a, l) +
        x (b, l) * y (a, j)) =
      marginCorrected x a j * marginCorrected y a j -
        rowSum x a * rowSum y a - colSum x j * colSum y j := by
  have hsplit (b : Fin 4) (l : ι) :
      (if a = b ∨ j = l then 0 else
        x (a, j) * y (b, l) + x (a, l) * y (b, j) + x (b, j) * y (a, l) +
          x (b, l) * y (a, j)) =
        x (a, j) * (if a = b ∨ j = l then 0 else y (b, l)) +
        (if j = l then 0 else x (a, l)) * (if a = b then 0 else y (b, j)) +
        (if a = b then 0 else x (b, j)) * (if j = l then 0 else y (a, l)) +
        (if a = b ∨ j = l then 0 else x (b, l)) * y (a, j) := by
    by_cases hab : a = b <;> by_cases hjl : j = l <;> simp [hab, hjl]
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_off_row_col, sum_except_one, ← Finset.mul_sum, sum_except_one, hx, hy]
  change _ = (2 * x (a, j) - rowSum x a - colSum x j) *
    (2 * y (a, j) - rowSum y a - colSum y j) - rowSum x a * rowSum y a - colSum x j * colSum y j
  unfold rowSum colSum
  ring

/-- On directions of total sum zero, the mixed cubic with one doubly centred slot
is diagonal after correcting the other slots by their row and column sums. -/
theorem mixedRook3_eq_corrected_dot (x y t : Mat4 ι)
    (hx : ∑ a, ∑ j, x (a, j) = 0) (hy : ∑ a, ∑ j, y (a, j) = 0)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    mixedRook3 x y t = ∑ a : Fin 4, ∑ j, t (a, j) * marginCorrected x a j * marginCorrected y a j := by
  rw [mixedRook3_of_double_centered x y t hr hc]
  change offRectangle (fun a b j l =>
    x (a, j) * y (b, l) * (t (a, j) + t (a, l) + t (b, j) + t (b, l))) = _
  have hcol := offRectangle_swap_cols (fun a b j l => x (a, l) * y (b, j) * t (a, j))
  have hrow := offRectangle_swap_rows (fun a b j l => x (b, j) * y (a, l) * t (a, j))
  have hboth := (offRectangle_swap_rows (fun a b j l => x (b, j) * y (a, l) * t (a, l))).trans
    (offRectangle_swap_cols (fun a b j l => x (b, l) * y (a, j) * t (a, j)))
  simp only [mul_add, offRectangle_add, hcol, hrow, hboth]
  simp only [← offRectangle_add, ← add_mul]
  unfold offRectangle
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  have hpull (a b : Fin 4) (j l : ι) :
      (if a = b ∨ j = l then 0 else
        (x (a, j) * y (b, l) + x (a, l) * y (b, j) + x (b, j) * y (a, l) +
          x (b, l) * y (a, j)) * t (a, j)) = (if a = b ∨ j = l then 0 else
        x (a, j) * y (b, l) + x (a, l) * y (b, j) + x (b, j) * y (a, l) +
          x (b, l) * y (a, j)) * t (a, j) := by
    split_ifs <;> simp
  simp_rw [hpull, ← Finset.sum_mul, sum_rectangle_anchors x y _ _ hx hy, sub_mul,
    Finset.sum_sub_distrib]
  have hrowTerm : (∑ a : Fin 4, ∑ j, rowSum x a * rowSum y a * t (a, j)) = 0 := by
    simp only [← Finset.mul_sum, hr, mul_zero, Finset.sum_const_zero]
  have hcolTerm : (∑ a : Fin 4, ∑ j, colSum x j * colSum y j * t (a, j)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hc, mul_zero, Finset.sum_const_zero]
  rw [hrowTerm, hcolTerm, sub_zero, sub_zero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- In a candidate space, the doubly centred directions annihilate the span of
coordinatewise products of margin-corrected directions. -/
theorem corrected_dot_eq_zero {V : Submodule ℂ (Mat4 ι)}
    (hV : ∀ t ∈ V, (∑ a, ∑ j, t (a, j)) = 0 ∧ rook3 t = 0)
    {x y t : Mat4 ι} (hx : x ∈ V) (hy : y ∈ V) (ht : t ∈ V)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    (∑ a : Fin 4, ∑ j, t (a, j) * marginCorrected x a j * marginCorrected y a j) = 0 := by
  rw [← mixedRook3_eq_corrected_dot x y t (hV x hx).1 (hV y hy).1 hr hc]
  exact mixedRook3_eq_zero (fun z hz => (hV z hz).2) hx hy ht

/-- On the total-sum-zero hyperplane the margin correction loses no directions. -/
theorem eq_zero_of_marginCorrected {x : Mat4 (Fin 6)}
    (hx : ∑ a, ∑ j, x (a, j) = 0) (hzero : ∀ a j, marginCorrected x a j = 0) : x = 0 := by
  have hRows : (∑ a, rowSum x a) = 0 := hx
  have hCols : (∑ j, colSum x j) = 0 := Finset.sum_comm.trans hx
  have hentry (a : Fin 4) (j : Fin 6) :
      2 * x (a, j) = rowSum x a + colSum x j := by
    have h := hzero a j
    unfold marginCorrected at h
    linear_combination h
  have hr (a : Fin 4) : rowSum x a = 0 := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hentry a j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hCols, add_zero] at hs
    change 2 * rowSum x a = (6 : ℂ) * rowSum x a at hs
    linear_combination (-1 / 4 : ℂ) * hs
  have hc (j : Fin 6) : colSum x j = 0 := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => hentry a j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hRows, zero_add] at hs
    change 2 * colSum x j = (4 : ℂ) * colSum x j at hs
    linear_combination (-1 / 2 : ℂ) * hs
  funext ⟨a, j⟩
  have h := hentry a j
  rw [hr, hc, zero_add] at h
  change x (a, j) = 0
  linear_combination (1 / 2 : ℂ) * h

/-!
The coordinatewise product span below is the square of a linear code in the terminology of
Hugues Randriambololona, *On products and powers of linear codes under componentwise
multiplication*, https://arxiv.org/abs/1312.0022. Only the definition of the product span
is used here. Its annihilator is exhibited directly by `corrected_dot_eq_zero`.
-/

/-- A nonzero doubly centred direction makes the corrected product span proper. -/
theorem corrected_product_span_ne_top {V : Submodule ℂ (Mat4 ι)}
    (hV : ∀ x ∈ V, (∑ a, ∑ j, x (a, j)) = 0 ∧ rook3 x = 0)
    {t : Mat4 ι} (ht : t ∈ V) (hne : t ≠ 0)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    Submodule.span ℂ {u : Mat4 ι | ∃ x ∈ V, ∃ y ∈ V,
      ∀ a j, u (a, j) = marginCorrected x a j * marginCorrected y a j} ≠ ⊤ := by
  let pairing := dotProductEquiv ℂ (Fin 4 × ι) t
  have hle : Submodule.span ℂ {u : Mat4 ι | ∃ x ∈ V, ∃ y ∈ V,
      ∀ a j, u (a, j) = marginCorrected x a j * marginCorrected y a j} ≤ pairing.ker := by
    apply Submodule.span_le.mpr
    rintro u ⟨x, hx, y, hy, hu⟩
    change dotProduct t u = 0
    rw [dotProduct, Fintype.sum_prod_type]
    simp only [hu, ← mul_assoc]
    exact corrected_dot_eq_zero hV hx hy ht hr hc
  intro htop
  rw [htop, top_le_iff] at hle
  apply hne
  apply (dotProductEquiv ℂ (Fin 4 × ι)).injective
  rw [map_zero]
  exact LinearMap.ker_eq_top.mp hle

private theorem twice_finrank_le_of_diagonal_form {α : Type*} [Fintype α] [DecidableEq α]
    (a : α → ℂ) (ha : ∀ i, a i ≠ 0) (W : Submodule ℂ (α → ℂ))
    (hW : ∀ x ∈ W, ∀ y ∈ W, (∑ i, a i * x i * y i) = 0) :
    2 * Module.finrank ℂ W ≤ Fintype.card α := by
  let scale : (α → ℂ) →ₗ[ℂ] (α → ℂ) := LinearMap.pi fun i => a i • LinearMap.proj i
  have hscale : Function.Injective scale := by
    intro x y h
    funext i
    exact mul_left_cancel₀ (ha i) (congrFun h i)
  let f : W →ₗ[ℂ] Module.Dual ℂ (α → ℂ) :=
    (dotProductEquiv ℂ α).toLinearMap.comp (scale.comp W.subtype)
  have hf : Function.Injective f :=
    (dotProductEquiv ℂ α).injective.comp (hscale.comp Subtype.val_injective)
  have hle : f.range ≤ W.dualAnnihilator := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    exact hW x.1 x.2 y hy
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hf] at hdim
  have hrank := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  omega

noncomputable def entrySupport (t : Mat4 ι) : Finset (Fin 4 × ι) := by
  classical exact Finset.univ.filter (fun ij => t ij ≠ 0)

/-- The row- and column-sum correction restricted to the support of `t`. -/
noncomputable def correctedOnSupport (t : Mat4 ι) : Mat4 ι →ₗ[ℂ] (↥(entrySupport t) → ℂ) where
  toFun x ij := marginCorrected x ij.1.1 ij.1.2
  map_add' x y := by
    funext ij
    simp only [marginCorrected, rowSum, colSum, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    funext ij
    simp only [marginCorrected, rowSum, colSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

/-- The mixed cubic bounds the rank of the corrected projection to the support of
any doubly centred direction. -/
theorem twice_finrank_corrected_support_le {V : Submodule ℂ (Mat4 ι)}
    (hV : ∀ x ∈ V, (∑ a, ∑ j, x (a, j)) = 0 ∧ rook3 x = 0)
    {t : Mat4 ι} (ht : t ∈ V)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    2 * Module.finrank ℂ ((correctedOnSupport t).domRestrict V).range ≤ (entrySupport t).card := by
  classical
  rw [← Fintype.card_coe]
  apply twice_finrank_le_of_diagonal_form (fun ij => t ij.1)
  · intro ij
    simpa only [entrySupport, Finset.mem_filter, Finset.mem_univ, true_and] using ij.2
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    let f : Fin 4 × ι → ℂ := fun ij =>
      t ij * marginCorrected x.1 ij.1 ij.2 * marginCorrected y.1 ij.1 ij.2
    change (∑ ij : entrySupport t, f ij.1) = 0
    rw [Finset.sum_coe_sort]
    have hsum : (∑ ij ∈ entrySupport t, f ij) = ∑ ij, f ij := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro ij _ hnot
      have hz : t ij = 0 := by simpa [entrySupport] using hnot
      simp [f, hz]
    rw [hsum, Fintype.sum_prod_type]
    exact corrected_dot_eq_zero hV x.2 y.2 ht hr hc

/-- With two opposite rows in the centred slot, the mixed cubic gives a linear
condition on the sum of the complementary rows. -/
theorem weighted_complementary_row_sum_eq_zero {V : Submodule ℂ (Mat4 (Fin 6))}
    (hV : ∀ x ∈ V, (∑ a, ∑ j, x (a, j)) = 0 ∧ rook3 x = 0)
    {t x : Mat4 (Fin 6)} (ht : t ∈ V) (hx : x ∈ V)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0)
    {v : Fin 6 → ℂ} (hvSq : ∑ j, v j ^ 2 = 0)
    (h0 : row t 0 = v) (h1 : row t 1 = fun j => -v j) (h2 : row t 2 = 0) (h3 : row t 3 = 0) :
    (∑ j, v j ^ 2 * (x (2, j) + x (3, j))) = 0 := by
  have htCorrect (a : Fin 4) (j : Fin 6) : marginCorrected t a j = 2 * t (a, j) := by
    simp [marginCorrected, rowSum, colSum, hr, hc]
  have hpoint (j : Fin 6) :
      (∑ a : Fin 4, t (a, j) * marginCorrected t a j * marginCorrected x a j) =
        -4 * (v j ^ 2 * (x (2, j) + x (3, j))) - v j ^ 2 * (2 * (rowSum x 0 + rowSum x 1)) := by
    have ht0 : t (0, j) = v j := congrFun h0 j
    have ht1 : t (1, j) = -v j := congrFun h1 j
    have ht2 : t (2, j) = 0 := congrFun h2 j
    have ht3 : t (3, j) = 0 := congrFun h3 j
    simp only [Fin.sum_univ_four, htCorrect, ht0, ht1, ht2, ht3]
    simp only [marginCorrected, colSum, Fin.sum_univ_four]
    ring
  have h := corrected_dot_eq_zero hV ht hx ht hr hc
  rw [Finset.sum_comm] at h
  simp only [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hvSq,
    zero_mul, sub_zero] at h
  linear_combination (-1 / 4 : ℂ) * h

/-- The two remaining rows in a mixed quartic coefficient contribute this sum
after the other two directions use columns `j` and `l`. -/
theorem distinct2_off_columns_of_centered (a b : ι → ℂ) (ha : ∑ m, a m = 0)
    (hb : ∑ m, b m = 0) {j l : ι} (hjl : j ≠ l) :
    (∑ m ∈ Finset.univ \ {j, l}, ∑ n ∈ Finset.univ \ {j, l},
      if m = n then 0 else a m * b n) =
      2 * a j * b j + 2 * a l * b l + a j * b l + a l * b j - pair a b := by
  let S : Finset ι := Finset.univ \ {j, l}
  have hsum (f : ι → ℂ) : (∑ m ∈ S, f m) = (∑ m, f m) - f j - f l := by
    have hS : S = Finset.univ.filter (fun m => m ∉ ({j, l} : Finset ι)) := by
      ext m
      simp [S]
    rw [hS, Finset.sum_filter]
    simpa only [ite_not, Finset.mem_insert, Finset.mem_singleton, eq_comm] using
      sum_except_two f hjl
  have hrow (m : ι) (hm : m ∈ S) :
      (∑ n ∈ S, if m = n then 0 else a m * b n) = a m * ((∑ n ∈ S, b n) - b m) := by
    have he (n : ι) : (if m = n then 0 else a m * b n) =
        a m * (b n - (if m = n then b n else 0)) := by
      by_cases hmn : m = n <;> simp [hmn]
    simp_rw [he, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, hm, ite_true]
  change (∑ m ∈ S, ∑ n ∈ S, if m = n then 0 else a m * b n) = _
  rw [Finset.sum_congr rfl (fun m hm => hrow m hm)]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum a, hsum b, hsum (fun m => a m * b m), ha, hb]
  unfold pair
  ring

abbrev rook4 (x : Mat4 ι) : ℂ := distinct4 (row x 0) (row x 1) (row x 2) (row x 3)

/-- The coefficient of `s²` in `rook4 (t + s • x)`. The rows are in their
original order in each of the six terms. -/
def quarticQuadratic (t x : Mat4 ι) : ℂ :=
  distinct4 (row x 0) (row x 1) (row t 2) (row t 3) +
  distinct4 (row x 0) (row t 1) (row x 2) (row t 3) +
  distinct4 (row x 0) (row t 1) (row t 2) (row x 3) +
  distinct4 (row t 0) (row x 1) (row x 2) (row t 3) +
  distinct4 (row t 0) (row x 1) (row t 2) (row x 3) +
  distinct4 (row t 0) (row t 1) (row x 2) (row x 3)

theorem twice_quarticQuadratic (t x : Mat4 ι) :
    2 * quarticQuadratic t x = rook4 (t + x) + rook4 (t - x) - 2 * rook4 t - 2 * rook4 x := by
  simp only [rook4, quarticQuadratic, distinct4, row, Pi.add_apply, Pi.sub_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

theorem quarticQuadratic_eq_zero {V : Submodule ℂ (Mat4 ι)} (hV : ∀ x ∈ V, rook4 x = 0)
    {t x : Mat4 ι} (ht : t ∈ V) (hx : x ∈ V) : quarticQuadratic t x = 0 := by
  have h := twice_quarticQuadratic t x
  rw [hV _ (V.add_mem ht hx), hV _ (V.sub_mem ht hx), hV _ ht, hV _ hx] at h
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp (by simpa using h)).resolve_left htwo

private theorem distinct4_swap_first (a b c d : ι → ℂ) :
    distinct4 a b c d = distinct4 b a c d := by
  unfold distinct4
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [eq_comm, or_left_comm, mul_comm, mul_left_comm]

private theorem distinct4_swap_middle (a b c d : ι → ℂ) :
    distinct4 a b c d = distinct4 a c b d := by
  unfold distinct4
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun n _ => ?_
  simp [eq_comm, or_comm, or_left_comm, mul_comm, mul_left_comm]

private theorem distinct4_swap_last (a b c d : ι → ℂ) :
    distinct4 a b c d = distinct4 a b d c := by
  unfold distinct4
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  simp [eq_comm, or_left_comm, mul_comm, mul_left_comm]

def quarticWeight (c d : ι → ℂ) (j l : ι) : ℂ :=
  2 * c j * d j + 2 * c l * d l + c j * d l + c l * d j - pair c d

def quarticPair (a b c d : ι → ℂ) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else a j * b l * quarticWeight c d j l

private theorem distinct4_eq_quarticPair (a b c d : ι → ℂ)
    (hc : ∑ j, c j = 0) (hd : ∑ j, d j = 0) : distinct4 a b c d = quarticPair a b c d := by
  unfold distinct4 quarticPair
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hjl : j = l
  · simp [hjl]
  · simp only [hjl, false_or, ite_false]
    rw [show quarticWeight c d j l = (∑ m ∈ Finset.univ \ {j, l},
      ∑ n ∈ Finset.univ \ {j, l}, if m = n then 0 else c m * d n) from
      (distinct2_off_columns_of_centered c d hc hd hjl).symm]
    simp only [Finset.sdiff_eq_filter, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : j = m ∨ l = m
    · rcases hm with h | h <;> subst m <;> simp
    · have hmj : j ≠ m := fun h => hm (Or.inl h)
      have hml : l ≠ m := fun h => hm (Or.inr h)
      simp only [Finset.mem_insert, Finset.mem_singleton, hmj.symm, hml.symm,
        false_or, not_false_eq_true, ite_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : j = n ∨ l = n
      · rcases hn with h | h <;> subst n <;> simp
      · have hnj : j ≠ n := fun h => hn (Or.inl h)
        have hnl : l ≠ n := fun h => hn (Or.inr h)
        by_cases hmn : m = n <;>
          simp [hmj, hml, hnj, hnl, hnj.symm, hnl.symm, hmn, mul_assoc]

/-- The quadratic coefficient of the quartic about a row-centred direction is a
sum of six weighted two-row forms on arbitrary directions. -/
theorem quarticQuadratic_eq_pairs (t x : Mat4 ι) (ht : ∀ a, ∑ j, t (a, j) = 0) :
    quarticQuadratic t x =
      quarticPair (row x 0) (row x 1) (row t 2) (row t 3) +
      quarticPair (row x 0) (row x 2) (row t 1) (row t 3) +
      quarticPair (row x 0) (row x 3) (row t 1) (row t 2) +
      quarticPair (row x 1) (row x 2) (row t 0) (row t 3) +
      quarticPair (row x 1) (row x 3) (row t 0) (row t 2) +
      quarticPair (row x 2) (row x 3) (row t 0) (row t 1) := by
  unfold quarticQuadratic
  rw [distinct4_swap_middle (row x 0) (row t 1) (row x 2) (row t 3),
    distinct4_swap_last (row x 0) (row t 1) (row t 2) (row x 3),
    distinct4_swap_middle (row x 0) (row t 1) (row x 3) (row t 2),
    distinct4_swap_first (row t 0) (row x 1) (row x 2) (row t 3),
    distinct4_swap_middle (row x 1) (row t 0) (row x 2) (row t 3),
    distinct4_swap_first (row t 0) (row x 1) (row t 2) (row x 3),
    distinct4_swap_last (row x 1) (row t 0) (row t 2) (row x 3),
    distinct4_swap_middle (row x 1) (row t 0) (row x 3) (row t 2),
    distinct4_swap_middle (row t 0) (row t 1) (row x 2) (row x 3),
    distinct4_swap_first (row t 0) (row x 2) (row t 1) (row x 3),
    distinct4_swap_last (row x 2) (row t 0) (row t 1) (row x 3),
    distinct4_swap_middle (row x 2) (row t 0) (row x 3) (row t 1)]
  simp only [distinct4_eq_quarticPair _ _ _ _ (ht 0) (ht 1),
    distinct4_eq_quarticPair _ _ _ _ (ht 0) (ht 2),
    distinct4_eq_quarticPair _ _ _ _ (ht 0) (ht 3),
    distinct4_eq_quarticPair _ _ _ _ (ht 1) (ht 2),
    distinct4_eq_quarticPair _ _ _ _ (ht 1) (ht 3),
    distinct4_eq_quarticPair _ _ _ _ (ht 2) (ht 3)]

/-- For a direction with opposite centred rows `v` and `-v` and two zero rows,
the matrix of quartic weights on the complementary rows has trivial kernel when
every entry of `v` is nonzero and its square sum vanishes. -/
theorem eq_zero_of_quarticWeight_mul {v y : Fin 6 → ℂ}
    (hv : ∀ j, v j ≠ 0) (hvSum : ∑ j, v j = 0) (hvSq : ∑ j, v j ^ 2 = 0)
    (h : ∀ j, (∑ l, if j = l then 0 else quarticWeight v (fun k => -v k) j l * y l) = 0) : y = 0 := by
  have hpair : pair v (fun j => -v j) = 0 := by
    simp only [pair, mul_neg, ← pow_two]
    rw [Finset.sum_neg_distrib, hvSq, neg_zero]
  have hweight (j l : Fin 6) : quarticWeight v (fun k => -v k) j l =
      -2 * (v j ^ 2 + v l ^ 2 + v j * v l) := by
    unfold quarticWeight
    rw [hpair]
    ring
  have hsum (j : Fin 6) :
      (∑ l, if j = l then 0 else (v j ^ 2 + v l ^ 2 + v j * v l) * y l) = 0 := by
    have hj := h j
    have hmul (l : Fin 6) :
        (if j = l then 0 else quarticWeight v (fun k => -v k) j l * y l) =
          -2 * (if j = l then 0 else (v j ^ 2 + v l ^ 2 + v j * v l) * y l) := by
      by_cases hjl : j = l <;> simp [hjl, hweight, mul_assoc]
    simp_rw [hmul, ← Finset.mul_sum] at hj
    exact (mul_eq_zero.mp hj).resolve_left (by norm_num)
  let A : ℂ := ∑ j, y j
  let B : ℂ := ∑ j, v j * y j
  let C : ℂ := ∑ j, v j ^ 2 * y j
  have hpoint (j : Fin 6) : 3 * v j ^ 2 * y j = v j ^ 2 * A + C + v j * B := by
    have hj := hsum j
    rw [sum_except_one (fun l => (v j ^ 2 + v l ^ 2 + v j * v l) * y l) j] at hj
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hj
    change v j ^ 2 * A + C + v j * B -
      (v j ^ 2 * y j + v j ^ 2 * y j + v j * (v j * y j)) = 0 at hj
    linear_combination -hj
  have hC : C = 0 := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hpoint j)
    simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hvSum, hvSq] at hs
    change 3 * C = 0 * A + (6 : ℂ) * C + 0 * B at hs
    linear_combination (-1 / 3 : ℂ) * hs
  have hlinear (j : Fin 6) : 3 * v j * y j = v j * A + B := by
    apply mul_left_cancel₀ (hv j)
    linear_combination hpoint j + hC
  have hB : B = 0 := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hlinear j)
    simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hvSum] at hs
    change 3 * B = 0 * A + (6 : ℂ) * B at hs
    linear_combination (-1 / 3 : ℂ) * hs
  have hconstant (j : Fin 6) : 3 * y j = A := by
    apply mul_left_cancel₀ (hv j)
    linear_combination hlinear j + hB
  have hA : A = 0 := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hconstant j)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
    change 3 * A = (6 : ℂ) * A at hs
    linear_combination (-1 / 3 : ℂ) * hs
  funext j
  change y j = 0
  linear_combination (1 / 3 : ℂ) * hconstant j + (1 / 3 : ℂ) * hA

private theorem finrank_le_of_weighted_pair (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hA : Function.Injective A) (W : Submodule ℂ ((ι → ℂ) × (ι → ℂ)))
    (hW : ∀ p ∈ W, dotProduct p.1 (A p.2) = 0) : Module.finrank ℂ W ≤ Fintype.card ι := by
  let f : W →ₗ[ℂ] (ι → ℂ) := (LinearMap.fst ℂ _ _).comp W.subtype
  let d : f.ker →ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
    ((dotProductEquiv ℂ ι).toLinearMap.comp (A.comp (LinearMap.snd ℂ _ _))).comp
      (W.subtype.comp f.ker.subtype)
  have hfst (z : f.ker) : (z.1.1).1 = 0 := z.2
  have hd : Function.Injective d := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((hfst x).trans (hfst y).symm)
      (hA ((dotProductEquiv ℂ ι).injective hxy))
  have hle : d.range ≤ f.range.dualAnnihilator := by
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨p, rfl⟩
    change dotProduct (A (z.1.1).2) (p.1).1 = 0
    rw [dotProduct_comm]
    have h := hW _ (W.add_mem p.2 z.1.2)
    change dotProduct (p.1.1 + (z.1.1).1) (A (p.1.2 + (z.1.1).2)) = 0 at h
    rw [hfst, add_zero, map_add, dotProduct_add, hW _ p.2, zero_add] at h
    exact h
  have hker := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hd] at hker
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have ha := Subspace.finrank_add_finrank_dualAnnihilator_eq f.range
  rw [Module.finrank_fintype_fun_eq_card] at ha
  omega

private theorem finrank_lt_of_weighted_pair_missing_ones
    (A : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ)) (hA : Function.Injective A)
    (W : Submodule ℂ ((Fin 6 → ℂ) × (Fin 6 → ℂ)))
    (hW : ∀ p ∈ W, dotProduct p.1 (A p.2) = 0)
    (hOne : dotProduct (1 : Fin 6 → ℂ) (A 1) = 0)
    (hCross : ∀ p ∈ W, dotProduct p.1 (A 1) + dotProduct 1 (A p.2) = 0)
    (hNot : (1, 1) ∉ W) : Module.finrank ℂ W < 6 := by
  let e : (Fin 6 → ℂ) × (Fin 6 → ℂ) := (1, 1)
  let U := W ⊔ Submodule.span ℂ {e}
  have hWU : W < U := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    apply hNot
    change e ∈ W
    rw [he]
    have hle : Submodule.span ℂ {e} ≤ U := le_sup_right
    exact hle (Submodule.mem_span_singleton_self e)
  have hU : ∀ p ∈ U, dotProduct p.1 (A p.2) = 0 := by
    intro p hp
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change dotProduct (u.1 + c • (1 : Fin 6 → ℂ)) (A (u.2 + c • (1 : Fin 6 → ℂ))) = 0
    simp only [map_add, map_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      hW _ hu, hOne, zero_add, smul_eq_mul]
    linear_combination c * hCross u hu
  have hb := finrank_le_of_weighted_pair A hA U hU
  have hs := Submodule.finrank_lt_finrank_of_lt hWU
  simpa using lt_of_lt_of_le hs hb

private def quarticWeightMap (v : Fin 6 → ℂ) : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun y j := ∑ l, if j = l then 0 else quarticWeight v (fun k => -v k) j l * y l
  map_add' y z := by
    funext j
    simp only [Pi.add_apply, mul_add, zeroElse_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hjl : j = l <;> simp [hjl, mul_left_comm]

private theorem quarticWeightMap_one {v : Fin 6 → ℂ}
    (hvSum : ∑ j, v j = 0) (hvSq : ∑ j, v j ^ 2 = 0) :
    quarticWeightMap v 1 = fun j => -6 * v j ^ 2 := by
  have hpair : pair v (fun j => -v j) = 0 := by
    simp only [pair, mul_neg, ← pow_two]
    rw [Finset.sum_neg_distrib, hvSq, neg_zero]
  have hweight (j l : Fin 6) : quarticWeight v (fun k => -v k) j l =
      -2 * (v j ^ 2 + v l ^ 2 + v j * v l) := by
    unfold quarticWeight
    rw [hpair]
    ring
  funext j
  change (∑ l, if j = l then 0 else quarticWeight v (fun k => -v k) j l * 1) = _
  simp only [mul_one, hweight]
  rw [sum_except_one (fun l => -2 * (v j ^ 2 + v l ^ 2 + v j * v l)) j]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hvSum, hvSq]
  ring

private theorem quarticPair_eq_dotProduct (a b v : Fin 6 → ℂ) :
    quarticPair a b v (fun j => -v j) = dotProduct a (quarticWeightMap v b) := by
  unfold quarticPair dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = a j * ∑ l, if j = l then 0 else quarticWeight v (fun k => -v k) j l * b l
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hjl : j = l <;> simp [hjl, mul_assoc, mul_comm]

private theorem quarticWeightMap_symmetric (a b v : Fin 6 → ℂ) :
    dotProduct a (quarticWeightMap v b) = dotProduct b (quarticWeightMap v a) := by
  simp only [← quarticPair_eq_dotProduct, quarticPair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hjl : j = l
  · simp [hjl]
  · simp only [hjl, Ne.symm hjl, ite_false, quarticWeight]
    ring

/-- The weighted complementary-row constraints allow at most five dimensions
once the pair of all-ones rows is excluded. -/
theorem finrank_le_five_of_complementary_weight_constraints
    (W : Submodule ℂ ((Fin 6 → ℂ) × (Fin 6 → ℂ))) {v : Fin 6 → ℂ}
    (hv : ∀ j, v j ≠ 0) (hvSum : ∑ j, v j = 0) (hvSq : ∑ j, v j ^ 2 = 0)
    (hQ : ∀ p ∈ W, quarticPair p.1 p.2 v (fun j => -v j) = 0)
    (hSum : ∀ p ∈ W, (∑ j, v j ^ 2 * (p.1 j + p.2 j)) = 0)
    (hNot : (1, 1) ∉ W) : Module.finrank ℂ W ≤ 5 := by
  have hinj : Function.Injective (quarticWeightMap v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact eq_zero_of_quarticWeight_mul hv hvSum hvSq (fun j => congrFun hy j)
  have hOne : dotProduct (1 : Fin 6 → ℂ) (quarticWeightMap v 1) = 0 := by
    rw [quarticWeightMap_one hvSum hvSq]
    simp only [dotProduct, Pi.one_apply, one_mul, ← Finset.mul_sum, hvSq, mul_zero]
  have hCross (p) (hp : p ∈ W) :
      dotProduct p.1 (quarticWeightMap v 1) + dotProduct 1 (quarticWeightMap v p.2) = 0 := by
    rw [quarticWeightMap_symmetric 1 p.2, quarticWeightMap_one hvSum hvSq]
    have he : (∑ j, p.1 j * (-6 * v j ^ 2)) + (∑ j, p.2 j * (-6 * v j ^ 2)) =
        -6 * (∑ j, v j ^ 2 * (p.1 j + p.2 j)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact he.trans (by rw [hSum p hp, mul_zero])
  have h := finrank_lt_of_weighted_pair_missing_ones _ hinj W
    (fun p hp => (quarticPair_eq_dotProduct p.1 p.2 v).symm.trans (hQ p hp)) hOne hCross hNot
  omega

/-- Opposite dense centred rows in a level direction bound the dimension of the
projection of the full level space onto the complementary two rows. -/
theorem finrank_complementary_rows_le_six {V : Submodule ℂ (Mat4 (Fin 6))}
    (hV : ∀ x ∈ V, rook4 x = 0) {t : Mat4 (Fin 6)} (ht : t ∈ V)
    {v : Fin 6 → ℂ} (hv : ∀ j, v j ≠ 0) (hvSum : ∑ j, v j = 0) (hvSq : ∑ j, v j ^ 2 = 0)
    (h0 : row t 0 = v) (h1 : row t 1 = fun j => -v j) (h2 : row t 2 = 0) (h3 : row t 3 = 0) :
    Module.finrank ℂ (((LinearMap.funLeft ℂ ℂ (fun j : Fin 6 => ((2 : Fin 4), j))).prod
      (LinearMap.funLeft ℂ ℂ (fun j : Fin 6 => ((3 : Fin 4), j)))).comp V.subtype).range ≤ 6 := by
  have hr (a : Fin 4) : ∑ j, t (a, j) = 0 := by
    change (∑ j, row t a j) = 0
    fin_cases a
    · change (∑ j, row t 0 j) = 0
      rw [h0, hvSum]
    · change (∑ j, row t 1 j) = 0
      rw [h1, Finset.sum_neg_distrib, hvSum, neg_zero]
    · simp [h2]
    · simp [h3]
  have hinj : Function.Injective (quarticWeightMap v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact eq_zero_of_quarticWeight_mul hv hvSum hvSq (fun j => congrFun hy j)
  refine finrank_le_of_weighted_pair (quarticWeightMap v) hinj _ ?_
  rintro _ ⟨x, rfl⟩
  change dotProduct (row (x : Mat4 (Fin 6)) 2) (quarticWeightMap v (row x 3)) = 0
  rw [← quarticPair_eq_dotProduct]
  have h := quarticQuadratic_eq_pairs t (x : Mat4 (Fin 6)) hr
  rw [quarticQuadratic_eq_zero hV ht x.2, h0, h1, h2, h3] at h
  simpa only [quarticPair, quarticWeight, pair, Pi.zero_apply, mul_zero, zero_mul,
    add_zero, sub_zero, ite_self, Finset.sum_const_zero, zero_add] using h.symm

/-- The centered dimension bound holds when the quartic row-pairing
correction vanishes identically on the space. -/
theorem finrank_lt_of_zero_pairing (V : Submodule ℂ (Mat4 ι)) [Nonempty ι]
    (h : ∀ t ∈ V,
      (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ rook2 t = 0 ∧ rook3 t = 0 ∧
      distinct4 (row t 0) (row t 1) (row t 2) (row t 3) = 0 ∧ pairingCorrection t = 0) :
    Module.finrank ℂ V < Fintype.card ι := by
  classical
  apply finrank_lt_of_columnProducts _ Finset.univ V (by simp) Finset.univ_nonempty
  intro t ht
  obtain ⟨hr, h2, h3, h4, hp⟩ := h t ht
  have e2 := (rook2_of_centered t hr).symm.trans h2
  have e3 := (rook3_of_centered t hr).symm.trans h3
  have e4 := (distinct4_of_centered (row t 0) (row t 1) (row t 2) (row t 3)
    (hr 0) (hr 1) (hr 2) (hr 3)).symm.trans h4
  change pairingCorrection t - 6 * (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j)) = 0 at e4
  rw [hp] at e4
  have hz2 : pair (row t 0) (row t 1) + pair (row t 0) (row t 2) + pair (row t 0) (row t 3) +
      pair (row t 1) (row t 2) + pair (row t 1) (row t 3) + pair (row t 2) (row t 3) = 0 :=
    neg_eq_zero.1 e2
  have hz3 : (∑ j, (
      t (0, j) * t (1, j) * t (2, j) + t (0, j) * t (1, j) * t (3, j) +
      t (0, j) * t (2, j) * t (3, j) + t (1, j) * t (2, j) * t (3, j))) = 0 :=
    (mul_eq_zero.1 e3).resolve_left (by norm_num)
  have hz4 : (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j)) = 0 := by
    exact (mul_eq_zero.1 (neg_eq_zero.1 (by simpa only [zero_sub] using e4))).resolve_left (by norm_num)
  refine ⟨by simp, ?_⟩
  have hExpand (j : ι) : columnProduct t j = 1 +
      (t (0, j) + t (1, j) + t (2, j) + t (3, j)) +
      (t (0, j) * t (1, j) + t (0, j) * t (2, j) + t (0, j) * t (3, j) +
        t (1, j) * t (2, j) + t (1, j) * t (3, j) + t (2, j) * t (3, j)) +
      (t (0, j) * t (1, j) * t (2, j) + t (0, j) * t (1, j) * t (3, j) +
        t (0, j) * t (2, j) * t (3, j) + t (1, j) * t (2, j) * t (3, j)) +
      t (0, j) * t (1, j) * t (2, j) * t (3, j) := by
    simp only [columnProduct, Fin.prod_univ_four]
    ring
  simp only [Finset.sum_add_distrib] at hz3
  simp only [hExpand, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_one, hr, add_zero]
  simp only [pair] at hz2
  linear_combination hz2 + hz3 + hz4

end FourRows

private theorem sumSix (f : Fin 6 → ℂ) : ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ]
  ring

private def pairedRowExample (w a b : ℂ) : Mat4 (Fin 6) := fun ij =>
  let v : Fin 6 → ℂ := ![1, w, -1 - w, 0, 0, 0]
  let u : Fin 6 → ℂ := ![1, 0, 0, w, -1 - w, 0]
  (![a * v ij.2, -a * v ij.2, b * u ij.2, -b * u ij.2] : Fin 4 → ℂ) ij.1

private theorem pairedRowExample_equations (w a b : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    let z := pairedRowExample w a b
    (∀ i, ∑ j, z (i, j) = 0) ∧ (∀ j, ∑ i, z (i, j) = 0) ∧
      rook2 z = 0 ∧ rook3 z = 0 ∧ rook4 z = -4 * a ^ 2 * b ^ 2 := by
  let z := pairedRowExample w a b
  change (∀ i, ∑ j, z (i, j) = 0) ∧ (∀ j, ∑ i, z (i, j) = 0) ∧
    rook2 z = 0 ∧ rook3 z = 0 ∧ rook4 z = -4 * a ^ 2 * b ^ 2
  have hr (i : Fin 4) : ∑ j, z (i, j) = 0 := by
    fin_cases i <;> simp [z, pairedRowExample, sumSix] <;> ring
  have hc (j : Fin 6) : ∑ i, z (i, j) = 0 := by
    simp [z, pairedRowExample, Fin.sum_univ_four]
  have h2 := twice_rook2_of_double_centered z hr hc
  have hs : (∑ j : Fin 6, ∑ i, z (i, j) ^ 2) = 0 := by
    simp [z, pairedRowExample, sumSix, Fin.sum_univ_four]
    linear_combination (4 * a ^ 2 + 4 * b ^ 2) * hw
  rw [hs] at h2
  have h3 := three_mul_rook3_of_double_centered z hr hc
  have hcubes (j : Fin 6) : (∑ i, z (i, j) ^ 3) = 0 := by
    simp [z, pairedRowExample, Fin.sum_univ_four]
    ring
  simp only [hcubes, Finset.sum_const_zero, mul_zero] at h3
  refine ⟨hr, hc, (mul_eq_zero.mp h2).resolve_left (by norm_num),
    (mul_eq_zero.mp h3).resolve_left (by norm_num), ?_⟩
  have h01 : pair (row z 0) (row z 1) = 0 := by
    simp [pair, row, z, pairedRowExample, sumSix]
    linear_combination (-2 * a ^ 2) * hw
  have h23 : pair (row z 2) (row z 3) = 0 := by
    simp [pair, row, z, pairedRowExample, sumSix]
    linear_combination (-2 * b ^ 2) * hw
  have h02 : pair (row z 0) (row z 2) = a * b := by
    simp [pair, row, z, pairedRowExample, sumSix]
  have h13 : pair (row z 1) (row z 3) = a * b := by
    simp [pair, row, z, pairedRowExample, sumSix]
  have h03 : pair (row z 0) (row z 3) = -(a * b) := by
    simp [pair, row, z, pairedRowExample, sumSix]
  have h12 : pair (row z 1) (row z 2) = -(a * b) := by
    simp [pair, row, z, pairedRowExample, sumSix]
  have hprod : (∑ j : Fin 6, z (0, j) * z (1, j) * z (2, j) * z (3, j)) = a ^ 2 * b ^ 2 := by
    simp [z, pairedRowExample, sumSix]
    ring
  rw [rook4, distinct4_of_centered _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3), h01, h23,
    h02, h13, h03, h12]
  change 0 * 0 + a * b * (a * b) + -(a * b) * -(a * b) - 6 *
    (∑ j : Fin 6, z (0, j) * z (1, j) * z (2, j) * z (3, j)) = _
  rw [hprod]
  ring

/-- The mixed quartic equation imposes an additional restriction on a family
where the lower-degree equations vanish. -/
theorem exists_mixed_quartic_obstruction : ∃ t x : Mat4 (Fin 6),
    (∀ a b : ℂ, let z := a • t + b • x
      (∀ i, ∑ j, z (i, j) = 0) ∧ (∀ j, ∑ i, z (i, j) = 0) ∧
        rook2 z = 0 ∧ rook3 z = 0) ∧
    rook4 t = 0 ∧ rook4 x = 0 ∧ quarticQuadratic t x = -4 := by
  have hs : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let w : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2
  have hw : w ^ 2 + w + 1 = 0 := by
    dsimp [w]
    linear_combination (1 / 4 : ℂ) * hs
  let t := pairedRowExample w 1 0
  let x := pairedRowExample w 0 1
  have hcombo (a b : ℂ) : a • t + b • x = pairedRowExample w a b := by
    funext ⟨i, j⟩
    fin_cases i <;> simp [t, x, pairedRowExample]
  have hquartic (a b : ℂ) : rook4 (a • t + b • x) = -4 * a ^ 2 * b ^ 2 := by
    rw [hcombo]
    exact (pairedRowExample_equations w a b hw).2.2.2.2
  have ht : rook4 t = 0 := by simpa using hquartic 1 0
  have hx : rook4 x = 0 := by simpa using hquartic 0 1
  refine ⟨t, x, ?_, ht, hx, ?_⟩
  · intro a b
    dsimp only
    rw [hcombo]
    obtain ⟨hr, hc, h2, h3, _⟩ := pairedRowExample_equations w a b hw
    exact ⟨hr, hc, h2, h3⟩
  · have hp : rook4 (t + x) = -4 := by simpa using hquartic 1 1
    have hm : rook4 (t - x) = -4 := by simpa [sub_eq_add_neg] using hquartic 1 (-1)
    have h := twice_quarticQuadratic t x
    rw [hp, hm, ht, hx] at h
    linear_combination (1 / 2 : ℂ) * h

private def sixColumnExample (z : ℂ) : Mat4 (Fin 6) := fun p =>
  (![![1, z, z - 1, -1, -z, 1 - z],
    ![1, 1 - z, -z, -1, z - 1, z],
    ![1, z - 1, -z, 1, z - 1, -z],
    ![-1, z, 1 - z, -1, z, 1 - z]] : Fin 4 → Fin 6 → ℂ) p.1 p.2

/-- The correction in the fourth-degree identity can be nonzero on a
row-centred direction satisfying every level equation. -/
theorem exists_nonzero_pairing : ∃ t : Mat4 (Fin 6),
    (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ rook2 t = 0 ∧ rook3 t = 0 ∧
    distinct4 (row t 0) (row t 1) (row t 2) (row t 3) = 0 ∧ pairingCorrection t = -36 := by
  have hs : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let z : ℂ := (1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2
  have hz : z ^ 2 - z + 1 = 0 := by
    dsimp [z]
    linear_combination hs / 4
  let t := sixColumnExample z
  have hr (i : Fin 4) : ∑ j, t (i, j) = 0 := by
    fin_cases i <;> simp [sumSix, t, sixColumnExample] <;> ring
  have p01 : pair (row t 0) (row t 1) = 6 := by
    simp only [pair, sumSix, t]
    simp [sixColumnExample]
    linear_combination -4 * hz
  have p02 : pair (row t 0) (row t 2) = 0 := by
    simp [pair, sumSix, t, sixColumnExample]
    ring
  have p03 : pair (row t 0) (row t 3) = 0 := by
    simp [pair, sumSix, t, sixColumnExample]
    ring
  have p12 : pair (row t 1) (row t 2) = 0 := by
    simp [pair, sumSix, t, sixColumnExample]
    ring
  have p13 : pair (row t 1) (row t 3) = 0 := by
    simp [pair, sumSix, t, sixColumnExample]
    ring
  have p23 : pair (row t 2) (row t 3) = -6 := by
    simp [pair, sumSix, t, sixColumnExample]
    linear_combination 4 * hz
  have h2 : rook2 t = 0 := by rw [rook2_of_centered t hr, p01, p02, p03, p12, p13, p23]; norm_num
  have h3 : rook3 t = 0 := by
    rw [rook3_of_centered t hr]
    simp [sumSix, t, sixColumnExample]
    ring
  have hQ : (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j)) = -6 := by
    simp [sumSix, t, sixColumnExample]
    linear_combination (-4 * (z ^ 2 - z - 1)) * hz
  have hP : pairingCorrection t = -36 := by
    rw [pairingCorrection, p01, p02, p03, p12, p13, p23]
    norm_num
  refine ⟨t, hr, h2, h3, ?_, hP⟩
  rw [distinct4_of_centered _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3)]
  change pairingCorrection t - 6 * (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j)) = 0
  rw [hP, hQ]
  norm_num

private theorem finrank_le_one_of_single_support (S : Submodule ℂ (Fin 4 → ℂ))
    (h : ∀ u ∈ S, ∀ i j : Fin 4, i ≠ j → u i * u j = 0) : Module.finrank ℂ S ≤ 1 := by
  by_cases hS : S = ⊥
  · subst S
    rw [finrank_bot]
    exact Nat.zero_le _
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra! hx
    apply hS
    exact le_antisymm (fun x hx' => (Submodule.mem_bot ℂ).2 (hx x hx')) bot_le
  obtain ⟨x, hxS, hx0⟩ := hx
  have hi : ∃ i : Fin 4, x i ≠ 0 := by
    by_contra! hi
    exact hx0 (funext hi)
  obtain ⟨i, hi⟩ := hi
  have hSupport (u : Fin 4 → ℂ) (hu : u ∈ S) (j : Fin 4) (hji : j ≠ i) : u j = 0 := by
    have hxj : x j = 0 := (mul_eq_zero.1 (h x hxS i j hji.symm)).resolve_left hi
    by_contra huj
    have hui : u i = 0 := (mul_eq_zero.1 (h u hu i j hji.symm)).resolve_right huj
    have hs := h (x + u) (S.add_mem hxS hu) i j hji.symm
    simp only [Pi.add_apply, hui, hxj, add_zero, zero_add] at hs
    exact (mul_ne_zero hi huj) hs
  let f : S →ₗ[ℂ] ℂ := (LinearMap.proj i).comp S.subtype
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      exact he
    · rw [hSupport u.1 u.2 j hji, hSupport v.1 v.2 j hji]
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- Suppose the first six Fourier moments are used as coordinates of a row.
Only modes 1 and 2 need survive, and the mode-2 coefficients may have one
nonzero row. The dimension bound uses no cyclic invariance of the space. -/
theorem finrank_le_five_of_two_modes (V : Submodule ℂ (Mat4 (Fin 6)))
    (F : (Fin 6 → ℂ) ≃ₗ[ℂ] (Fin 6 → ℂ))
    (hModes : ∀ t ∈ V, ∀ i : Fin 4, ∀ k : Fin 6, k ≠ 1 → k ≠ 2 → F (row t i) k = 0)
    (hSparse : ∀ t ∈ V, ∀ i j : Fin 4, i ≠ j → F (row t i) 2 * F (row t j) 2 = 0) :
    Module.finrank ℂ V ≤ 5 := by
  let entryMap (i : Fin 4) : V →ₗ[ℂ] (Fin 6 → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun j : Fin 6 => (i, j)).comp V.subtype
  let mode (k : Fin 6) : V →ₗ[ℂ] (Fin 4 → ℂ) :=
    LinearMap.pi (fun i => (LinearMap.proj k).comp (F.toLinearMap.comp (entryMap i)))
  let S := (mode 2).range
  have hS : Module.finrank ℂ S ≤ 1 := by
    apply finrank_le_one_of_single_support
    rintro _ ⟨t, rfl⟩ i j hij
    exact hSparse t.1 t.2 i j hij
  let f : V →ₗ[ℂ] (Fin 4 → ℂ) × S := (mode 1).prod (mode 2).rangeRestrict
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    funext ⟨i, j⟩
    have hv : F (row x.1 i) = F (row y.1 i) := by
      funext k
      by_cases hk₁ : k = 1
      · subst k
        exact congrFun (congrArg Prod.fst he) i
      · by_cases hk₂ : k = 2
        · subst k
          exact congrFun (congrArg Subtype.val (congrArg Prod.snd he)) i
        · rw [hModes x.1 x.2 i k hk₁ hk₂, hModes y.1 y.2 i k hk₁ hk₂]
    exact congrFun (F.injective hv) j
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_fin_fun] at hdim
  omega

private def twoBlockEntry {R : Type*} [CommRing R] (w : R) (z : Fin 6 → R) : Fin 4 × Fin 6 → R :=
  let a := z 0
  let b := z 1
  let c := z 2
  let d := z 3
  let e := z 4
  let f := z 5
  let v := -1 - w
  fun p => (![![a + c, a*w + c*v, a*v + c*w, f, f*v, f*w],
    ![b, b*w, b*v, d, d*w, d*v],
    ![-b, -b*w, -b*v, e, e*w, e*v],
    ![-a + c, -a*w + c*v, -a*v + c*w, -f, -f*v, -f*w]] : Fin 4 → Fin 6 → R) p.1 p.2

set_option maxHeartbeats 1000000 in
private def twoBlockParam (w : ℂ) : (Fin 6 → ℂ) →ₗ[ℂ] Mat4 (Fin 6) where
  toFun := twoBlockEntry w
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [twoBlockEntry] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [twoBlockEntry] <;> ring

private theorem twoBlock_zero_of_pivots (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (z : Fin 6 → ℂ)
    (h₀ : twoBlockEntry w z (0, 0) = 0) (h₁ : twoBlockEntry w z (0, 1) = 0)
    (hb : twoBlockEntry w z (1, 0) = 0) (hd : twoBlockEntry w z (1, 3) = 0)
    (he : twoBlockEntry w z (2, 3) = 0) (hf : twoBlockEntry w z (0, 3) = 0) : z = 0 := by
  simp [twoBlockEntry] at h₀ h₁ hb hd he hf
  have hw' : 1 + 2*w ≠ 0 := by
    intro H
    have hSquare : (1 + 2*w)^2 = -3 := by linear_combination 4 * hw
    rw [H] at hSquare
    norm_num at hSquare
  have hc' : (1 + 2*w) * z 2 = 0 := by linear_combination w * h₀ - h₁
  have hc := (mul_eq_zero.1 hc').resolve_left hw'
  have ha : z 0 = 0 := by simpa [hc] using h₀
  funext j
  fin_cases j <;> simp [ha, hb, hc, hd, he, hf]

private theorem twoBlock_injective (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    Function.Injective (twoBlockParam w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h (i : Fin 4) (j : Fin 6) : twoBlockEntry w z (i, j) = 0 := congrFun hz (i, j)
  exact twoBlock_zero_of_pivots w hw z (h 0 0) (h 0 1) (h 1 0) (h 1 3) (h 2 3) (h 0 3)

private theorem twoBlock_equations (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (z : Fin 6 → ℂ) :
    let t := twoBlockEntry w z
    (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ rook2 t = 0 ∧ rook3 t = 0 ∧
    distinct4 (row t 0) (row t 1) (row t 2) (row t 3) = 0 := by
  let t := twoBlockEntry w z
  change (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ rook2 t = 0 ∧ rook3 t = 0 ∧
    distinct4 (row t 0) (row t 1) (row t 2) (row t 3) = 0
  have hr (i : Fin 4) : ∑ j, t (i, j) = 0 := by
    fin_cases i <;> simp [t, twoBlockEntry, sumSix] <;> ring
  have p01 : pair (row t 0) (row t 1) = 3 * (z 1 * z 2 + z 3 * z 5) := by
    simp [pair, row, t, twoBlockEntry, sumSix]
    linear_combination (2*((z 0-z 2) * z 1 - z 5 * z 3)) * hw
  have p02 : pair (row t 0) (row t 2) = 3 * (-z 1 * z 2 + z 4 * z 5) := by
    simp [pair, row, t, twoBlockEntry, sumSix]
    linear_combination (2*((z 0-z 2) * (-z 1) - z 5 * z 4)) * hw
  have p03 : pair (row t 0) (row t 3) = 0 := by
    simp [pair, row, t, twoBlockEntry, sumSix]
    linear_combination (2*((z 0-z 2) * (-z 0-z 2) - (z 5)^2)) * hw
  have p12 : pair (row t 1) (row t 2) = 0 := by
    simp [pair, row, t, twoBlockEntry, sumSix]
    linear_combination (2*(-(z 1)^2 + z 3 * z 4)) * hw
  have p13 : pair (row t 1) (row t 3) = 3 * (z 1 * z 2 - z 3 * z 5) := by
    simp [pair, row, t, twoBlockEntry, sumSix]
    linear_combination (2*(z 1 * (-z 0-z 2) + z 3 * z 5)) * hw
  have p23 : pair (row t 2) (row t 3) = 3 * (-z 1 * z 2 - z 4 * z 5) := by
    simp [pair, row, t, twoBlockEntry, sumSix]
    linear_combination (2*((-z 1) * (-z 0-z 2) + z 4 * z 5)) * hw
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [rook2_of_centered t hr, p01, p02, p03, p12, p13, p23]
    ring
  · rw [rook3_of_centered t hr]
    simp [t, twoBlockEntry, sumSix]
    linear_combination (-2*(z 1)^2*z 2 - (z 5)^2*(z 3+z 4)) * hw
  · have hQ : (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j)) =
        -3 * ((z 1)^2*(z 2)^2 + z 3*z 4*(z 5)^2) := by
      simp [t, twoBlockEntry, sumSix]
      linear_combination
        (2*(z 0)^2*(z 1)^2*(w^2+w+1) + ((z 1)^2*(z 2)^2 + z 3*z 4*(z 5)^2)*(4-2*(w^2+w+1))) * hw
    rw [distinct4_of_centered _ _ _ _ (hr 0) (hr 1) (hr 2) (hr 3)]
    change pairingCorrection t - 6 * (∑ j, t (0, j) * t (1, j) * t (2, j) * t (3, j)) = 0
    rw [pairingCorrection, p01, p02, p03, p12, p13, p23, hQ]
    ring

/-- A six-dimensional row-centred level space. In particular, the
dimension-five bound cannot be used to prove the uncentred bound of eight. -/
theorem exists_six_dimensional_centered_level : ∃ V : Submodule ℂ (Mat4 (Fin 6)),
    Module.finrank ℂ V = 6 ∧ ∀ t ∈ V,
      (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ rook2 t = 0 ∧ rook3 t = 0 ∧
      distinct4 (row t 0) (row t 1) (row t 2) (row t 3) = 0 := by
  have hs : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let w : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2
  have hw : w ^ 2 + w + 1 = 0 := by
    dsimp [w]
    linear_combination hs / 4
  refine ⟨(twoBlockParam w).range, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (twoBlock_injective w hw), Module.finrank_fin_fun]
  · rintro _ ⟨z, rfl⟩
    exact twoBlock_equations w hw z

/-
Application to a row-centred level space that contains every matrix
whose rows are multiples of one primitive mode w, where w(j) = z^j and z
is a primitive sixth root. The following coefficient argument supplies
the hypotheses of finrank_le_five_of_two_modes.

For any t in the space, write m_k(i) = sum_j w(j)^k * t(i,j).
Polarizing the quadratic with a base vector in row r shows that the sum
of m_1 over rows other than r is zero. Hence every m_1(i) is zero.
Polarizing the cubic with base vectors in two distinct rows shows that
the sum of m_2 on the two complementary rows is zero. This is true for
every pair, so each m_2(i) is zero.
Polarizing the quartic with base vectors in three distinct rows removes
the pairing correction, since one pairing always joins two base vectors
and sum_j w(j)^2 = 0. The remaining term is a nonzero multiple of m_3 on
the complementary row. Thus each m_3(i) is zero. Centering also gives
m_0(i) = 0, so only Fourier modes 1 and 2 can remain.

Subtract the mode-1 part, which belongs to the space by hypothesis. If
the remaining mode-2 direction has row weights b(i), polarize the
quartic twice in that direction and once in each of two distinct base
rows. Every bilinear factor of the pairing correction vanishes, since
the frequency sums are 2, 3, or 4. The single-column term is a nonzero
multiple of b(i) b(j) on the two complementary rows, since
sum_j w(j)^6 = 6. Therefore b has at most one nonzero row.
-/

/-!
The three directions below are the complement from the exact elimination in the
user-supplied `test_v6_ext.py` and `test_v6_gram.py`, scaled by three to use integer
coefficients in `w`. The Gram calculation is proved by polynomial expansion.

For the broader search, Diego Mirandola and Gilles Zémor, *Critical pairs for the
Product Singleton Bound*, Theorem 2.12, https://arxiv.org/abs/1501.06419, classify
pairs under a Product-MDS hypothesis. The present Schur-square obstruction leaves
that hypothesis to be established. Miles Reid, *The complete intersection of two
or more quadrics*, https://mreid.warwick.ac.uk/3folds/qu.pdf, provides context for
the common isotropic spaces of pencils. The certificate below uses only the
explicit rook polynomials, finite arithmetic, and linear algebra.
-/

private def extensionComplement {R : Type*} [CommRing R] (w : R) (z : Fin 3 → R) : Fin 4 × Fin 6 → R :=
  let a := z 0
  let b := z 1
  let c := z 2
  fun p => (![![0, 0, 3*a, 0, 3*b, -3*w*b],
    ![0, 3*c, 3*(1+w)*c, 0, (w-1)*a+3*w*b-3*c, (-2-w)*a-3*b-3*(1+w)*c],
    ![(4+2*w)*c, (1+2*w)*c, (1-w)*c, 0, (w-1)*a+3*w*b-3*c, (-2-w)*a-3*b-3*(1+w)*c],
    ![-2*w*a, (2+2*w)*a, a, (2-2*w)*b, (-1-2*w)*b, (2+w)*b]] : Fin 4 → Fin 6 → R) p.1 p.2

def extensionComplementMap (w : ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] Mat4 (Fin 6) where
  toFun := extensionComplement w
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [extensionComplement] <;> ring
  map_smul' a x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [extensionComplement] <;> ring

private def extensionGram (w : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-48, -30+30*w, -36-18*w; -30+30*w, 72*w, 18; -36-18*w, 18, -36-36*w]

private theorem extensionGram_det (w : ℂ) (hw : w^2+w+1=0) :
    (extensionGram w).det = 116640 := by
  simp [Matrix.det_fin_three, extensionGram]
  linear_combination (9072*w-29808) * hw

private theorem distinct2_eq (a b : ι → ℂ) :
    distinct2 a b = (∑ j, a j) * (∑ j, b j) - pair a b := by
  unfold distinct2 pair
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h (l : ι) : (if j = l then 0 else a j * b l) = a j * (if j = l then 0 else b l) := by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun l _ => h l), ← Finset.mul_sum, sum_except_one]
  ring

private theorem extensionComplement_quadratic (w : ℂ) (hw : w^2+w+1=0) (z : Fin 3 → ℂ) :
    2 * rook2 (extensionComplementMap w z) = dotProduct z ((extensionGram w).mulVec z) := by
  change 2 * rook2 (extensionComplement w z) = _
  simp [rook2_as_row_pairs, distinct2_eq, pair, row, extensionComplement, sumSix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, extensionGram]
  linear_combination (-4*(z 0)^2-24*(z 1)^2-12*(z 2)^2-
    12*z 0*z 1-12*z 0*z 2-24*z 1*z 2) * hw

private theorem extensionGram_symmetric (w : ℂ) (x y : Fin 3 → ℂ) :
    dotProduct x ((extensionGram w).mulVec y) = dotProduct y ((extensionGram w).mulVec x) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, extensionGram]
  ring

/-- At most one dimension in the specified complement can satisfy the quadratic
level equation on a linear space. -/
theorem finrank_extensionComplement_le_one {L : Submodule ℂ (Mat4 (Fin 6))}
    (hL : ∀ x ∈ L, rook2 x = 0) {w : ℂ} (hw : w^2+w+1=0) :
    Module.finrank ℂ (L.comap (extensionComplementMap w)) ≤ 1 := by
  let W := L.comap (extensionComplementMap w)
  let A := (extensionGram w).mulVecLin
  have hinj : Function.Injective A := Matrix.mulVec_injective_of_det_ne_zero (by
    rw [extensionGram_det w hw]; norm_num)
  have hQ (z) (hz : z ∈ W) : dotProduct z (A z) = 0 := by
    change extensionComplementMap w z ∈ L at hz
    change dotProduct z ((extensionGram w).mulVec z) = 0
    rw [← extensionComplement_quadratic w hw, hL _ hz, mul_zero]
  let f : W →ₗ[ℂ] Module.Dual ℂ (Fin 3 → ℂ) :=
    (dotProductEquiv ℂ (Fin 3)).toLinearMap.comp (A.comp W.subtype)
  have hf : Function.Injective f :=
    (dotProductEquiv ℂ (Fin 3)).injective.comp (hinj.comp Subtype.val_injective)
  have hle : f.range ≤ W.dualAnnihilator := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    change dotProduct (A x.1) y = 0
    rw [dotProduct_comm]
    have h := hQ (x.1 + y) (W.add_mem x.2 hy)
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, hQ _ x.2, hQ _ hy,
      zero_add, add_zero] at h
    have hs : dotProduct x.1 (A y) = dotProduct y (A x.1) := extensionGram_symmetric w _ _
    linear_combination (h - hs) / 2
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hf] at hdim
  have hrank := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [Module.finrank_fin_fun] at hrank
  change Module.finrank ℂ W ≤ 1
  omega

/-- The quadratic cap once a space extending the two-block example is contained
in the nine-dimensional span found by linearization. -/
theorem finrank_le_seven_of_twoBlock_containment {L : Submodule ℂ (Mat4 (Fin 6))}
    (hL : ∀ x ∈ L, rook2 x = 0) {w : ℂ} (hw : w^2+w+1=0)
    (hOld : (twoBlockParam w).range ≤ L)
    (hNew : L ≤ (twoBlockParam w).range ⊔ (extensionComplementMap w).range) :
    Module.finrank ℂ L ≤ 7 := by
  let E := extensionComplementMap w
  let W := (L.comap E).map E
  have hW : W ≤ L := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  have hEq : L = (twoBlockParam w).range ⊔ W := by
    apply le_antisymm _ (sup_le hOld hW)
    intro x hx
    rcases Submodule.mem_sup.mp (hNew hx) with ⟨u, hu, e, ⟨z, rfl⟩, rfl⟩
    have hz : E z ∈ L := by
      rw [← add_sub_cancel_right (E z) u, add_comm (E z) u]
      exact L.sub_mem hx (hOld hu)
    exact Submodule.mem_sup.mpr ⟨u, hu, E z, ⟨z, hz, rfl⟩, rfl⟩
  have hRankW : Module.finrank ℂ W ≤ 1 :=
    (Submodule.finrank_map_le _ _).trans (finrank_extensionComplement_le_one hL hw)
  have hRankU : Module.finrank ℂ (twoBlockParam w).range = 6 := by
    rw [LinearMap.finrank_range_of_inj (twoBlock_injective w hw), Module.finrank_fin_fun]
  have hRank := Submodule.finrank_sup_add_finrank_inf_eq (twoBlockParam w).range W
  rw [hRankU, ← hEq] at hRank
  omega

private def sumFin {R : Type*} [AddMonoid R] : (n : ℕ) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin n (fun i => f i.succ)

private theorem sumFin_eq {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Fin n → R) :
    sumFin n f = ∑ i, f i := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => rw [sumFin, Fin.sum_univ_succ, ih]

private def rookValue {R : Type*} [CommRing R] (k : Fin 4) (t : Fin 4 × Fin 6 → R) : R :=
  if k = 0 then sumFin 4 fun a => sumFin 6 fun j => t (a, j)
  else if k = 1 then sumFin 6 fun j => sumFin 6 fun l => if j = l then 0 else
    t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (0, j) * t (3, l) +
      t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l)
  else if k = 2 then sumFin 6 fun j => sumFin 6 fun l => sumFin 6 fun m =>
    if j = l ∨ j = m ∨ l = m then 0 else
      t (0, j) * t (1, l) * t (2, m) + t (0, j) * t (1, l) * t (3, m) +
        t (0, j) * t (2, l) * t (3, m) + t (1, j) * t (2, l) * t (3, m)
  else sumFin 6 fun j => sumFin 6 fun l => sumFin 6 fun m => sumFin 6 fun n =>
    if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0
    else t (0, j) * t (1, l) * t (2, m) * t (3, n)

private theorem map_rookValue {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 4) (t : Fin 4 × Fin 6 → R) :
    f (rookValue k t) = rookValue k (fun ij => f (t ij)) := by
  by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;>
    simp only [rookValue, sumFin_eq, h0, h1, h2, ite_true, ite_false, map_sum, apply_ite f,
      map_zero, map_add, map_mul]

private theorem rookValue_eq_zero_of_level {x : Mat4 (Fin 6)}
    (h : (∑ a, ∑ j, x (a, j)) = 0 ∧ rook2 x = 0 ∧ rook3 x = 0 ∧ rook4 x = 0)
    (k : Fin 4) : rookValue k x = 0 := by
  rcases h with ⟨h1, h2, h3, h4⟩
  fin_cases k <;> simp (config := {decide := true}) only [rookValue, sumFin_eq, ite_true, ite_false]
  · exact h1
  · simpa (config := {decide := true}) only [rook2, Fin.sum_univ_four, ite_true, ite_false,
      add_zero, zero_add, add_assoc] using h2
  · simpa (config := {decide := true}) only [rook3, Fin.sum_univ_four, ite_true, ite_false,
      add_zero, zero_add, add_assoc] using h3
  · exact h4

/-- First variation obtained by substituting `t + ε x` with `ε² = 0`. -/
def rookFirstVariation {R : Type*} [CommRing R] (k : Fin 4) (t x : Fin 4 × Fin 6 → R) : R :=
  (rookValue (R := QuadraticAlgebra R 0 0) k (fun ij => ⟨t ij, x ij⟩)).im

section VariationProofs

attribute [local irreducible] rookValue

/-- Every first variation vanishes when the base and test directions belong to
the same level space. This links polynomial computations to the gap equations. -/
theorem rookFirstVariation_eq_zero {L : Submodule ℂ (Mat4 (Fin 6))}
    (hL : ∀ x ∈ L, (∑ a, ∑ j, x (a, j)) = 0 ∧ rook2 x = 0 ∧ rook3 x = 0 ∧ rook4 x = 0)
    (k : Fin 4) {t x : Mat4 (Fin 6)} (ht : t ∈ L) (hx : x ∈ L) :
    rookFirstVariation k t x = 0 := by
  let p : Polynomial ℂ := rookValue k fun ij => Polynomial.C (t ij) + Polynomial.X * Polynomial.C (x ij)
  have hp : p = 0 := by
    apply Polynomial.funext
    intro s
    change Polynomial.evalRingHom s (rookValue k (fun ij =>
      Polynomial.C (t ij) + Polynomial.X * Polynomial.C (x ij))) = Polynomial.eval s 0
    rw [map_rookValue, Polynomial.eval_zero]
    simp only [map_add, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X]
    have hentry : (fun ij => t ij + s * x ij) = t + s • x := rfl
    rw [hentry]
    have hs := L.add_mem ht (L.smul_mem s hx)
    exact rookValue_eq_zero_of_level (hL _ hs) k
  let F := Polynomial.eval₂RingHom (algebraMap ℂ (QuadraticAlgebra ℂ 0 0)) QuadraticAlgebra.omega
  have he := congrArg F hp
  change F (rookValue k (fun ij => Polynomial.C (t ij) + Polynomial.X * Polynomial.C (x ij))) = F 0 at he
  rw [map_rookValue, map_zero] at he
  have hentry (ij : Fin 4 × Fin 6) :
      F (Polynomial.C (t ij) + Polynomial.X * Polynomial.C (x ij)) = ⟨t ij, x ij⟩ := by
    simp only [F, map_add, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.omega]
  simp only [hentry] at he
  exact congrArg QuadraticAlgebra.im he

private def mapSquareZero {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    QuadraticAlgebra R 0 0 →+* QuadraticAlgebra S 0 0 where
  toFun x := ⟨f x.re, f x.im⟩
  map_zero' := by ext <;> simp
  map_one' := QuadraticAlgebra.ext (map_one f) (map_zero f)
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private theorem map_rookFirstVariation {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 4) (t x : Fin 4 × Fin 6 → R) :
    f (rookFirstVariation k t x) = rookFirstVariation k (fun ij => f (t ij)) (fun ij => f (x ij)) := by
  unfold rookFirstVariation
  have h := map_rookValue (mapSquareZero f) k (fun ij => (⟨t ij, x ij⟩ : QuadraticAlgebra R 0 0))
  exact congrArg (fun z : QuadraticAlgebra S 0 0 => z.im) h

end VariationProofs

private def extensionSamples : Fin 15 → Fin 4 × (Fin 6 → ℤ) :=
  ![(0, 0), (1, ![0,0,0,0,0,1]), (1, ![0,0,0,0,1,0]), (1, ![0,0,0,1,0,0]),
    (1, ![0,0,1,0,0,0]), (1, ![0,1,0,0,0,0]), (1, ![1,0,0,0,0,0]),
    (2, ![0,0,0,0,0,1]), (2, ![0,0,1,0,0,0]), (2, ![0,1,0,0,0,0]),
    (2, ![0,0,0,0,1,1]), (2, ![0,0,0,1,1,0]), (2, ![0,1,1,0,0,0]),
    (3, ![1,1,0,0,0,0]), (3, ![-1,1,0,0,0,0])]

private def extensionPivots : Fin 15 → Fin 4 × Fin 6 :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),
    (1,4),(2,0),(2,1),(2,3),(3,3)]

private def extensionMinor {R : Type*} [CommRing R] (w : R) : Matrix (Fin 15) (Fin 15) R :=
  fun i j => rookFirstVariation (extensionSamples i).1
    (twoBlockEntry w fun k => (extensionSamples i).2 k) (Pi.single (extensionPivots j) 1)

private theorem of_checked_fin_grid {m n : ℕ} {P : Fin m → Fin n → Prop}
    (D : ∀ i j, Decidable (P i j))
    (h : (List.finRange m).all (fun i => (List.finRange n).all (fun j => @decide (P i j) (D i j))) = true)
    (i : Fin m) (j : Fin n) : P i j := by
  have hi := List.all_eq_true.mp h i (by simp)
  exact @of_decide_eq_true (P i j) (D i j) (List.all_eq_true.mp hi j (by simp))

private def extensionMinorModSeven : Matrix (Fin 15) (Fin 15) (ZMod 7) :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 6],
    ![0, 0, 0, 6, 5, 3, 0, 0, 0, 6, 5, 0, 0, 0, 6],
    ![0, 0, 0, 6, 5, 3, 0, 0, 0, 0, 0, 0, 0, 6, 6],
    ![6, 3, 5, 0, 0, 0, 5, 6, 3, 0, 0, 5, 6, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 2, 4, 0, 0, 6, 5, 0, 0],
    ![1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 0, 0, 5, 0],
    ![0, 0, 0, 0, 0, 0, 2, 4, 1, 0, 0, 2, 4, 0, 0],
    ![5, 6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![3, 3, 3, 1, 1, 1, 0, 0, 0, 5, 3, 0, 0, 5, 6],
    ![0, 0, 0, 2, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ![5, 6, 3, 0, 0, 0, 4, 6, 3, 6, 6, 0, 2, 1, 0],
    ![0, 0, 0, 6, 6, 6, 0, 0, 0, 6, 6, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 6, 6, 0, 0, 1, 6]]

private def extensionMinorModSevenInverse : Matrix (Fin 15) (Fin 15) (ZMod 7) :=
  ![![0, 0, 0, 0, 0, 0, 5, 3, 0, 1, 4, 0, 0, 2, 5],
    ![0, 0, 0, 0, 0, 0, 6, 3, 0, 2, 4, 0, 0, 2, 5],
    ![0, 0, 0, 0, 0, 0, 3, 3, 0, 4, 4, 0, 0, 2, 5],
    ![0, 6, 1, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 1, 6],
    ![0, 2, 4, 4, 0, 0, 0, 5, 0, 0, 0, 4, 0, 1, 6],
    ![0, 2, 2, 2, 0, 0, 0, 6, 0, 0, 0, 2, 0, 1, 6],
    ![4, 4, 3, 4, 1, 3, 0, 1, 4, 6, 1, 5, 4, 6, 1],
    ![2, 2, 5, 2, 2, 4, 0, 4, 3, 1, 4, 6, 5, 5, 6],
    ![5, 5, 2, 5, 4, 0, 0, 3, 5, 5, 3, 1, 0, 3, 2],
    ![0, 0, 5, 2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 6, 6],
    ![0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4],
    ![1, 1, 6, 1, 0, 4, 0, 2, 2, 4, 2, 3, 3, 4, 1],
    ![3, 3, 4, 3, 0, 3, 0, 6, 0, 5, 6, 2, 2, 5, 3],
    ![0, 0, 4, 3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem extensionMinor_mod_seven_row (i : Fin 15) :
    (List.finRange 15).all (fun j => decide
      (extensionMinor (2 : ZMod 7) i j = extensionMinorModSeven i j)) = true := by
  fin_cases i <;> decide +kernel

private theorem extensionMinor_mod_seven :
    extensionMinor (2 : ZMod 7) = extensionMinorModSeven := by
  ext i j
  exact of_decide_eq_true (List.all_eq_true.mp (extensionMinor_mod_seven_row i) j (by simp))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem extensionMinor_mod_seven_inverse :
    extensionMinorModSevenInverse * extensionMinorModSeven = 1 := by
  ext i j
  exact of_checked_fin_grid (P := fun a b => (extensionMinorModSevenInverse * extensionMinorModSeven) a b =
    (1 : Matrix (Fin 15) (Fin 15) (ZMod 7)) a b) (fun _ _ => inferInstance) (by decide +kernel) i j

private theorem extensionMinor_mod_seven_det_ne_zero : (extensionMinor (2 : ZMod 7)).det ≠ 0 := by
  rw [extensionMinor_mod_seven]
  have h := congrArg Matrix.det extensionMinor_mod_seven_inverse
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, mul_zero] at h
  exact (by decide : (0 : ZMod 7) ≠ 1) h

private abbrev Eisenstein := QuadraticAlgebra ℤ (-1) (-1)

private def evaluateEisenstein {R : Type*} [CommRing R] (u : R) (hu : u^2+u+1=0) :
    Eisenstein →+* R :=
  (QuadraticAlgebra.lift ⟨u, by
    change u * u = (-1 : ℤ) • (1 : R) + (-1 : ℤ) • u
    simp only [neg_smul, one_smul]
    linear_combination hu⟩).toRingHom

private theorem evaluateEisenstein_omega {R : Type*} [CommRing R] (u : R) (hu : u^2+u+1=0) :
    evaluateEisenstein u hu QuadraticAlgebra.omega = u := by
  simp [evaluateEisenstein, QuadraticAlgebra.omega, QuadraticAlgebra.lift]

private theorem evaluateEisenstein_complex_injective {w : ℂ} (hw : w^2+w+1=0) :
    Function.Injective (evaluateEisenstein w hw) := by
  have hIm : w.im ≠ 0 := by
    intro hi
    have h := congrArg Complex.re hw
    simp [pow_two, Complex.mul_re, hi] at h
    nlinarith [sq_nonneg (w.re + 1/2)]
  have hEval (z : Eisenstein) : evaluateEisenstein w hw z = (z.re : ℂ) + (z.im : ℂ) * w := by
    simp [evaluateEisenstein, QuadraticAlgebra.lift, Algebra.smul_def]
  intro a b h
  rw [hEval, hEval] at h
  have hi := congrArg Complex.im h
  simp [Complex.mul_im] at hi
  have hb : a.im = b.im := hi.resolve_right hIm
  rw [hb] at h
  have ha : a.re = b.re := by exact_mod_cast add_right_cancel h
  exact QuadraticAlgebra.ext ha hb

private theorem map_twoBlockEntry {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : R) (z : Fin 6 → R) :
    (fun ij => f (twoBlockEntry w z ij)) = twoBlockEntry (f w) (fun i => f (z i)) := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [twoBlockEntry]

private theorem map_extensionMinor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : R) : (extensionMinor w).map f = extensionMinor (f w) := by
  ext i j
  change f (rookFirstVariation (extensionSamples i).1
    (twoBlockEntry w (fun k => (extensionSamples i).2 k)) (Pi.single (extensionPivots j) 1)) = _
  rw [map_rookFirstVariation, map_twoBlockEntry]
  have hx : (fun ij => f ((Pi.single (extensionPivots j) (1 : R) : Fin 4 × Fin 6 → R) ij)) =
      Pi.single (extensionPivots j) (1 : S) := by
    funext ij
    by_cases h : ij = extensionPivots j <;> simp [h]
  rw [hx]
  simp only [extensionMinor, map_intCast]

private theorem evaluateEisenstein_minor_det {R : Type*} [CommRing R] (u : R) (hu : u^2+u+1=0) :
    evaluateEisenstein u hu ((extensionMinor (QuadraticAlgebra.omega : Eisenstein)).det) =
      (extensionMinor u).det := by
  rw [RingHom.map_det]
  change ((extensionMinor (QuadraticAlgebra.omega : Eisenstein)).map (evaluateEisenstein u hu)).det = _
  rw [map_extensionMinor, evaluateEisenstein_omega]

private theorem extensionMinor_det_ne_zero {w : ℂ} (hw : w^2+w+1=0) :
    (extensionMinor w).det ≠ 0 := by
  let f := evaluateEisenstein w hw
  intro hz
  have h0 : (extensionMinor (QuadraticAlgebra.omega : Eisenstein)).det = 0 :=
    evaluateEisenstein_complex_injective hw
      ((evaluateEisenstein_minor_det w hw).trans (hz.trans (map_zero f).symm))
  apply extensionMinor_mod_seven_det_ne_zero
  rw [← evaluateEisenstein_minor_det (2 : ZMod 7) (by decide), h0, map_zero]

section VariationLinear

attribute [local irreducible] rookValue

private def squareZeroToQuadratic : TrivSqZeroExt ℂ ℂ →+* QuadraticAlgebra ℂ 0 0 where
  toFun z := ⟨z.fst, z.snd⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · change x.fst * y.fst = x.fst * y.fst + 0 * x.snd * y.snd
      simp
    · change x.fst * y.snd + x.snd * y.fst = x.fst * y.snd + x.snd * y.fst + 0 * x.snd * y.snd
      simp

private def rookFirstVariationLinear (k : Fin 4) (t : Mat4 (Fin 6)) :
    Mat4 (Fin 6) →ₗ[ℂ] ℂ :=
  (rookValue (R := TrivSqZeroExt ℂ (Mat4 (Fin 6) →ₗ[ℂ] ℂ)) k
    (fun ij => ⟨t ij, LinearMap.proj ij⟩)).snd

private theorem rookFirstVariationLinear_apply (k : Fin 4) (t x : Mat4 (Fin 6)) :
    rookFirstVariationLinear k t x = rookFirstVariation k t x := by
  let ev : (Mat4 (Fin 6) →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => f x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let f := squareZeroToQuadratic.comp (TrivSqZeroExt.map ev).toRingHom
  let z : Fin 4 × Fin 6 → TrivSqZeroExt ℂ (Mat4 (Fin 6) →ₗ[ℂ] ℂ) :=
    fun ij => ⟨t ij, LinearMap.proj ij⟩
  have hmap : (fun ij => f (z ij)) = fun ij => ⟨t ij, x ij⟩ := by
    funext ij
    apply QuadraticAlgebra.ext
    · change (TrivSqZeroExt.map ev (z ij)).fst = t ij
      rw [TrivSqZeroExt.fst_map]
      rfl
    · change (TrivSqZeroExt.map ev (z ij)).snd = x ij
      rw [TrivSqZeroExt.snd_map]
      rfl
  have h := map_rookValue f k z
  rw [hmap] at h
  have he := congrArg (fun u : QuadraticAlgebra ℂ 0 0 => u.im) h
  change (TrivSqZeroExt.map ev (rookValue k z)).snd = _ at he
  rw [TrivSqZeroExt.snd_map] at he
  exact he

end VariationLinear

private def sampledVariations (w : ℂ) : Mat4 (Fin 6) →ₗ[ℂ] (Fin 15 → ℂ) :=
  LinearMap.pi fun i => rookFirstVariationLinear (extensionSamples i).1
    (twoBlockEntry w (fun k => (extensionSamples i).2 k))

private theorem sampledVariations_apply (w : ℂ) (x : Mat4 (Fin 6)) (i : Fin 15) :
    sampledVariations w x i = rookFirstVariation (extensionSamples i).1
      (twoBlockEntry w (fun k => (extensionSamples i).2 k)) x :=
  rookFirstVariationLinear_apply _ _ _

private theorem sampledVariations_surjective {w : ℂ} (hw : w^2+w+1=0) :
    Function.Surjective (sampledVariations w) := by
  have hm : Function.Surjective (extensionMinor w).mulVec :=
    (Matrix.mulVecLin (extensionMinor w)).injective_iff_surjective.mp
      (Matrix.mulVec_injective_of_det_ne_zero (extensionMinor_det_ne_zero hw))
  intro y
  obtain ⟨z, hz⟩ := hm y
  refine ⟨∑ j : Fin 15, z j • Pi.single (extensionPivots j) (1 : ℂ), ?_⟩
  rw [← hz, map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, sampledVariations_apply,
    Matrix.mulVec, dotProduct, extensionMinor, mul_comm]

private theorem sampledVariations_kernel_dimension {w : ℂ} (hw : w^2+w+1=0) :
    Module.finrank ℂ (sampledVariations w).ker = 9 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sampledVariations w)
  rw [LinearMap.range_eq_top.mpr (sampledVariations_surjective hw), finrank_top] at h
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h
  omega

private theorem map_extensionComplement {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : R) (z : Fin 3 → R) :
    (fun ij => f (extensionComplement w z ij)) = extensionComplement (f w) (fun i => f (z i)) := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [extensionComplement, map_ofNat]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem samples_annihilate_complement_exact (i : Fin 15) (j : Fin 3) :
    rookFirstVariation (extensionSamples i).1
      (twoBlockEntry (QuadraticAlgebra.omega : Eisenstein) (fun k => (extensionSamples i).2 k))
      (extensionComplement QuadraticAlgebra.omega (Pi.single j 1)) = 0 := by
  exact of_checked_fin_grid (P := fun a b => rookFirstVariation (extensionSamples a).1
    (twoBlockEntry (QuadraticAlgebra.omega : Eisenstein) (fun k => (extensionSamples a).2 k))
    (extensionComplement QuadraticAlgebra.omega (Pi.single b 1)) = 0)
    (fun _ _ => inferInstance) (by decide +kernel) i j

private theorem complement_le_sampledKernel {w : ℂ} (hw : w^2+w+1=0) :
    (extensionComplementMap w).range ≤ (sampledVariations w).ker := by
  rintro _ ⟨z, rfl⟩
  rw [LinearMap.mem_ker]
  have hBasis (j : Fin 3) : sampledVariations w (extensionComplementMap w (Pi.single j 1)) = 0 := by
    funext i
    rw [sampledVariations_apply]
    let f := evaluateEisenstein w hw
    have h := congrArg f (samples_annihilate_complement_exact i j)
    rw [map_rookFirstVariation, map_zero, map_twoBlockEntry, map_extensionComplement,
      evaluateEisenstein_omega] at h
    have hm : (fun k => f ((Pi.single j (1 : Eisenstein) : Fin 3 → Eisenstein) k)) = Pi.single j (1 : ℂ) := by
      funext k
      by_cases hk : k = j <;> simp [hk, f]
    rw [hm] at h
    simp only [map_intCast] at h
    exact h
  let B := Pi.basisFun ℂ (Fin 3)
  have hz : (∑ j : Fin 3, z j • Pi.single j (1 : ℂ)) = z := by
    simpa only [B, Pi.basisFun_apply, Pi.basisFun_repr] using B.sum_repr z
  rw [← hz, map_sum, map_sum]
  simp only [map_smul, hBasis, smul_zero, Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in
private theorem twoBlock_and_complement_rank {w : ℂ} (hw : w^2+w+1=0) :
    Module.finrank ℂ (((twoBlockParam w).range ⊔ (extensionComplementMap w).range) :
      Submodule ℂ (Mat4 (Fin 6))) = 9 := by
  let g := (twoBlockParam w).coprod (extensionComplementMap w)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨z, u⟩ hg0
    have h (i : Fin 4) (j : Fin 6) : twoBlockEntry w z (i, j) + extensionComplement w u (i, j) = 0 :=
      congrFun hg0 (i, j)
    have hz := twoBlock_zero_of_pivots w hw z
      (by simpa [extensionComplement] using h 0 0) (by simpa [extensionComplement] using h 0 1)
      (by simpa [extensionComplement] using h 1 0) (by simpa [extensionComplement] using h 1 3)
      (by simpa [extensionComplement] using h 2 3) (by simpa [extensionComplement] using h 0 3)
    subst z
    have ha := h 0 2
    have hb := h 0 4
    have hc := h 1 1
    simp [twoBlockEntry, extensionComplement, mul_eq_zero] at ha hb hc
    have hu : u = 0 := by funext i; fin_cases i <;> simp [ha, hb, hc]
    exact Prod.ext rfl hu
  rw [← LinearMap.range_coprod, LinearMap.finrank_range_of_inj hg, Module.finrank_prod,
    Module.finrank_fin_fun, Module.finrank_fin_fun]

/-- Any level space containing the six-dimensional two-block construction has
dimension at most seven. The finite rank certificate uses fifteen first variations
and verifies an inverse for their selected minor after reduction modulo seven. -/
theorem finrank_le_seven_of_twoBlock_level {L : Submodule ℂ (Mat4 (Fin 6))}
    (hL : ∀ x ∈ L, (∑ a, ∑ j, x (a, j)) = 0 ∧ rook2 x = 0 ∧ rook3 x = 0 ∧ rook4 x = 0)
    {w : ℂ} (hw : w^2+w+1=0) (hOld : (twoBlockParam w).range ≤ L) : Module.finrank ℂ L ≤ 7 := by
  have hK : L ≤ (sampledVariations w).ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext i
    rw [sampledVariations_apply]
    let z : Fin 6 → ℂ := fun k => (extensionSamples i).2 k
    have ht : twoBlockParam w z ∈ L := hOld ⟨z, rfl⟩
    exact rookFirstVariation_eq_zero hL _ ht hx
  have hle := sup_le (hOld.trans hK) (complement_le_sampledKernel hw)
  have he := Submodule.eq_of_le_of_finrank_eq hle
    ((twoBlock_and_complement_rank hw).trans (sampledVariations_kernel_dimension hw).symm)
  exact finrank_le_seven_of_twoBlock_containment (fun x hx => (hL x hx).2.1) hw hOld
    (by simpa only [he] using hK)

section GlobalQuadratic

private abbrev Mat46 := Mat4 (Fin 6)

private def totalSum (x : Mat46) : ℂ := ∑ a : Fin 4, ∑ j : Fin 6, x (a, j)

private def marginOperator (c : ℂ) : Mat46 →ₗ[ℂ] Mat46 where
  toFun x p := c * x p - rowSum x p.1 - colSum x p.2
  map_add' x y := by
    funext p
    simp only [rowSum, colSum, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' z x := by
    funext p
    simp only [rowSum, colSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

private theorem rowSum_marginOperator (c : ℂ) (x : Mat46) (a : Fin 4) :
    rowSum (marginOperator c x) a = (c - 6) * rowSum x a - totalSum x := by
  have hCol : (∑ j, colSum x j) = totalSum x := Finset.sum_comm
  change (∑ j : Fin 6, (c * x (a, j) - rowSum x a - colSum x j)) = _
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hCol]
  change c * rowSum x a - 6 * rowSum x a - totalSum x = _
  ring

private theorem colSum_marginOperator (c : ℂ) (x : Mat46) (j : Fin 6) :
    colSum (marginOperator c x) j = (c - 4) * colSum x j - totalSum x := by
  change (∑ a : Fin 4, (c * x (a, j) - rowSum x a - colSum x j)) = _
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change c * colSum x j - totalSum x - 4 * colSum x j = _
  ring

private theorem totalSum_marginOperator (c : ℂ) (x : Mat46) :
    totalSum (marginOperator c x) = (c - 10) * totalSum x := by
  change (∑ a, rowSum (marginOperator c x) a) = _
  simp only [rowSum_marginOperator, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (c - 6) * totalSum x - 4 * totalSum x = _
  ring

private theorem marginOperator_one_injective : Function.Injective (marginOperator 1) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have ht := totalSum_marginOperator 1 x
  have ht0 : totalSum x = 0 := by
    have hZero : totalSum (0 : Mat46) = 0 := by simp [totalSum]
    rw [hx, hZero] at ht
    linear_combination (1/9 : ℂ) * ht
  have hr (a) : rowSum x a = 0 := by
    have h := rowSum_marginOperator 1 x a
    have hZero : rowSum (0 : Mat46) a = 0 := by simp [rowSum]
    rw [hx, hZero, ht0, sub_zero] at h
    linear_combination (1/5 : ℂ) * h
  have hc (j) : colSum x j = 0 := by
    have h := colSum_marginOperator 1 x j
    have hZero : colSum (0 : Mat46) j = 0 := by simp [colSum]
    rw [hx, hZero, ht0, sub_zero] at h
    linear_combination (1/3 : ℂ) * h
  funext ⟨a, j⟩
  have h := congrFun hx (a, j)
  change 1 * x (a, j) - rowSum x a - colSum x j = 0 at h
  simpa [hr, hc] using h

private theorem dotProduct_marginOperator (c : ℂ) (x y : Mat46) :
    dotProduct x (marginOperator c y) = c * dotProduct x y -
      (∑ a, rowSum x a * rowSum y a) - ∑ j, colSum x j * colSum y j := by
  have h (a : Fin 4) (j : Fin 6) : x (a, j) * (marginOperator c y) (a, j) =
      c * (x (a, j) * y (a, j)) - x (a, j) * rowSum y a - x (a, j) * colSum y j := by
    change x (a, j) * (c * y (a, j) - rowSum y a - colSum y j) = _
    ring
  unfold dotProduct
  simp only [Fintype.sum_prod_type, h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hc : (∑ a : Fin 4, ∑ j, x (a, j) * colSum y j) = ∑ j, colSum x j * colSum y j := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, colSum]
  rw [hc]
  rfl

private theorem dotProduct_marginOperator_symm (c : ℂ) (x y : Mat46) :
    dotProduct x (marginOperator c y) = dotProduct y (marginOperator c x) := by
  rw [dotProduct_marginOperator, dotProduct_marginOperator, dotProduct_comm x y]
  simp only [mul_comm]

/-!
The quadratic calculation follows the permanent-Hessian approach of Thierry Mignon and
Nicolas Ressayre, *A quadratic bound for the determinant and permanent problem*,
IMRN (2004), 4241–4253, https://doi.org/10.1155/S1073792804142566. Here the
rectangular identity and nondegeneracy follow directly from the row and column sums.
-/

private theorem twice_rook2_eq_dotProduct (x : Mat46) :
    2 * rook2 x = totalSum x ^ 2 + dotProduct x (marginOperator 1 x) := by
  have hRow : totalSum x ^ 2 - (∑ a, rowSum x a ^ 2) = 2 *
      (rowSum x 0 * rowSum x 1 + rowSum x 0 * rowSum x 2 + rowSum x 0 * rowSum x 3 +
        rowSum x 1 * rowSum x 2 + rowSum x 1 * rowSum x 3 + rowSum x 2 * rowSum x 3) := by
    change (∑ a, rowSum x a) ^ 2 - _ = _
    simp only [Fin.sum_univ_four]
    ring
  have hColAt (j : Fin 6) : colSum x j ^ 2 = (∑ a : Fin 4, x (a, j) ^ 2) + 2 *
      (x (0, j) * x (1, j) + x (0, j) * x (2, j) + x (0, j) * x (3, j) +
        x (1, j) * x (2, j) + x (1, j) * x (3, j) + x (2, j) * x (3, j)) := by
    simp only [colSum, Fin.sum_univ_four]
    ring
  have hCol := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hColAt j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hCol
  have hEx : (∑ j : Fin 6, ∑ a : Fin 4, x (a, j) ^ 2) = dotProduct x x := by
    rw [Finset.sum_comm, dotProduct, Fintype.sum_prod_type]
    simp only [pow_two]
  rw [hEx] at hCol
  rw [rook2_as_row_pairs, dotProduct_marginOperator, one_mul]
  simp only [distinct2_eq, row, pair, ← pow_two]
  change _ = totalSum x ^ 2 + (dotProduct x x - (∑ a, rowSum x a ^ 2) - ∑ j, colSum x j ^ 2)
  simp only [rowSum] at hRow ⊢
  linear_combination -hRow + hCol

/-- Polarized quadratic form on the total-sum-zero hyperplane. -/
def rookQuadraticDual : Mat46 →ₗ[ℂ] Module.Dual ℂ Mat46 :=
  (dotProductEquiv ℂ (Fin 4 × Fin 6)).toLinearMap.comp (marginOperator 1)

private theorem rookQuadraticDual_injective : Function.Injective rookQuadraticDual :=
  (dotProductEquiv ℂ (Fin 4 × Fin 6)).injective.comp marginOperator_one_injective

private theorem rookQuadraticDual_zero_of_mem {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0) {x y : Mat46} (hx : x ∈ L) (hy : y ∈ L) :
    rookQuadraticDual x y = 0 := by
  have H (u) (hu : u ∈ L) : dotProduct u (marginOperator 1 u) = 0 := by
    have h := twice_rook2_eq_dotProduct u
    rw [(hL u hu).1, (hL u hu).2] at h
    simpa using h.symm
  have h := H (x + y) (L.add_mem hx hy)
  rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, H x hx, H y hy, zero_add, add_zero] at h
  rw [dotProduct_marginOperator_symm 1 y x] at h
  change dotProduct (marginOperator 1 x) y = 0
  rw [dotProduct_comm (marginOperator 1 x) y, dotProduct_marginOperator_symm 1 y x]
  linear_combination (1/2 : ℂ) * h

private theorem rookQuadraticDual_one {x : Mat46} (hx : totalSum x = 0) : rookQuadraticDual x 1 = 0 := by
  change dotProduct (marginOperator 1 x) 1 = 0
  unfold dotProduct
  simp only [Pi.one_apply, mul_one, Fintype.sum_prod_type]
  exact (totalSum_marginOperator 1 x).trans (by rw [hx, mul_zero])

private def withConstants (L : Submodule ℂ Mat46) : Submodule ℂ Mat46 := L ⊔ ℂ ∙ (1 : Mat46)

private theorem finrank_withConstants {L : Submodule ℂ Mat46} (hL : ∀ x ∈ L, totalSum x = 0) :
    Module.finrank ℂ (withConstants L) = Module.finrank ℂ L + 1 := by
  let U : Submodule ℂ Mat46 := ℂ ∙ (1 : Mat46)
  have hOne : (1 : Mat46) ≠ 0 := by
    intro h
    have := congrFun h ((0 : Fin 4), (0 : Fin 6))
    norm_num at this
  have hU : Module.finrank ℂ U = 1 := finrank_span_singleton hOne
  have hi : L ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hx, hu⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have h := hL _ hx
    have ha : a = 0 := by
      have he : totalSum (a • (1 : Mat46)) = 24 * a := by
        simp [totalSum, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
        ring
      rw [he] at h
      linear_combination (1 / 24 : ℂ) * h
    simp [ha]
  have h := Submodule.finrank_sup_add_finrank_inf_eq L U
  rw [hi, finrank_bot, add_zero, hU] at h
  exact h

private theorem rookQuadraticDual_mem_annihilator {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0) {x : Mat46} (hx : x ∈ L) :
    rookQuadraticDual x ∈ (withConstants L).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro y hy
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [map_add, map_smul, rookQuadraticDual_zero_of_mem hL hx hu, rookQuadraticDual_one (hL x hx).1,
    smul_zero, add_zero]

/-- The linear and quadratic equations alone bound all complex spaces by eleven. -/
theorem finrank_le_eleven_of_quadratic_level (L : Submodule ℂ Mat46)
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0) : Module.finrank ℂ L ≤ 11 := by
  let P := (withConstants L).dualAnnihilator
  let f := (rookQuadraticDual.domRestrict L).codRestrict P fun x => rookQuadraticDual_mem_annihilator hL x.2
  have hInj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (rookQuadraticDual_injective (congrArg Subtype.val h))
  have hle := LinearMap.finrank_le_finrank_of_injective hInj
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (withConstants L)
  rw [finrank_withConstants (fun x hx => (hL x hx).1)] at h
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h
  change Module.finrank ℂ L ≤ Module.finrank ℂ (withConstants L).dualAnnihilator at hle
  omega

private def entryScale (t : Mat46) : Mat46 →ₗ[ℂ] Mat46 :=
  LinearMap.pi fun ij => t ij • LinearMap.proj ij

/-- The bilinear form from the cubic at a doubly centred direction, expressed
via the row and column sum correction. -/
def centeredCubicDual (t : Mat46) : Mat46 →ₗ[ℂ] Module.Dual ℂ Mat46 :=
  (dotProductEquiv ℂ (Fin 4 × Fin 6)).toLinearMap.comp
    ((marginOperator 2).comp ((entryScale t).comp (marginOperator 2)))

theorem centeredCubicDual_apply (t x y : Mat46) :
    centeredCubicDual t x y = ∑ a : Fin 4, ∑ j : Fin 6,
      t (a, j) * marginCorrected x a j * marginCorrected y a j := by
  change dotProduct (marginOperator 2 (entryScale t (marginOperator 2 x))) y = _
  rw [dotProduct_comm, dotProduct_marginOperator_symm 2 y, dotProduct, Fintype.sum_prod_type]
  rfl

private theorem corrected_one (a : Fin 4) (j : Fin 6) : marginCorrected (1 : Mat46) a j = -8 := by
  norm_num [marginCorrected, rowSum, colSum, nsmul_eq_mul]

private theorem centeredCubicDual_one {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0)
    {t x : Mat46} (ht : t ∈ L) (hx : x ∈ L)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    centeredCubicDual t x 1 = 0 := by
  have hMargin (c : ℂ) : marginOperator c t = c • t := by
    funext ⟨a,j⟩
    change c * t (a, j) - (∑ l, t (a, l)) - (∑ b, t (b, j)) = c * t (a, j)
    simp [hr, hc]
  have hdot := rookQuadraticDual_zero_of_mem hL ht hx
  change dotProduct (marginOperator 1 t) x = 0 at hdot
  rw [hMargin, one_smul] at hdot
  have hform : centeredCubicDual t x 1 = (-8 : ℂ) * dotProduct t (marginOperator 2 x) := by
    rw [centeredCubicDual_apply, dotProduct, Fintype.sum_prod_type]
    simp only [corrected_one, ← Finset.sum_mul, mul_comm (-8 : ℂ)]
    rfl
  rw [hform, dotProduct_marginOperator_symm, hMargin, dotProduct_smul, dotProduct_comm x t,
    hdot, smul_zero, mul_zero]

private theorem centeredCubicDual_mem_annihilator {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0 ∧ rook3 x = 0)
    {t x : Mat46} (ht : t ∈ L) (hx : x ∈ L)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    centeredCubicDual t x ∈ (withConstants L).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro y hy
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hU : centeredCubicDual t x u = 0 := by
    rw [centeredCubicDual_apply]
    exact corrected_dot_eq_zero (fun z hz => ⟨(hL z hz).1, (hL z hz).2.2⟩) hx hu ht hr hc
  have hOne := centeredCubicDual_one (fun z hz => ⟨(hL z hz).1, (hL z hz).2.1⟩) ht hx hr hc
  rw [map_add, map_smul, hU, hOne, smul_zero, add_zero]

set_option maxHeartbeats 1000000 in
private theorem exists_subspace_of_matching_duals (L : Submodule ℂ Mat46)
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0)
    (F : Mat46 →ₗ[ℂ] Module.Dual ℂ Mat46)
    (hF : ∀ x ∈ L, F x ∈ (withConstants L).dualAnnihilator) :
    ∃ U : Submodule ℂ L, 3 * Module.finrank ℂ L ≤ 23 + Module.finrank ℂ U ∧
      ∀ x ∈ U, ∃ y ∈ L, F (x : Mat46) = rookQuadraticDual y := by
  let P := (withConstants L).dualAnnihilator
  let Q : L →ₗ[ℂ] P := (rookQuadraticDual.domRestrict L).codRestrict P fun x =>
    rookQuadraticDual_mem_annihilator hL x.2
  let C : L →ₗ[ℂ] P := (F.domRestrict L).codRestrict P fun x => hF x.1 x.2
  let R := Q.range.mkQ.comp C
  refine ⟨R.ker, ?_, ?_⟩
  · have hQinj : Function.Injective Q := by
      intro x y h
      exact Subtype.ext (rookQuadraticDual_injective (congrArg Subtype.val h))
    have hQ := Q.range.finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hQinj] at hQ
    have hP := Subspace.finrank_add_finrank_dualAnnihilator_eq (withConstants L)
    rw [finrank_withConstants (fun x hx => (hL x hx).1)] at hP
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at hP
    change Module.finrank ℂ L + 1 + Module.finrank ℂ P = 24 at hP
    have hR := LinearMap.finrank_range_add_finrank_ker R
    have hRange := Submodule.finrank_le R.range
    omega
  · intro x hx
    change R x = 0 at hx
    have hm : C x ∈ Q.range := by
      change Q.range.mkQ (C x) = 0 at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact hx
    obtain ⟨y, hy⟩ := hm
    exact ⟨y.1, y.2, (congrArg Subtype.val hy).symm⟩

/-- The cubic form at any doubly centred direction agrees with the quadratic
form on at least `3 * dim L - 23` dimensions of a level space. -/
theorem exists_subspace_of_matching_cubic_and_quadratic_duals (L : Submodule ℂ Mat46)
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0 ∧ rook3 x = 0)
    {t : Mat46} (ht : t ∈ L)
    (hr : ∀ a, ∑ j, t (a, j) = 0) (hc : ∀ j, ∑ a, t (a, j) = 0) :
    ∃ U : Submodule ℂ L, 3 * Module.finrank ℂ L ≤ 23 + Module.finrank ℂ U ∧
      ∀ x ∈ U, ∃ y ∈ L, centeredCubicDual t (x : Mat46) = rookQuadraticDual y :=
  exists_subspace_of_matching_duals L (fun z hz => ⟨(hL z hz).1, (hL z hz).2.1⟩)
    (centeredCubicDual t) (fun _ hx => centeredCubicDual_mem_annihilator hL ht hx hr hc)

private theorem zeroElse_mul (P : Prop) [Decidable P] (a b : ℂ) :
    (if P then 0 else a * b) = a * (if P then 0 else b) := by
  split_ifs <;> simp

private theorem mixedRook3_smul_first (c : ℂ) (x y z : Mat46) :
    mixedRook3 (c • x) y z = c * mixedRook3 x y z := by
  have he (a b d : Fin 4) : distinct3 (row (c • x) a) (row y b) (row z d) =
      c * distinct3 (row x a) (row y b) (row z d) := by
    simp only [distinct3, row, Pi.smul_apply, smul_eq_mul, mul_assoc, zeroElse_mul, ← Finset.mul_sum]
  simp only [mixedRook3, he, zeroElse_mul, ← Finset.mul_sum]

private theorem distinct2_comm (a b : Fin 6 → ℂ) : distinct2 a b = distinct2 b a := by
  simp only [distinct2_eq, pair, mul_comm]

/-- A constant direction in the cubic counts the eight ways to extend a
two-rook placement by one more rook, with the factor two from polarization. -/
theorem mixedRook3_ones_diagonal (x : Mat46) : mixedRook3 x x 1 = 16 * rook2 x := by
  have h (i : Fin 4) : row (1 : Mat46) i = 1 := rfl
  rw [rook2_as_row_pairs]
  simp (config := {decide := true}) only [mixedRook3, h, Fin.sum_univ_four, ite_true, ite_false,
    distinct3_last_one, distinct2_comm, zero_add, add_zero]
  ring

set_option maxHeartbeats 1000000 in
/-- The full cubic polarization as a map into the dual matrix space. -/
def rookCubicDual (t : Mat46) : Mat46 →ₗ[ℂ] Module.Dual ℂ Mat46 where
  toFun x :=
    { toFun := fun y => mixedRook3 y x t
      map_add' y z := mixedRook3_add_first y z x t
      map_smul' c y := mixedRook3_smul_first c y x t }
  map_add' x y := by
    refine LinearMap.ext fun z => ?_
    change mixedRook3 z (x + y) t = mixedRook3 z x t + mixedRook3 z y t
    exact mixedRook3_add_second z x y t
  map_smul' c x := by
    refine LinearMap.ext fun z => ?_
    change mixedRook3 z (c • x) t = c * mixedRook3 z x t
    rw [mixedRook3_swap_first z (c • x), mixedRook3_smul_first, mixedRook3_swap_first x z]

private theorem mixedRook3_ones_of_mem {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, rook2 x = 0) {x y : Mat46} (hx : x ∈ L) (hy : y ∈ L) :
    mixedRook3 x y 1 = 0 := by
  have H (z) (hz : z ∈ L) : mixedRook3 z z 1 = 0 := by
    rw [mixedRook3_ones_diagonal, hL z hz, mul_zero]
  have h := H (x+y) (L.add_mem hx hy)
  rw [mixedRook3_add_first, mixedRook3_add_second, mixedRook3_add_second,
    H x hx, H y hy, zero_add, add_zero, mixedRook3_swap_first y x] at h
  linear_combination (1/2 : ℂ) * h

private theorem rookCubicDual_mem_annihilator {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, rook2 x = 0 ∧ rook3 x = 0) {t x : Mat46} (ht : t ∈ L) (hx : x ∈ L) :
    rookCubicDual t x ∈ (withConstants L).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro y hy
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hU : rookCubicDual t x u = 0 := mixedRook3_eq_zero (fun z hz => (hL z hz).2) hu hx ht
  have hOne : rookCubicDual t x 1 = 0 := by
    change mixedRook3 1 x t = 0
    rw [mixedRook3_swap_first 1 x, mixedRook3_swap_last x 1]
    exact mixedRook3_ones_of_mem (fun z hz => (hL z hz).1) hx ht
  rw [map_add, map_smul, hU, hOne, smul_zero, add_zero]

/-- The matching-subspace bound holds at every direction, using the full
polarized cubic. -/
theorem exists_subspace_of_matching_rook_duals (L : Submodule ℂ Mat46)
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0 ∧ rook3 x = 0)
    {t : Mat46} (ht : t ∈ L) :
    ∃ U : Submodule ℂ L, 3 * Module.finrank ℂ L ≤ 23 + Module.finrank ℂ U ∧
      ∀ x ∈ U, ∃ y ∈ L, rookCubicDual t (x : Mat46) = rookQuadraticDual y :=
  exists_subspace_of_matching_duals L (fun z hz => ⟨(hL z hz).1, (hL z hz).2.1⟩)
    (rookCubicDual t) (fun _ hx => rookCubicDual_mem_annihilator (fun z hz => (hL z hz).2) ht hx)

private theorem distinct4_last_one (a b c : Fin 6 → ℂ) : distinct4 a b c 1 = 3 * distinct3 a b c := by
  unfold distinct4 distinct3
  have h (i j k : Fin 6) :
      (∑ l : Fin 6, if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l then 0
        else a i * b j * c k * (1 : Fin 6 → ℂ) l) =
        3 * (if i = j ∨ i = k ∨ j = k then 0 else a i * b j * c k) := by
    by_cases hij : i = j
    · simp [hij]
    by_cases hik : i = k
    · simp [hik]
    by_cases hjk : j = k
    · simp [hjk]
    simp only [hij, hik, hjk, false_or, or_false, ite_false, Pi.one_apply, mul_one]
    rw [sum_except_three (fun _ => a i * b j * c k) hij hik hjk]
    simp [nsmul_eq_mul]
    ring
  simp_rw [h, ← Finset.mul_sum]

private def mixedRook4 (w x y z : Mat46) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    if a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d then 0
    else distinct4 (row w a) (row x b) (row y c) (row z d)

private theorem mixedRook4_swap_first (w x y z : Mat46) : mixedRook4 w x y z = mixedRook4 x w y z := by
  unfold mixedRook4
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp [eq_comm, or_left_comm, distinct4_swap_first]

private theorem mixedRook4_swap_middle (w x y z : Mat46) : mixedRook4 w x y z = mixedRook4 w y x z := by
  unfold mixedRook4
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => ?_
  simp [eq_comm, or_comm, or_left_comm, distinct4_swap_middle]

private theorem mixedRook4_swap_last (w x y z : Mat46) : mixedRook4 w x y z = mixedRook4 w x z y := by
  unfold mixedRook4
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp [eq_comm, or_left_comm, distinct4_swap_last]

private theorem mixedRook4_add_first (v w x y z : Mat46) :
    mixedRook4 (v + w) x y z = mixedRook4 v x y z + mixedRook4 w x y z := by
  simp only [mixedRook4, distinct4, row, Pi.add_apply, add_mul, zeroElse_add, Finset.sum_add_distrib]

private theorem mixedRook4_add_second (v w x y z : Mat46) :
    mixedRook4 v (w + x) y z = mixedRook4 v w y z + mixedRook4 v x y z := by
  rw [mixedRook4_swap_first v, mixedRook4_add_first, mixedRook4_swap_first w, mixedRook4_swap_first x]

private theorem mixedRook4_smul_first (c : ℂ) (w x y z : Mat46) :
    mixedRook4 (c • w) x y z = c * mixedRook4 w x y z := by
  simp only [mixedRook4, distinct4, row, Pi.smul_apply, smul_eq_mul, mul_assoc,
    zeroElse_mul, ← Finset.mul_sum]

set_option maxHeartbeats 1000000 in
private theorem mixedRook4_diagonal_pair (x t : Mat46) :
    mixedRook4 x x t t = 4 * quarticQuadratic t x := by
  simp (config := {decide := true}) only [mixedRook4, quarticQuadratic, Fin.sum_univ_four,
    ite_true, ite_false, zero_add, add_zero, distinct4_swap_first, distinct4_swap_middle, distinct4_swap_last]
  ring

set_option maxHeartbeats 1000000 in
private theorem mixedRook4_ones (x y z : Mat46) : mixedRook4 x y z 1 = 3 * mixedRook3 x y z := by
  have h (i : Fin 4) : row (1 : Mat46) i = 1 := rfl
  simp (config := {decide := true}) only [mixedRook4, mixedRook3, h, Fin.sum_univ_four,
    ite_true, ite_false, zero_add, add_zero, distinct4_last_one]
  ring

set_option maxHeartbeats 1000000 in
/-- The quartic polarization with two copies of the selected direction. -/
def rookQuarticDual (t : Mat46) : Mat46 →ₗ[ℂ] Module.Dual ℂ Mat46 where
  toFun x :=
    { toFun := fun y => mixedRook4 y x t t
      map_add' y z := mixedRook4_add_first y z x t t
      map_smul' c y := mixedRook4_smul_first c y x t t }
  map_add' x y := by
    refine LinearMap.ext fun z => ?_
    change mixedRook4 z (x + y) t t = mixedRook4 z x t t + mixedRook4 z y t t
    exact mixedRook4_add_second z x y t t
  map_smul' c x := by
    refine LinearMap.ext fun z => ?_
    change mixedRook4 z (c • x) t t = c * mixedRook4 z x t t
    rw [mixedRook4_swap_first z (c • x), mixedRook4_smul_first, mixedRook4_swap_first x z]

private theorem rookQuarticDual_mem_annihilator {L : Submodule ℂ Mat46}
    (hL : ∀ x ∈ L, rook3 x = 0 ∧ rook4 x = 0) {t x : Mat46} (ht : t ∈ L) (hx : x ∈ L) :
    rookQuarticDual t x ∈ (withConstants L).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro y hy
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have H (z) (hz : z ∈ L) : mixedRook4 z z t t = 0 := by
    rw [mixedRook4_diagonal_pair, quarticQuadratic_eq_zero (fun z hz => (hL z hz).2) ht hz, mul_zero]
  have hU : rookQuarticDual t x u = 0 := by
    change mixedRook4 u x t t = 0
    have h := H (u + x) (L.add_mem hu hx)
    rw [mixedRook4_add_first, mixedRook4_add_second, mixedRook4_add_second,
      H u hu, H x hx, zero_add, add_zero, mixedRook4_swap_first x u] at h
    linear_combination (1/2 : ℂ) * h
  have hOne : rookQuarticDual t x 1 = 0 := by
    change mixedRook4 1 x t t = 0
    rw [mixedRook4_swap_first 1 x, mixedRook4_swap_middle x 1 t, mixedRook4_swap_last x t 1,
      mixedRook4_ones, mixedRook3_eq_zero (fun z hz => (hL z hz).1) hx ht ht, mul_zero]
  rw [map_add, map_smul, hU, hOne, smul_zero, add_zero]

/-- At every direction of a level space, each combination of the cubic and
quartic polarizations matches the quadratic form on at least `3 * dim L - 23`
dimensions. -/
theorem exists_subspace_of_matching_cubic_quartic_pencil (L : Submodule ℂ Mat46)
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0 ∧ rook3 x = 0 ∧ rook4 x = 0)
    {t : Mat46} (ht : t ∈ L) (a b : ℂ) :
    ∃ U : Submodule ℂ L, 3 * Module.finrank ℂ L ≤ 23 + Module.finrank ℂ U ∧
      ∀ x ∈ U, ∃ y ∈ L,
        (a • rookCubicDual t + b • rookQuarticDual t) (x : Mat46) = rookQuadraticDual y := by
  refine exists_subspace_of_matching_duals L (fun z hz => ⟨(hL z hz).1, (hL z hz).2.1⟩)
    (a • rookCubicDual t + b • rookQuarticDual t) ?_
  intro x hx
  have hC := rookCubicDual_mem_annihilator (fun z hz => ⟨(hL z hz).2.1, (hL z hz).2.2.1⟩) ht hx
  have hQ := rookQuarticDual_mem_annihilator (fun z hz => (hL z hz).2.2) ht hx
  exact (withConstants L).dualAnnihilator.add_mem
    ((withConstants L).dualAnnihilator.smul_mem a hC) ((withConstants L).dualAnnihilator.smul_mem b hQ)

/-- Null directions of the quadratic form restricted to a proposed extension space. -/
def quadraticRadical (E : Submodule ℂ Mat46) : Submodule ℂ E :=
  (E.subtype.dualMap.comp (rookQuadraticDual.domRestrict E)).ker

/-- A containing space controls the quadratic level dimension through its
dimension and the dimension of the restricted quadratic radical. -/
theorem twice_finrank_le_dim_add_radical {L E : Submodule ℂ Mat46} (hLE : L ≤ E)
    (hL : ∀ x ∈ L, totalSum x = 0 ∧ rook2 x = 0) :
    2 * Module.finrank ℂ L ≤ Module.finrank ℂ E + Module.finrank ℂ (quadraticRadical E) := by
  let B := E.subtype.dualMap.comp (rookQuadraticDual.domRestrict E)
  let j := Submodule.inclusion hLE
  let f := B.comp j
  have hle : f.range ≤ j.range.dualAnnihilator := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨y, rfl⟩
    exact rookQuadraticDual_zero_of_mem hL x.2 y.2
  let g : f.ker →ₗ[ℂ] quadraticRadical E :=
    (j.comp f.ker.subtype).codRestrict _ fun x => x.2
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Submodule.inclusion_injective hLE (congrArg Subtype.val h))
  have hKer := LinearMap.finrank_le_finrank_of_injective hg
  have hDim := LinearMap.finrank_range_add_finrank_ker f
  have hRange := Submodule.finrank_mono hle
  have hAnn := Subspace.finrank_add_finrank_dualAnnihilator_eq j.range
  rw [LinearMap.finrank_range_of_inj (Submodule.inclusion_injective hLE)] at hAnn
  omega

end GlobalQuadratic

section SingleRowSlice

/-!
Coordinates for the second slice in `search-gct-195-fourier.py --single-row-slice`.
The first six coordinates generate the centred first row and the lower direction
on columns zero and one. Coordinates six through eight put the opposite cube-root
mode on the last four columns. The last three coordinates carry the quadratic form
in the candidate extension space. The radical basis here uses unscaled cube roots.
-/

private def singleRowEntry {R : Type*} [CommRing R] (w : R) (z : Fin 12 → R) :
    Fin 4 × Fin 6 → R := fun p =>
  let w2 := -1 - w
  let r : Fin 6 → R := ![z 0, z 1, z 2, z 3, z 4, -(z 0 + z 1 + z 2 + z 3 + z 4)]
  let u : Fin 6 → R := ![z 5 + z 10, -z 5, 0, 0, 0, 0]
  let v : Fin 6 → R := ![z 11, z 11, z 6 + z 7 + z 8, -z 6, -z 7, -z 8]
  let a := z 9
  (![r p.2 + 3 * a, u p.2 + v p.2 - a, w * u p.2 + w2 * v p.2 - a,
    w2 * u p.2 + w * v p.2 - a] : Fin 4 → R) p.1

set_option maxHeartbeats 1000000 in
def singleRowExtensionMap (w : ℂ) : (Fin 12 → ℂ) →ₗ[ℂ] Mat4 (Fin 6) where
  toFun := singleRowEntry w
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [singleRowEntry] <;> ring
  map_smul' a x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [singleRowEntry] <;> ring

set_option maxHeartbeats 1000000 in
/-- The quadratic equation in the explicit twelve-dimensional extension coordinates. -/
theorem singleRowExtension_quadratic (w : ℂ) (hw : w^2+w+1=0) (z : Fin 12 → ℂ) :
    2 * rook2 (singleRowExtensionMap w z) = -360 * (z 9)^2 - 6 * z 10 * z 11 := by
  change 2 * rook2 (singleRowEntry w z) = _
  simp [rook2_as_row_pairs, distinct2_eq, pair, row, singleRowEntry, sumSix]
  linear_combination
    (4 * ((z 5)^2 + z 5 * z 10 + z 10 * z 11 - (z 11)^2 +
      (z 6)^2 + (z 7)^2 + (z 8)^2 + z 6 * z 7 + z 6 * z 8 + z 7 * z 8)) * hw

set_option maxHeartbeats 1000000 in
/-- The radical cubic factors in the three coordinates outside the original slice. -/
theorem singleRowExtension_radical_cubic (w : ℂ) (hw : w^2+w+1=0) (z : Fin 12 → ℂ)
    (h9 : z 9 = 0) (h10 : z 10 = 0) (h11 : z 11 = 0) :
    rook3 (singleRowExtensionMap w z) = 6 * (z 6 + z 7) * (z 6 + z 8) * (z 7 + z 8) := by
  change rook3 (singleRowEntry w z) = _
  have hRow (i : Fin 4) : ∑ j, singleRowEntry w z (i, j) = 0 := by
    fin_cases i <;> simp [singleRowEntry, sumSix, h9, h10, h11] <;> ring
  rw [rook3_of_centered _ hRow]
  simp [singleRowEntry, sumSix, h9, h10, h11]
  linear_combination
    (2 * ((z 0 + z 1 + z 3 + z 4) * (z 8)^2 - (z 0 + z 1) * (z 5)^2 -
      (z 2 + z 3) * (z 6)^2 - (z 2 + z 4) * (z 7)^2 -
      2 * z 2 * (z 6 * z 7 + z 6 * z 8 + z 7 * z 8)) -
      6 * (z 6 + z 7) * (z 6 + z 8) * (z 7 + z 8)) * hw

private def singleRowWitnessA {R : Type*} [CommRing R] : Fin 12 → R :=
  ![1,0,0,0,0,0,1,-1,1,0,0,0]

private def singleRowWitnessB {R : Type*} [CommRing R] : Fin 12 → R :=
  ![1,0,0,0,0,0,1,1,-1,0,0,0]

set_option maxHeartbeats 1000000 in
/-- This quartic value excludes the plane `z 6 + z 7 = 0` in the radical quotient. -/
theorem singleRowExtension_quartic_witnessA (w : ℂ) (hw : w^2+w+1=0) :
    rook4 (singleRowExtensionMap w singleRowWitnessA) = 6 := by
  change rook4 (singleRowEntry w singleRowWitnessA) = _
  have hRow (i : Fin 4) : ∑ j, singleRowEntry w singleRowWitnessA (i, j) = 0 := by
    fin_cases i <;> simp [singleRowEntry, singleRowWitnessA, sumSix]
    ring
  rw [rook4, distinct4_of_centered _ _ _ _ (hRow 0) (hRow 1) (hRow 2) (hRow 3)]
  simp [pair, singleRowEntry, singleRowWitnessA, sumSix]
  linear_combination -6 * hw

set_option maxHeartbeats 1000000 in
/-- The same witness belongs to the other two planes of the radical cubic. -/
theorem singleRowExtension_quartic_witnessB (w : ℂ) (hw : w^2+w+1=0) :
    rook4 (singleRowExtensionMap w singleRowWitnessB) = -6 := by
  change rook4 (singleRowEntry w singleRowWitnessB) = _
  have hRow (i : Fin 4) : ∑ j, singleRowEntry w singleRowWitnessB (i, j) = 0 := by
    fin_cases i <;> simp [singleRowEntry, singleRowWitnessB, sumSix]
    ring
  rw [rook4, distinct4_of_centered _ _ _ _ (hRow 0) (hRow 1) (hRow 2) (hRow 3)]
  simp [pair, singleRowEntry, singleRowWitnessB, sumSix]
  linear_combination 6 * hw

private def singleRowPad {R : Type*} [Zero R] (z : Fin 6 → R) : Fin 12 → R :=
  ![z 0, z 1, z 2, z 3, z 4, z 5, 0, 0, 0, 0, 0, 0]

private def singleRowPadLinear : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 12 → ℂ) where
  toFun := singleRowPad
  map_add' _ _ := by funext i; fin_cases i <;> simp [singleRowPad]
  map_smul' _ _ := by funext i; fin_cases i <;> simp [singleRowPad]

/-- The original six-dimensional single-row construction. -/
def singleRowSeed (w : ℂ) : Submodule ℂ (Mat4 (Fin 6)) :=
  ((singleRowExtensionMap w).comp singleRowPadLinear).range

private theorem singleRowExtensionMap_injective {w : ℂ} (hw : w^2+w+1=0) :
    Function.Injective (singleRowExtensionMap w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h (i : Fin 4) (j : Fin 6) : singleRowEntry w z (i,j) = 0 := congrFun hz (i,j)
  have ha : z 9 = 0 := by
    have hs : (∑ j, singleRowEntry w z (0,j)) = 0 := by simp [h]
    simp [singleRowEntry, sumSix] at hs
    linear_combination (1/18 : ℂ) * hs
  have h01 := h 1 0
  have h02 := h 2 0
  simp [singleRowEntry, ha] at h01 h02
  have hD : 1+2*w ≠ 0 := by
    intro he
    have hSquare : (1+2*w)^2 = -3 := by linear_combination 4 * hw
    rw [he] at hSquare
    norm_num at hSquare
  have hV : (1+2*w)*z 11 = 0 := by linear_combination w * h01 - h02
  have hv := (mul_eq_zero.mp hV).resolve_left hD
  have h5 := h 1 1
  have h6 := h 1 3
  have h7 := h 1 4
  have h8 := h 1 5
  simp [singleRowEntry, ha, hv] at h5 h6 h7 h8
  have h10 : z 10 = 0 := by simpa [h5, hv] using h01
  have h0 := h 0 0
  have h1 := h 0 1
  have h2 := h 0 2
  have h3 := h 0 3
  have h4 := h 0 4
  simp [singleRowEntry, ha] at h0 h1 h2 h3 h4
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, ha, h10, hv]

private def singleRowSamples : Fin 12 → Fin 4 × (Fin 6 → ℤ) :=
  ![(0, ![0, 0, 0, 0, 0, 0]),
    (1, ![0, 0, 0, 0, 0, 1]),
    (1, ![0, 0, 0, 0, 1, 0]),
    (1, ![0, 0, 0, 1, 0, 0]),
    (1, ![0, 0, 1, 0, 0, 0]),
    (1, ![0, 1, 0, 0, 0, 0]),
    (1, ![1, 0, 0, 0, 0, 0]),
    (2, ![0, 0, 0, 0, 0, 1]),
    (2, ![0, 1, 0, 0, 0, 1]),
    (3, ![0, 0, 0, 0, 1, 1]),
    (3, ![0, 0, 0, 1, 0, 1]),
    (3, ![0, 0, 1, 0, 0, 1])]

private def singleRowPivots : Fin 12 → Fin 4 × Fin 6 :=
  ![(0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 2), (2, 3), (2, 4), (2, 5)]

private def singleRowMinorModSeven : Matrix (Fin 12) (Fin 12) (ZMod 7) :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 1, 6, 0, 0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 6, 1, 0, 0, 0, 6, 1],
    ![0, 0, 0, 0, 6, 0, 1, 0, 0, 6, 0, 1],
    ![0, 0, 0, 6, 0, 0, 1, 0, 6, 0, 0, 1],
    ![0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 6, 0, 0, 0, 0, 1, 6, 0, 0, 0, 1],
    ![0, 0, 0, 5, 5, 5, 5, 0, 6, 6, 6, 6],
    ![0, 6, 1, 4, 4, 4, 4, 5, 4, 4, 4, 4],
    ![0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 1, 6],
    ![0, 0, 0, 0, 2, 0, 5, 0, 0, 1, 0, 6],
    ![0, 0, 0, 2, 0, 0, 5, 0, 1, 0, 0, 6]]

private def singleRowMinorInverse : Matrix (Fin 12) (Fin 12) (ZMod 7) :=
  ![![1, 4, 3, 3, 3, 1, 1, 0, 4, 0, 0, 0],
    ![0, 3, 2, 2, 2, 1, 5, 0, 4, 0, 0, 0],
    ![0, 4, 2, 2, 2, 6, 0, 0, 4, 0, 0, 0],
    ![0, 3, 5, 5, 6, 0, 0, 5, 3, 5, 5, 6],
    ![0, 3, 5, 6, 5, 0, 0, 5, 3, 5, 6, 5],
    ![0, 3, 6, 5, 5, 0, 0, 5, 3, 6, 5, 5],
    ![0, 3, 5, 5, 5, 0, 0, 5, 3, 5, 5, 5],
    ![0, 1, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0],
    ![0, 1, 4, 4, 2, 0, 0, 2, 1, 2, 2, 1],
    ![0, 1, 4, 2, 4, 0, 0, 2, 1, 2, 1, 2],
    ![0, 1, 2, 4, 4, 0, 0, 2, 1, 1, 2, 2],
    ![0, 1, 4, 4, 4, 0, 0, 2, 1, 2, 2, 2]]

private def singleRowSampleEntry {R : Type*} [CommRing R] (w : R) (i : Fin 12) :
    Fin 4 × Fin 6 → R := singleRowEntry w (singleRowPad fun j => (singleRowSamples i).2 j)

private def singleRowMinor {R : Type*} [CommRing R] (w : R) : Matrix (Fin 12) (Fin 12) R :=
  fun i j => rookFirstVariation (singleRowSamples i).1 (singleRowSampleEntry w i)
    (Pi.single (singleRowPivots j) 1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem singleRowMinor_row_check (i : Fin 12) :
    (List.finRange 12).all (fun j => decide
      (singleRowMinor (2 : ZMod 7) i j = singleRowMinorModSeven i j)) = true := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem singleRowMinor_mod_det : (singleRowMinor (2 : ZMod 7)).det ≠ 0 := by
  have hm : singleRowMinor (2 : ZMod 7) = singleRowMinorModSeven := by
    ext i j
    exact of_decide_eq_true (List.all_eq_true.mp (singleRowMinor_row_check i) j (by simp))
  have hi : singleRowMinorInverse * singleRowMinorModSeven = 1 := by
    ext i j
    exact of_checked_fin_grid (P := fun a b => (singleRowMinorInverse * singleRowMinorModSeven) a b =
      (1 : Matrix (Fin 12) (Fin 12) (ZMod 7)) a b) (fun _ _ => inferInstance) (by decide +kernel) i j
  have hd := congrArg Matrix.det hi
  rw [Matrix.det_mul, Matrix.det_one] at hd
  rw [hm]
  intro hz
  rw [hz, mul_zero] at hd
  exact (by decide : (0 : ZMod 7) ≠ 1) hd

private theorem map_singleRowEntry {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : R) (z : Fin 12 → R) :
    (fun ij => f (singleRowEntry w z ij)) = singleRowEntry (f w) (fun i => f (z i)) := by
  funext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [singleRowEntry, map_ofNat]

private theorem map_singleRowSampleEntry {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : R) (i : Fin 12) :
    (fun ij => f (singleRowSampleEntry w i ij)) = singleRowSampleEntry (f w) i := by
  unfold singleRowSampleEntry
  rw [map_singleRowEntry]
  congr 1
  funext j
  fin_cases j <;> simp [singleRowPad]

private theorem map_singleRowMinor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : R) : (singleRowMinor w).map f = singleRowMinor (f w) := by
  ext i j
  change f (rookFirstVariation (singleRowSamples i).1 (singleRowSampleEntry w i)
    (Pi.single (singleRowPivots j) 1)) = _
  rw [map_rookFirstVariation, map_singleRowSampleEntry]
  have hx : (fun ij => f ((Pi.single (singleRowPivots j) (1 : R) : Fin 4 × Fin 6 → R) ij)) =
      Pi.single (singleRowPivots j) (1 : S) := by
    funext ij
    by_cases h : ij = singleRowPivots j <;> simp [h]
  rw [hx]
  rfl

private theorem evaluateEisenstein_singleRow_det {R : Type*} [CommRing R] (u : R) (hu : u^2+u+1=0) :
    evaluateEisenstein u hu ((singleRowMinor (QuadraticAlgebra.omega : Eisenstein)).det) =
      (singleRowMinor u).det := by
  rw [RingHom.map_det]
  change ((singleRowMinor (QuadraticAlgebra.omega : Eisenstein)).map (evaluateEisenstein u hu)).det = _
  rw [map_singleRowMinor, evaluateEisenstein_omega]

private theorem singleRowMinor_det_ne_zero {w : ℂ} (hw : w^2+w+1=0) :
    (singleRowMinor w).det ≠ 0 := by
  intro hz
  have h0 : (singleRowMinor (QuadraticAlgebra.omega : Eisenstein)).det = 0 :=
    evaluateEisenstein_complex_injective hw
      ((evaluateEisenstein_singleRow_det w hw).trans (hz.trans (map_zero (evaluateEisenstein w hw)).symm))
  apply singleRowMinor_mod_det
  rw [← evaluateEisenstein_singleRow_det (2 : ZMod 7) (by decide), h0, map_zero]

private def singleRowVariations (w : ℂ) : Mat4 (Fin 6) →ₗ[ℂ] (Fin 12 → ℂ) :=
  LinearMap.pi fun i => rookFirstVariationLinear (singleRowSamples i).1 (singleRowSampleEntry w i)

private theorem singleRowVariations_apply (w : ℂ) (x : Mat4 (Fin 6)) (i : Fin 12) :
    singleRowVariations w x i = rookFirstVariation (singleRowSamples i).1 (singleRowSampleEntry w i) x :=
  rookFirstVariationLinear_apply _ _ _

private theorem singleRowVariations_kernel_dimension {w : ℂ} (hw : w^2+w+1=0) :
    Module.finrank ℂ (singleRowVariations w).ker = 12 := by
  have hm : Function.Surjective (singleRowMinor w).mulVec :=
    (Matrix.mulVecLin (singleRowMinor w)).injective_iff_surjective.mp
      (Matrix.mulVec_injective_of_det_ne_zero (singleRowMinor_det_ne_zero hw))
  have hs : Function.Surjective (singleRowVariations w) := by
    intro y
    obtain ⟨z, hz⟩ := hm y
    refine ⟨∑ j : Fin 12, z j • Pi.single (singleRowPivots j) (1 : ℂ), ?_⟩
    rw [← hz, map_sum]
    funext i
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, singleRowVariations_apply,
      Matrix.mulVec, dotProduct, singleRowMinor, mul_comm]
  have h := LinearMap.finrank_range_add_finrank_ker (singleRowVariations w)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem singleRow_exact_annihilation (i j : Fin 12) :
    rookFirstVariation (singleRowSamples i).1 (singleRowSampleEntry (QuadraticAlgebra.omega : Eisenstein) i)
      (singleRowEntry QuadraticAlgebra.omega (Pi.single j 1)) = 0 := by
  exact of_checked_fin_grid (P := fun a b => rookFirstVariation (singleRowSamples a).1
    (singleRowSampleEntry (QuadraticAlgebra.omega : Eisenstein) a)
    (singleRowEntry QuadraticAlgebra.omega (Pi.single b 1)) = 0)
    (fun _ _ => inferInstance) (by decide +kernel) i j

private theorem singleRowExtension_le_kernel {w : ℂ} (hw : w^2+w+1=0) :
    (singleRowExtensionMap w).range ≤ (singleRowVariations w).ker := by
  rintro _ ⟨z, rfl⟩
  rw [LinearMap.mem_ker]
  have hBasis (j : Fin 12) : singleRowVariations w (singleRowExtensionMap w (Pi.single j 1)) = 0 := by
    funext i
    rw [singleRowVariations_apply]
    let f := evaluateEisenstein w hw
    have h := congrArg f (singleRow_exact_annihilation i j)
    rw [map_rookFirstVariation, map_zero, map_singleRowSampleEntry, map_singleRowEntry,
      evaluateEisenstein_omega] at h
    have hm : (fun k => f ((Pi.single j (1 : Eisenstein) : Fin 12 → Eisenstein) k)) = Pi.single j (1 : ℂ) := by
      funext k
      by_cases hk : k = j <;> simp [hk, f]
    rw [hm] at h
    exact h
  let B := Pi.basisFun ℂ (Fin 12)
  have hz : (∑ j : Fin 12, z j • Pi.single j (1 : ℂ)) = z := by
    simpa only [B, Pi.basisFun_apply, Pi.basisFun_repr] using B.sum_repr z
  rw [← hz, map_sum, map_sum]
  simp only [map_smul, hBasis, smul_zero, Finset.sum_const_zero]

/-- Every level extension of the second seed is in the verified twelve-dimensional space. -/
theorem singleRowExtension_contains_level {L : Submodule ℂ (Mat4 (Fin 6))}
    (hL : ∀ x ∈ L, (∑ a, ∑ j, x (a,j)) = 0 ∧ rook2 x = 0 ∧ rook3 x = 0 ∧ rook4 x = 0)
    {w : ℂ} (hw : w^2+w+1=0) (hSeed : singleRowSeed w ≤ L) :
    L ≤ (singleRowExtensionMap w).range := by
  have hK : L ≤ (singleRowVariations w).ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext i
    rw [singleRowVariations_apply]
    have ht : singleRowSampleEntry w i ∈ L := hSeed ⟨fun j => (singleRowSamples i).2 j, rfl⟩
    exact rookFirstVariation_eq_zero hL _ ht hx
  have he := Submodule.eq_of_le_of_finrank_eq (singleRowExtension_le_kernel hw) (by
    rw [LinearMap.finrank_range_of_inj (singleRowExtensionMap_injective hw), Module.finrank_fin_fun,
      singleRowVariations_kernel_dimension hw])
  simpa only [he] using hK

private def singleRowQuadraticCoords : (Fin 12 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  LinearMap.funLeft ℂ ℂ (![9, 10, 11] : Fin 3 → Fin 12)

private theorem finrank_le_one_of_singleRow_quadratic (V : Submodule ℂ (Fin 3 → ℂ))
    (hV : ∀ z ∈ V, 60 * (z 0)^2 + z 1 * z 2 = 0) : Module.finrank ℂ V ≤ 1 := by
  let A : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi
    (![(120 : ℂ) • LinearMap.proj (0 : Fin 3), LinearMap.proj (2 : Fin 3), LinearMap.proj (1 : Fin 3)] :
      Fin 3 → (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
  have hA (x : Fin 3 → ℂ) : A x = ![120 * x 0, x 2, x 1] := by
    funext i
    fin_cases i <;> simp [A, smul_eq_mul]
  have hInj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [hA] at hx
    have h0 : 120 * x 0 = 0 := congrFun hx 0
    have h1 : x 1 = 0 := congrFun hx 2
    have h2 : x 2 = 0 := congrFun hx 1
    have h0' : x 0 = 0 := (mul_eq_zero.mp h0).resolve_left (by norm_num)
    funext i
    fin_cases i <;> simp [h0', h1, h2]
  have hSym (x y : Fin 3 → ℂ) : dotProduct x (A y) = dotProduct y (A x) := by
    simp [dotProduct, hA, Fin.sum_univ_three]
    ring
  have H (x) (hx : x ∈ V) : dotProduct x (A x) = 0 := by
    simp [dotProduct, hA, Fin.sum_univ_three]
    linear_combination 2 * hV x hx
  let f := (dotProductEquiv ℂ (Fin 3)).toLinearMap.comp (A.comp V.subtype)
  have hf : Function.Injective f :=
    (dotProductEquiv ℂ (Fin 3)).injective.comp (hInj.comp Subtype.val_injective)
  have hle : f.range ≤ V.dualAnnihilator := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    change dotProduct (A x.1) y = 0
    rw [dotProduct_comm]
    have h := H (x.1 + y) (V.add_mem x.2 hy)
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, H _ x.2, H _ hy,
      zero_add, add_zero, hSym x.1 y] at h
    linear_combination (1/2 : ℂ) * h
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hf] at h1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq V
  rw [Module.finrank_fin_fun] at h2
  omega

private theorem linear_factor_vanishes {V : Submodule ℂ (Fin 12 → ℂ)}
    (A B C : (Fin 12 → ℂ) →ₗ[ℂ] ℂ) (h : ∀ x ∈ V, A x * B x * C x = 0) :
    (∀ x ∈ V, A x = 0) ∨ (∀ x ∈ V, B x = 0) ∨ (∀ x ∈ V, C x = 0) := by
  by_contra! hn
  obtain ⟨⟨x, hx, hA⟩, ⟨y, hy, hB⟩, ⟨z, hz, hC⟩⟩ := hn
  let p (f : (Fin 12 → ℂ) →ₗ[ℂ] ℂ) : Polynomial ℂ :=
    Polynomial.C (f x) + Polynomial.C (f y) * Polynomial.X + Polynomial.C (f z) * Polynomial.X^2
  have ha : p A ≠ 0 := by
    intro he
    apply hA
    simpa [p, Polynomial.coeff_add, Polynomial.coeff_C_mul] using
      congrArg (fun q : Polynomial ℂ => q.coeff 0) he
  have hb : p B ≠ 0 := by
    intro he
    apply hB
    simpa [p, Polynomial.coeff_add, Polynomial.coeff_C_mul] using
      congrArg (fun q : Polynomial ℂ => q.coeff 1) he
  have hc : p C ≠ 0 := by
    intro he
    apply hC
    simpa [p, Polynomial.coeff_add, Polynomial.coeff_C_mul] using
      congrArg (fun q : Polynomial ℂ => q.coeff 2) he
  apply mul_ne_zero (mul_ne_zero ha hb) hc
  apply Polynomial.funext
  intro s
  have he (f : (Fin 12 → ℂ) →ₗ[ℂ] ℂ) : (p f).eval s = f (x + s • y + s^2 • z) := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, map_add, map_smul, smul_eq_mul]
    ring
  simp only [Polynomial.eval_mul, he, Polynomial.eval_zero]
  exact h _ (V.add_mem (V.add_mem hx (V.smul_mem s hy)) (V.smul_mem (s^2) hz))

private def singleRowCoordinate (i : Fin 12) : (Fin 12 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i

private def singleRowPlaneMap (i j : Fin 12) : (Fin 12 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearMap.pi (![singleRowCoordinate 9, singleRowCoordinate 10, singleRowCoordinate 11,
    singleRowCoordinate i + singleRowCoordinate j] : Fin 4 → (Fin 12 → ℂ) →ₗ[ℂ] ℂ)

private theorem singleRowPlane_dimension {i j : Fin 12} (hi : i < 9) (hj : j < 9) (hij : i ≠ j) :
    Module.finrank ℂ (singleRowPlaneMap i j).ker = 8 := by
  have hi9 := ne_of_lt hi
  have hj9 := ne_of_lt hj
  have hi10 : i ≠ 10 := ne_of_lt (lt_trans hi (by decide : (9 : Fin 12) < 10))
  have hj10 : j ≠ 10 := ne_of_lt (lt_trans hj (by decide : (9 : Fin 12) < 10))
  have hi11 : i ≠ 11 := ne_of_lt (lt_trans hi (by decide : (9 : Fin 12) < 11))
  have hj11 : j ≠ 11 := ne_of_lt (lt_trans hj (by decide : (9 : Fin 12) < 11))
  have hs : Function.Surjective (singleRowPlaneMap i j) := by
    intro u
    let z : Fin 12 → ℂ := fun k =>
      if k = 9 then u 0 else if k = 10 then u 1 else if k = 11 then u 2 else if k = i then u 3 else 0
    refine ⟨z, ?_⟩
    funext a
    fin_cases a
    · change z 9 = u 0
      simp [z]
    · change z 10 = u 1
      norm_num [z]
    · change z 11 = u 2
      norm_num [z]
    · change z i + z j = u 3
      simp [z, hi9, hi10, hi11, hj9, hj10, hj11, hij.symm]
  have h := LinearMap.finrank_range_add_finrank_ker (singleRowPlaneMap i j)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

set_option maxHeartbeats 1500000 in
/-- Any level space containing the single-row seed has dimension at most eight.
The cubic on the quadratic radical is a product of three linear forms, and
each of their planes contains an explicit nonzero quartic witness. -/
theorem finrank_le_eight_of_singleRow_level {L : Submodule ℂ (Mat4 (Fin 6))}
    (hL : ∀ x ∈ L, (∑ a, ∑ j, x (a,j)) = 0 ∧ rook2 x = 0 ∧ rook3 x = 0 ∧ rook4 x = 0)
    {w : ℂ} (hw : w^2+w+1=0) (hSeed : singleRowSeed w ≤ L) : Module.finrank ℂ L ≤ 8 := by
  by_contra! hBig
  let P := singleRowExtensionMap w
  let W := L.comap P
  have hRng : (P.domRestrict W).range = L := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · intro x hx
      obtain ⟨z, rfl⟩ := singleRowExtension_contains_level hL hw hSeed hx
      exact ⟨⟨z, hx⟩, rfl⟩
  have hInj : Function.Injective (P.domRestrict W) :=
    (singleRowExtensionMap_injective hw).comp Subtype.val_injective
  have hW := LinearMap.finrank_range_of_inj hInj
  rw [hRng] at hW
  let F := singleRowQuadraticCoords.domRestrict W
  have hF : Module.finrank ℂ F.range ≤ 1 := by
    apply finrank_le_one_of_singleRow_quadratic
    rintro _ ⟨x, rfl⟩
    have h := singleRowExtension_quadratic w hw x.1
    have hq : rook2 (P x.1) = 0 := (hL _ x.2).2.1
    rw [hq, mul_zero] at h
    change 60 * (x.1 9)^2 + x.1 10 * x.1 11 = 0
    linear_combination (1/6 : ℂ) * h
  have hDim := LinearMap.finrank_range_add_finrank_ker F
  let g := W.subtype.domRestrict F.ker
  let R := g.range
  have hR : 8 ≤ Module.finrank ℂ R := by
    change 8 ≤ Module.finrank ℂ g.range
    have hg : Function.Injective g := Subtype.val_injective.comp Subtype.val_injective
    rw [LinearMap.finrank_range_of_inj hg]
    omega
  have hRW : R ≤ W := by
    rintro _ ⟨x, rfl⟩
    exact x.1.2
  have hZero (z : Fin 12 → ℂ) (hz : z ∈ R) : z 9 = 0 ∧ z 10 = 0 ∧ z 11 = 0 := by
    obtain ⟨x, rfl⟩ := hz
    have h : F x.1 = 0 := x.2
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  have hProd (z : Fin 12 → ℂ) (hz : z ∈ R) :
      (singleRowCoordinate 6 + singleRowCoordinate 7) z *
        (singleRowCoordinate 6 + singleRowCoordinate 8) z *
        (singleRowCoordinate 7 + singleRowCoordinate 8) z = 0 := by
    obtain ⟨h9, h10, h11⟩ := hZero z hz
    have h := singleRowExtension_radical_cubic w hw z h9 h10 h11
    have h3 : rook3 (P z) = 0 := (hL _ (hRW hz)).2.2.1
    rw [h3] at h
    change (z 6 + z 7) * (z 6 + z 8) * (z 7 + z 8) = 0
    linear_combination (-1/6 : ℂ) * h
  have hPlane (i j : Fin 12) (hi : i < 9) (hj : j < 9) (hij : i ≠ j)
      (hijZero : ∀ z ∈ R, (singleRowCoordinate i + singleRowCoordinate j) z = 0)
      (z : Fin 12 → ℂ) (hz : singleRowPlaneMap i j z = 0) (hne : rook4 (P z) ≠ 0) : False := by
    have hle : R ≤ (singleRowPlaneMap i j).ker := by
      intro x hx
      rw [LinearMap.mem_ker]
      obtain ⟨h9, h10, h11⟩ := hZero x hx
      funext k
      fin_cases k
      · exact h9
      · exact h10
      · exact h11
      · exact hijZero x hx
    have hEq := Submodule.eq_of_le_of_finrank_le hle (by
      rw [singleRowPlane_dimension hi hj hij]
      exact hR)
    have hzR : z ∈ R := hEq.symm ▸ (show z ∈ (singleRowPlaneMap i j).ker from hz)
    exact hne (hL _ (hRW hzR)).2.2.2
  rcases linear_factor_vanishes _ _ _ hProd with h | h | h
  · exact hPlane 6 7 (by decide) (by decide) (by decide) h singleRowWitnessA
      (by funext i; fin_cases i <;> norm_num [singleRowPlaneMap, singleRowCoordinate, singleRowWitnessA])
      (by rw [singleRowExtension_quartic_witnessA w hw]; norm_num)
  · exact hPlane 6 8 (by decide) (by decide) (by decide) h singleRowWitnessB
      (by funext i; fin_cases i <;> norm_num [singleRowPlaneMap, singleRowCoordinate, singleRowWitnessB])
      (by rw [singleRowExtension_quartic_witnessB w hw]; norm_num)
  · exact hPlane 7 8 (by decide) (by decide) (by decide) h singleRowWitnessB
      (by funext i; fin_cases i <;> norm_num [singleRowPlaneMap, singleRowCoordinate, singleRowWitnessB])
      (by rw [singleRowExtension_quartic_witnessB w hw]; norm_num)

end SingleRowSlice

end Gct195.Centered
