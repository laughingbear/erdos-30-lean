/-
Copyright 2026 Laughing Bear.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import PrimeNumberTheoremAnd.Consequences
import Mathlib.Algebra.Order.Chebyshev

/-!
# Erdős Problems 30 and 241: Sidon sets have size `(1 + o(1)) √N`

Proofs of four statements from google-deepmind/formal-conjectures:

* `Erdos30.erdos_30.variants.erdos_turan`: `h(N) ≤ √N + C N^{1/4}` (here `C = 4`);
* `Erdos30.erdos_30.variants.singer`: `h(N) ≥ (1 - ε) √N` for all large `N`;
* `Erdos30.erdos_30.variants.isEquivalent_sqrt`: `h(N) ~ √N`;
* `Erdos241.erdos_241.variants.r_eq_2`: the Bose–Chowla conjecture for `r = 2`.

Here `h(N)` is the largest size of a Sidon set in `{1, …, N}`. The definitions `IsSidon`,
`Finset.maxSidonSubsetCard`, `Erdos30.h`, `Erdos241.f` and `Erdos241.BoseChowlaConjecture`, and
all four statements, are copied verbatim from formal-conjectures (`FormalConjecturesForMathlib/
Combinatorics/Basic.lean`, `FormalConjectures/ErdosProblems/30.lean` and `241.lean`).

**Upper bound (Erdős–Turán).** Let `A ⊆ [1, N]` be Sidon with `|A| = k`. For windows
`W_t = (t - m, t]`, `1 ≤ t ≤ N + m - 1`, let `x_t = |A ∩ W_t|`. Then `∑ x_t = k m`. Sending a
triple `(t, a, b)` with `a ≠ b` in `A ∩ W_t` to `(t - a, t - b)` is injective by the Sidon
property, so `∑ x_t (x_t - 1) ≤ m (m - 1)`. Cauchy–Schwarz gives
`(k m)² ≤ (N + m - 1) (k m + m (m - 1))`. With `r = N^{1/4}` and `m = ⌈r³⌉` this forces
`k ≤ r² + 4 r`.

**Lower bound (Bose / Singer).** For a prime `p`, let `θ` generate `GF(p²)ˣ` and take the
discrete logarithms of `θ + c`, `c ∈ GF(p)`, shifted by one. Equal pairwise sums give equal monic
quadratics at `θ`, whose minimal polynomial has degree `2`, so the pairs agree: a Sidon set of
size `p` in `[1, p² - 1]`. `prime_between` from PrimeNumberTheoremAnd supplies `p` just below
`√N`. The construction is proved for every prime degree `k`, as in Bose–Chowla.

**`r = 2`.** The condition defining `f N 2` is exactly the Sidon property, so `f N 2 = h N`.
-/

section Defs

open Function Set
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Finset

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The maximum size of a Sidon set in the supplied `Finset`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

end Finset

end Defs

namespace BoseChowla

set_option linter.unusedSectionVars false

open Polynomial

variable (p k : ℕ) [hp : Fact p.Prime] [hk : Fact k.Prime]

abbrev K := GaloisField p k

/-- A generator of the cyclic group `GF(p^k)ˣ`. -/
noncomputable def gen : (K p k)ˣ := Classical.choose (IsCyclic.exists_generator (α := (K p k)ˣ))

lemma gen_spec (x : (K p k)ˣ) : x ∈ Subgroup.zpowers (gen p k) :=
  Classical.choose_spec (IsCyclic.exists_generator (α := (K p k)ˣ)) x

/-- `n = p ^ k - 1`, the order of the generator. -/
abbrev n : ℕ := p ^ k - 1

lemma orderOf_gen : orderOf (gen p k) = n p k := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (gen_spec p k), Nat.card_units,
    GaloisField.card p k hk.out.ne_zero]

lemma two_le : 2 ≤ p := hp.out.two_le

/-- The generator as an element of the field. -/
noncomputable abbrev θ : K p k := (gen p k : K p k)

lemma theta_not_mem : θ p k ∉ (algebraMap (ZMod p) (K p k)).range := by
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact (gen p k).ne_zero hc.symm
  have h1 : (gen p k) ^ (p - 1) = 1 := by
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    show θ p k ^ (p - 1) = 1
    rw [← hc, ← map_pow, ZMod.pow_card_sub_one_eq_one hc0, map_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_gen p k] at h2
  unfold n at h2
  have h3 := Nat.le_of_dvd (by have := two_le p; omega) h2
  have := two_le p
  have h4 : p * p ≤ p ^ k := by
    rw [← sq]; exact Nat.pow_le_pow_right (by omega) hk.out.two_le
  have h5 : p * 1 < p * p := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

lemma natDegree_minpoly : (minpoly (ZMod p) (θ p k)).natDegree = k := by
  have hint : IsIntegral (ZMod p) (θ p k) := Algebra.IsIntegral.isIntegral _
  rw [← IntermediateField.adjoin.finrank hint]
  have hd : Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {θ p k}) ∣ k := by
    have := IntermediateField.finrank_dvd_of_le_right
      (le_top : IntermediateField.adjoin (ZMod p) {θ p k} ≤ ⊤)
    rwa [IntermediateField.finrank_top', GaloisField.finrank p hk.out.ne_zero] at this
  rcases (Nat.dvd_prime hk.out).1 hd with h | h
  · exfalso
    apply theta_not_mem p k
    rw [← minpoly.natDegree_eq_one_iff, ← IntermediateField.adjoin.finrank hint, h]
  · exact h

lemma theta_add_ne_zero (c : ZMod p) : θ p k + algebraMap (ZMod p) (K p k) c ≠ 0 := by
  intro h
  apply theta_not_mem p k
  exact ⟨-c, by rw [map_neg]; linear_combination -h⟩

lemma exists_log (c : ZMod p) :
    ∃ j, j < n p k ∧ (θ p k) ^ j = θ p k + algebraMap (ZMod p) (K p k) c := by
  classical
  set u : (K p k)ˣ := Units.mk0 _ (theta_add_ne_zero p k c)
  have hu : u ∈ Submonoid.powers (gen p k) := mem_powers_iff_mem_zpowers.2 (gen_spec p k u)
  rw [mem_powers_iff_mem_range_orderOf, orderOf_gen p k] at hu
  obtain ⟨j, hj, hju⟩ := Finset.mem_image.1 hu
  refine ⟨j, Finset.mem_range.1 hj, ?_⟩
  have := congrArg Units.val hju
  simpa [u] using this

/-- The discrete logarithm of `θ + c`. -/
noncomputable def L (c : ZMod p) : ℕ := Classical.choose (exists_log p k c)

lemma L_lt (c : ZMod p) : L p k c < n p k := (Classical.choose_spec (exists_log p k c)).1

lemma L_spec (c : ZMod p) : (θ p k) ^ (L p k c) = θ p k + algebraMap (ZMod p) (K p k) c :=
  (Classical.choose_spec (exists_log p k c)).2

lemma L_injective : Function.Injective (L p k) := by
  intro c d h
  have := L_spec p k c
  rw [h, L_spec p k d] at this
  exact (algebraMap (ZMod p) (K p k)).injective (add_left_cancel this).symm

lemma pow_sum_map_L (m : Multiset (ZMod p)) :
    (θ p k) ^ (m.map (L p k)).sum = (m.map (fun c => θ p k + algebraMap (ZMod p) (K p k) c)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [pow_add, ih, L_spec]

/-- The monic polynomial `∏ (X + c)`. -/
noncomputable def P (m : Multiset (ZMod p)) : (ZMod p)[X] :=
  ((m.map (fun c => -c)).map (fun a => X - C a)).prod

lemma aeval_P (m : Multiset (ZMod p)) :
    aeval (θ p k) (P p m) = (m.map (fun c => θ p k + algebraMap (ZMod p) (K p k) c)).prod := by
  simp [P, map_multiset_prod, Multiset.map_map, sub_eq_add_neg]

lemma eq_of_sum_modEq (m₁ m₂ : Multiset (ZMod p)) (h₁ : m₁.card = k) (h₂ : m₂.card = k)
    (h : (m₁.map (L p k)).sum ≡ (m₂.map (L p k)).sum [MOD n p k]) : m₁ = m₂ := by
  have hpow : (gen p k) ^ (m₁.map (L p k)).sum = (gen p k) ^ (m₂.map (L p k)).sum := by
    rw [pow_eq_pow_iff_modEq, orderOf_gen p k]; exact h
  have hK : aeval (θ p k) (P p m₁) = aeval (θ p k) (P p m₂) := by
    rw [aeval_P, aeval_P, ← pow_sum_map_L, ← pow_sum_map_L]
    have := congrArg Units.val hpow
    simpa using this
  have hmon : ∀ m : Multiset (ZMod p), (P p m).Monic := fun m =>
    monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hdeg : ∀ m : Multiset (ZMod p), (P p m).natDegree = m.card := by
    intro m; rw [P, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
  have hPP : P p m₁ = P p m₂ := by
    by_contra hne
    have hD : P p m₁ - P p m₂ ≠ 0 := sub_ne_zero.2 hne
    have hdvd : minpoly (ZMod p) (θ p k) ∣ P p m₁ - P p m₂ :=
      minpoly.dvd _ _ (by rw [map_sub, hK, sub_self])
    have hle := natDegree_le_of_dvd hdvd hD
    rw [natDegree_minpoly] at hle
    have hlt : (P p m₁ - P p m₂).degree < (P p m₁).degree := by
      apply degree_sub_lt_left
      · rw [degree_eq_natDegree (hmon _).ne_zero, degree_eq_natDegree (hmon _).ne_zero,
          hdeg, hdeg, h₁, h₂]
      · exact (hmon _).ne_zero
      · rw [(hmon _).leadingCoeff, (hmon _).leadingCoeff]
    rw [degree_eq_natDegree hD, degree_eq_natDegree (hmon _).ne_zero, hdeg, h₁] at hlt
    have : (P p m₁ - P p m₂).natDegree < k := by exact_mod_cast hlt
    omega
  have hroots := congrArg Polynomial.roots hPP
  simp only [P, roots_multiset_prod_X_sub_C] at hroots
  exact Multiset.map_injective neg_injective hroots

end BoseChowla

namespace ErdosTuran

/-- The Erdős–Turán window count: for a Sidon set `A ⊆ [1, N]` and windows of length `m`,
`(|A| m)² ≤ (N + m - 1) (|A| m + m (m - 1))`. -/
lemma window_count (A : Finset ℕ) (N m : ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) :
    (A.card * m) ^ 2 ≤ (N + m - 1) * (A.card * m + m * (m - 1)) := by
  classical
  set T := Finset.Icc 1 (N + m - 1) with hT
  set S : ℕ → Finset ℕ := fun t => A.filter (fun a => a ≤ t ∧ t < a + m) with hSdef
  have h1 : ∑ t ∈ T, (S t).card = A.card * m := by
    have hc : ∀ a ∈ A, (T.filter (fun t => a ≤ t ∧ t < a + m)).card = m := by
      intro a ha
      have := hA ha
      rw [Finset.mem_Icc] at this
      have e : T.filter (fun t => a ≤ t ∧ t < a + m) = Finset.Ico a (a + m) := by
        ext t
        simp only [hT, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [e, Nat.card_Ico]
      omega
    calc ∑ t ∈ T, (S t).card
        = ∑ t ∈ T, ∑ a ∈ A, if a ≤ t ∧ t < a + m then 1 else 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hSdef, Finset.card_filter]
      _ = ∑ a ∈ A, ∑ t ∈ T, if a ≤ t ∧ t < a + m then 1 else 0 := Finset.sum_comm
      _ = ∑ a ∈ A, m := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [← Finset.card_filter]
          exact hc a ha
      _ = A.card * m := by rw [Finset.sum_const, smul_eq_mul]
  have h2 : ∑ t ∈ T, (S t).offDiag.card ≤ m * (m - 1) := by
    rw [← Finset.card_sigma]
    have hmap := Finset.card_le_card_of_injOn (s := T.sigma fun t => (S t).offDiag)
      (t := (Finset.range m).offDiag) (fun x => (x.1 - x.2.1, x.1 - x.2.2)) ?_ ?_
    · rw [Finset.offDiag_card, Finset.card_range] at hmap
      have : m * m - m = m * (m - 1) := by rw [Nat.mul_sub_one]
      omega
    · rintro ⟨t, a, b⟩ hx
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_offDiag, hSdef,
        Finset.mem_filter, Finset.mem_range] at hx ⊢
      omega
    · rintro ⟨t, a, b⟩ hx ⟨t', a', b'⟩ hx' heq
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_offDiag, hSdef,
        Finset.mem_filter, Prod.mk.injEq] at hx hx' heq
      obtain ⟨-, ⟨ha, hat, hta⟩, ⟨hb, hbt, htb⟩, hab⟩ := hx
      obtain ⟨-, ⟨ha', hat', hta'⟩, ⟨hb', hbt', htb'⟩, hab'⟩ := hx'
      have hsum : a' + b = a + b' := by omega
      rcases hS a' ha' a ha b hb b' hb' hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : t = t' := by omega
        subst this; rfl
      · exact absurd rfl hab'
  have h3 : ∀ t, (S t).card ^ 2 = (S t).card + (S t).offDiag.card := by
    intro t
    rw [Finset.offDiag_card, sq]
    have := Nat.le_mul_self (S t).card
    omega
  have hsq : ∑ t ∈ T, (S t).card ^ 2 ≤ A.card * m + m * (m - 1) := by
    simp only [h3, Finset.sum_add_distrib, h1]
    omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := fun t => (S t).card)
  rw [h1, hT, Nat.card_Icc] at hcs
  calc (A.card * m) ^ 2 ≤ (N + m - 1 + 1 - 1) * ∑ t ∈ T, (S t).card ^ 2 := hcs
    _ ≤ (N + m - 1) * (A.card * m + m * (m - 1)) := by
      rw [Nat.add_sub_cancel]; exact Nat.mul_le_mul_left _ hsq

/-- Real form of the Erdős–Turán bound: a Sidon set in `[1, N]` has at most
`√N + 4 N^{1/4}` elements. -/
lemma card_le (A : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ (N : ℝ).sqrt + 4 * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  set r : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ) with hr
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr1 : 1 ≤ r := Real.one_le_rpow hN1 (by norm_num)
  have hr4 : r ^ 4 = N := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hsqrt : (N : ℝ).sqrt = r ^ 2 := by
    rw [← hr4, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set m : ℕ := ⌈r ^ 3⌉₊ with hm
  have hm1 : r ^ 3 ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < r ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ hr1
  have hmpos : (0 : ℝ) < m := by linarith
  have hm1' : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hw := window_count A N m hA hS
  set k : ℝ := (A.card : ℝ) with hk
  have hwR : (k * m) ^ 2 ≤ (N + m - 1) * (k * m + m * (m - 1)) := by
    have : ((A.card * m) ^ 2 : ℕ) ≤ ((N + m - 1) * (A.card * m + m * (m - 1)) : ℕ) := hw
    have e1 : ((N + m - 1 : ℕ) : ℝ) = N + m - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : ((m - 1 : ℕ) : ℝ) = m - 1 := by
      rw [Nat.cast_sub hm1']; push_cast; ring
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast [e1, e2] at this
    simpa [hk] using this
  have hk0 : 0 ≤ k := by positivity
  -- divide by m
  have hA' : k ^ 2 * m ≤ (N + m) * (k + m) := by
    have h' : (k * m) ^ 2 ≤ (N + m) * (k * m + m * m) := by
      have : (N + m - 1) * (k * m + m * (m - 1)) ≤ (N + m) * (k * m + m * m) := by
        have : 0 ≤ k * m + m * (m - 1) := by nlinarith
        nlinarith
      linarith
    have : m * (k ^ 2 * m) ≤ m * ((N + m) * (k + m)) := by nlinarith
    exact le_of_mul_le_mul_left this hmpos
  have hNm : (N : ℝ) ≤ r * m := by
    rw [← hr4]
    have : r ^ 4 = r * r ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hm1 (by linarith)
  have hB : k ^ 2 ≤ (r + 1) * (k + r ^ 3 + 1) := by
    have h1 : (N + m) * (k + m) ≤ m * ((r + 1) * (k + m)) := by
      have : (N : ℝ) + m ≤ m * (r + 1) := by nlinarith
      nlinarith
    have h2 : k ^ 2 * m ≤ m * ((r + 1) * (k + m)) := hA'.trans h1
    have h3 : k ^ 2 ≤ (r + 1) * (k + m) := by
      have : m * k ^ 2 ≤ m * ((r + 1) * (k + m)) := by linarith
      exact le_of_mul_le_mul_left this hmpos
    have : (r + 1) * (k + m) ≤ (r + 1) * (k + r ^ 3 + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  rw [hsqrt]
  by_contra hcon'
  have hcon := lt_of_not_ge hcon'
  have hpos1 : 0 < k - (r ^ 2 + 4 * r) := by linarith
  have hpos2 : 0 < k + (r ^ 2 + 4 * r) - (r + 1) := by nlinarith
  have key : k ^ 2 - (r + 1) * k = (k - (r ^ 2 + 4 * r)) * (k + (r ^ 2 + 4 * r) - (r + 1)) +
      ((r ^ 2 + 4 * r) ^ 2 - (r + 1) * (r ^ 2 + 4 * r)) := by ring
  have hprod := mul_pos hpos1 hpos2
  have hpoly : (r ^ 2 + 4 * r) ^ 2 - (r + 1) * (r ^ 2 + 4 * r) - (r + 1) * (r ^ 3 + 1) > 0 := by
    nlinarith [hr1, sq_nonneg r, mul_le_mul_of_nonneg_left hr1 (by linarith : (0 : ℝ) ≤ r)]
  nlinarith

end ErdosTuran

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)


open Filter
open scoped Asymptotics Pointwise

lemma h_le (N : ℕ) (hN : 1 ≤ N) :
    (h N : ℝ) ≤ (N : ℝ).sqrt + 4 * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  classical
  obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup
    ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [IsSidon]⟩⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  have : h N = B.card := by
    simp only [h, Finset.maxSidonSubsetCard]
    convert hBeq
  rw [this]
  exact ErdosTuran.card_le B N hN hB.1 hB.2

theorem erdos_30.variants.erdos_turan :
    ∃ C : ℝ, ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + C * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  exact ⟨4, eventually_ge_atTop 1 |>.mono fun N hN => h_le N hN⟩

lemma pair_eq {α : Type*} {a b c d : α} (h : ({a, b} : Multiset α) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Multiset α) := by rw [← h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right, Multiset.singleton_inj] at h
    exact h
  · right
    refine ⟨rfl, ?_⟩
    rw [Multiset.pair_comm c a] at h
    simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right, Multiset.singleton_inj] at h
    exact h

/-- Bose's construction: for a prime `p` with `p ^ 2 - 1 ≤ N`, `[1, N]` contains a Sidon set of
size `p`. -/
lemma le_h (p N : ℕ) [Fact p.Prime] (hN : p ^ 2 - 1 ≤ N) : p ≤ h N := by
  classical
  set A : Finset ℕ := (Finset.univ : Finset (ZMod p)).image
    (fun c => BoseChowla.L p 2 c + 1) with hA
  have hinj : Function.Injective (fun c : ZMod p => BoseChowla.L p 2 c + 1) := fun c d hcd =>
    BoseChowla.L_injective p 2 (Nat.add_right_cancel hcd)
  have hcard : A.card = p := by
    rw [hA, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hsub : A ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    have := BoseChowla.L_lt p 2 c
    unfold BoseChowla.n at this
    rw [Finset.mem_Icc]; omega
  have hS : IsSidon (A : Set ℕ) := by
    intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    simp only [Finset.mem_coe, hA, Finset.mem_image, Finset.mem_univ, true_and] at hi₁ hj₁ hi₂ hj₂
    obtain ⟨c₁, rfl⟩ := hi₁
    obtain ⟨d₁, rfl⟩ := hj₁
    obtain ⟨c₂, rfl⟩ := hi₂
    obtain ⟨d₂, rfl⟩ := hj₂
    have hm := BoseChowla.eq_of_sum_modEq p 2 {c₁, c₂} {d₁, d₂} (by simp) (by simp)
      (by simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
            Multiset.sum_cons, Multiset.sum_singleton]
          rw [show BoseChowla.L p 2 c₁ + BoseChowla.L p 2 c₂ =
            BoseChowla.L p 2 d₁ + BoseChowla.L p 2 d₂ by omega])
    rcases pair_eq hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
  rw [← hcard]
  simp only [h, Finset.maxSidonSubsetCard]
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hS⟩)

theorem erdos_30.variants.singer :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (1 - ε) * (N : ℝ).sqrt ≤ h N := by
  intro ε hε
  have hg : Tendsto (fun N : ℕ => (N : ℝ).sqrt / (1 + ε)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by linarith)
  filter_upwards [hg.eventually (prime_between hε)] with N hN
  obtain ⟨p, hp, hlo, hhi⟩ := hN
  have : Fact p.Prime := ⟨hp⟩
  set s : ℝ := (N : ℝ).sqrt with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hps : (p : ℝ) < s := by
    have : (1 + ε) * (s / (1 + ε)) = s := by field_simp
    linarith
  have hp2 : (p : ℝ) ^ 2 < N := (Real.lt_sqrt (Nat.cast_nonneg _)).1 hps
  have hp2' : p ^ 2 - 1 ≤ N := by
    have : p ^ 2 < N := by exact_mod_cast hp2
    omega
  have hle : (p : ℝ) ≤ h N := by exact_mod_cast le_h p N hp2'
  have h1 : (1 - ε) * s ≤ s / (1 + ε) := by
    rw [le_div_iff₀ hε1]
    nlinarith [sq_nonneg ε]
  linarith

theorem erdos_30.variants.isEquivalent_sqrt :
    (fun N => (h N : ℝ)) ~[atTop] fun N => (N : ℝ).sqrt := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hε : 0 < (1 - a) / 2 := by linarith
    filter_upwards [erdos_30.variants.singer _ hε, eventually_ge_atTop 1] with N hN hN1
    have hs : 0 < (N : ℝ).sqrt := Real.sqrt_pos.2 (by exact_mod_cast hN1)
    simp only [Pi.div_apply]
    rw [lt_div_iff₀ hs]
    nlinarith
  · have hr : Tendsto (fun N : ℕ => (N : ℝ) ^ (4⁻¹ : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hr.eventually_gt_atTop (4 / (a - 1)), eventually_ge_atTop 1] with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    set r : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ) with hrdef
    have hr1 : 1 ≤ r := Real.one_le_rpow hN1' (by norm_num)
    have hr4 : r ^ 4 = N := by
      rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hsqrt : (N : ℝ).sqrt = r ^ 2 := by
      rw [← hr4, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hle := h_le N hN1
    rw [← hrdef, hsqrt] at hle
    simp only [Pi.div_apply]
    rw [hsqrt, div_lt_iff₀ (by positivity)]
    have ha1 : 0 < a - 1 := by linarith
    have h4 : 4 < (a - 1) * r := by
      rw [div_lt_iff₀ ha1] at hN; linarith
    nlinarith

end Erdos30

namespace Erdos241

open Filter Finset
open scoped Asymptotics

/--
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums $a+b+c$ with
$a,b,c\in A$ are all distinct (aside from the trivial coincidences).

Formalization note: this is generalized to allow for different $r$.
-/
noncomputable def f (N r : ℕ) : ℕ :=
  open scoped Classical in
  letI candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

/--
The conjecture that the size of the set $A\subseteq \{1,\ldots,N\}$ is asymptotically $N^{1/r}$.
-/
def BoseChowlaConjecture (r : ℕ) : Prop :=
  (fun N ↦ (f N r : ℝ)) ~[atTop] (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / r))

/-- For `r = 2`, the defining condition of `f` is exactly the Sidon property. -/
lemma cond_two_iff (B : Finset ℕ) :
    (∀ m₁ m₂ : Multiset ℕ, m₁.card = 2 → m₂.card = 2 →
      (∀ x ∈ m₁, x ∈ B) → (∀ x ∈ m₂, x ∈ B) → m₁.sum = m₂.sum → m₁ = m₂) ↔
    IsSidon (B : Set ℕ) := by
  constructor
  · intro H i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    have := H {i₁, i₂} {j₁, j₂} (by simp) (by simp)
      (by intro x hx; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption)
      (by intro x hx; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption)
      (by simpa using hsum)
    exact Erdos30.pair_eq this
  · intro hS m₁ m₂ h₁ h₂ hm₁ hm₂ hsum
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h₁
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.1 h₂
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      forall_eq_or_imp, forall_eq] at hm₁ hm₂
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    rcases hS a hm₁.1 c hm₂.1 b hm₁.2 d hm₂.2 hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Multiset.pair_comm _ _

lemma f_two_eq (N : ℕ) : f N 2 = Erdos30.h N := by
  classical
  simp only [f, Erdos30.h, Finset.maxSidonSubsetCard]
  rw [Finset.filter_congr (fun B _ => cond_two_iff B)]

theorem erdos_241.variants.r_eq_2 :
    BoseChowlaConjecture 2 := by
  unfold BoseChowlaConjecture
  have e : (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) = fun N : ℕ ↦ (N : ℝ).sqrt := by
    funext N; rw [Real.sqrt_eq_rpow]; norm_num
  rw [e]
  simp only [f_two_eq]
  exact Erdos30.erdos_30.variants.isEquivalent_sqrt

end Erdos241
