import Mathlib
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Standalone proof of the full asymptotic claim in erdos319-solution.tex.
The final theorem Erdos319Formal.erdos_problem_319 proves FullAsymptotic
without mathematical hypotheses. erdos_problem_319_limit unfolds the ratio
limit, and erdos_problem_319_witnesses states the signed minimality witnesses
explicitly. All analytic inputs used by these theorems have proofs below.
The final declarations, rather than earlier conditional reductions, are the
unconditional conclusion of this file.

Checked environment: Lean 4.35.0-rc2; Mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

-- BEGIN PINNED ANALYTIC BACKGROUND

/-
Analytic background adapted from plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, src/v4.29.1/UnitFractions/ForMathlib.
These are existing proofs, ported here to Lean 4.35.0-rc2. They are not new
claims about Erdos 319. Their full proof terms are included and checked.
-/

section Erdos319BackgroundIntegralRPow


noncomputable section

open Filter MeasureTheory Set

/-!
This file is mostly a compatibility layer for the old Lean 3 `for_mathlib/integral_rpow` file.
All of the main half-line `rpow` lemmas are now available in Mathlib 4 under standard names.
-/

theorem integrable_on_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ r) (Ioi a) :=
  integrableOn_Ioi_rpow_of_lt hr ha

theorem integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    ∫ x in Ioi a, x ^ r = -a ^ (r + 1) / (r + 1) :=
  integral_Ioi_rpow_of_lt hr ha

theorem integral_Ioi_rpow_tendsto_aux {a r : ℝ} (hr : r < -1) (ha : 0 < a)
    {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
    Tendsto (fun i ↦ ∫ x in a..b i, x ^ r) l (nhds (-a ^ (r + 1) / (r + 1))) := by
  have hEq :
      (fun i ↦ ∫ x in a..b i, x ^ r) =ᶠ[l]
        fun i ↦ b i ^ (r + 1) / (r + 1) - a ^ (r + 1) / (r + 1) := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_rpow]
    · rw [sub_div]
    · exact Or.inr ⟨hr.ne, Set.notMem_uIcc_of_lt ha (ha.trans_le hi)⟩
  refine Tendsto.congr' hEq.symm ?_
  have hpow : Tendsto (fun i ↦ b i ^ (r + 1)) l (nhds 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -(r + 1))).comp hb
  simpa [neg_div] using hpow.div_const (r + 1) |>.sub_const (a ^ (r + 1) / (r + 1))

theorem integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ r)⁻¹) (Ioi a) := by
  refine (integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  change x ^ (-r) = (x ^ r)⁻¹
  rw [Real.rpow_neg (ha.trans hx).le]

theorem integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by
    rw [← Real.rpow_neg (ha.trans hx).le])]
  rw [integral_rpow_Ioi (neg_lt_neg hr) ha]
  rw [show -r + 1 = 1 - r by ring]
  rw [show 1 - r = -(r - 1) by ring, div_neg, neg_div, neg_neg]

theorem integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ n) (Ioi a) := by
  simpa using (integrable_on_rpow_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    ∫ x in Ioi a, x ^ n = -a ^ (n + 1) / (n + 1) := by
  exact_mod_cast (integral_rpow_Ioi (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Ioi a) := by
  simpa using (integrable_on_rpow_inv_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) := by
  exact_mod_cast (integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Ioi a) := by
  simpa only [← zpow_natCast] using
    (integrable_on_zpow_inv_Ioi (n := (n : ℤ)) (show 1 < (n : ℤ) by exact_mod_cast hn) ha)

theorem integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) := by
  have h :=
    integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha
  have hexp : 1 - (n : ℝ) = -((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
    ring
  have hden : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
    ring
  rw [hexp, hden, Real.rpow_neg ha.le, Real.rpow_natCast] at h
  simpa [Nat.cast_sub hn.le] using h

end

end Erdos319BackgroundIntegralRPow

section Erdos319BackgroundMisc


open scoped BigOperators

/-!
This file only reintroduces the pieces of `src/for_mathlib/misc.lean` that are not already
available in Mathlib4 under the same names.

In particular, Mathlib4 already provides results such as:
* `Rat.cast_sum`
* `Finset.filter_comm`
* `Finset.one_le_prod`
* `Real.finset_prod_rpow`
* `Real.self_le_rpow_of_one_le`
* `Real.self_le_rpow_of_le_one`
* the add-one interval lemmas in `Finset` and `Set`
-/

namespace Int

lemma Ico_succ_right {a b : ℤ} : Finset.Ico a (b + 1) = Finset.Icc a b := by
  simpa using (Finset.Ico_add_one_right_eq_Icc a b)

lemma Ioc_succ_right {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
  simpa [eq_comm] using (Finset.insert_Ioc_right_eq_Ioc_add_one (a := a) (b := b) h)

lemma insert_Ioc_succ_left {a b : ℤ} (h : a < b) :
    insert (a + 1) (Finset.Ioc (a + 1) b) = Finset.Ioc a b := by
  simpa using (Finset.insert_Ioc_add_one_left_eq_Ioc (a := a) (b := b) h)

lemma Ioc_succ_left {a b : ℤ} (h : a < b) :
    Finset.Ioc (a + 1) b = (Finset.Ioc a b).erase (a + 1) := by
  have hnot : a + 1 ∉ Finset.Ioc (a + 1) b := by simp
  rw [← insert_Ioc_succ_left h, Finset.erase_insert hnot]

lemma Ioc_succ_succ {a b : ℤ} (h : a ≤ b) :
    Finset.Ioc (a + 1) (b + 1) = (insert (b + 1) (Finset.Ioc a b)).erase (a + 1) := by
  have hab : a < b + 1 := h.trans_lt (lt_add_of_pos_right b zero_lt_one)
  rw [Ioc_succ_left hab, Ioc_succ_right h]

end Int

namespace Finset

lemma Icc_subset_range_add_one {x y : ℕ} :
    Icc x y ⊆ range (y + 1) := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  exact Finset.Icc_subset_Icc_left (b := y) (Nat.zero_le x)

lemma Ico_union_Icc_eq_Icc {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Ico x y ∪ Icc y z = Icc x z := by
  rw [← Finset.coe_inj, Finset.coe_union, Finset.coe_Ico, Finset.coe_Icc, Finset.coe_Icc,
    Set.Ico_union_Icc_eq_Icc h₁ h₂]

lemma Icc_sdiff_Icc_right {x y z : ℕ} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    Icc x z \ Icc y z = Ico x y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

lemma Icc_sdiff_Icc_left {x y z : ℕ} (h₁ : z ≤ y) (h₂ : x ≤ z) :
    Icc x y \ Icc x z = Ioc z y := by
  have h₁' := h₁
  have h₂' := h₂
  ext n
  simp [Finset.mem_sdiff]
  omega

lemma prod_rpow {ι : Type*} {s : Finset ι} {f : ι → ℝ} (c : ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    (∏ i ∈ s, f i) ^ c = ∏ i ∈ s, (f i ^ c) := by
  simpa [eq_comm] using (Real.finsetProd_rpow s f hf c)

end Finset

@[simp] theorem Ico_inter_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Finset.Ico a b ∩ Finset.Icc b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem Ico_disjoint_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Disjoint (Finset.Ico a b) (Finset.Icc b c) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem range_sdiff_Icc {x y : ℕ} (h : x ≤ y) :
    Finset.range (y + 1) \ Finset.Icc x y = Finset.Ico 0 x := by
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_sdiff_Icc_right (Nat.zero_le _) h]

theorem Ici_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ici a \ Set.Icc a b = Set.Ioi b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · intro hx
    exact lt_of_not_ge fun hxb => hx.2 ⟨hx.1, hxb⟩
  · intro hbx
    exact ⟨hab.trans hbx.le, fun hx => (not_lt_of_ge hx.2) hbx⟩

theorem Ioi_diff_Icc {a b : ℝ} (hab : a ≤ b) : Set.Ioi a \ Set.Ioc a b = Set.Ioi b := by
  rw [Set.Ioi_sdiff_Ioc, max_eq_right hab]

theorem one_le_prod {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i ∈ s, f i) := by
  simpa using (Finset.one_le_prod₀ (s := s) (f := f) h1)

namespace Real

lemma le_rpow_self_of_one_le {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
    x ≤ x ^ r :=
  self_le_rpow_of_one_le hx hr

lemma le_rpow_self_of {x r : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (h_one_le : r ≤ 1) :
    x ≤ x ^ r :=
  self_le_rpow_of_le_one hx₀ hx₁ h_one_le

end Real

@[to_additive]
theorem prod_powerset_compl {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Finset α) (f : Finset α → β) :
    (∏ x ∈ s.powerset, f (s \ x)) = ∏ x ∈ s.powerset, f x := by
  refine Finset.prod_bij' (fun x _ ↦ s \ x) (fun x _ ↦ s \ x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    rfl



end Erdos319BackgroundMisc

section Erdos319BackgroundBasicEstimates


noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open scoped Chebyshev Nat.Prime Topology

/-!
This file contains the Lean 4 statement port of the old Lean 3
`for_mathlib/basic_estimates` file.

When a result already exists upstream in Mathlib 4, this file prefers the
Mathlib version instead of reintroducing a duplicate local theorem.
-/

theorem tendsto_log_coe_at_top : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_log_coe_at_top : Tendsto (fun x : ℕ => log (log (x : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_coe_at_top

section Summatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ n ≤ x, a n`.
-/
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n

theorem summatory_nat (a : ℕ → M) (k n : ℕ) :
    summatory a k n = ∑ i ∈ Finset.Icc k n, a i := by
  simp [summatory]

theorem summatory_eq_floor (a : ℕ → M) {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, Nat.floor_natCast]

end Summatory

section PrimeSummatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ p ≤ x, a p`
where `p` ranges over primes.
-/
def prime_summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ (Finset.Icc k ⌊x⌋₊).filter Nat.Prime, a n

theorem prime_summatory_eq_summatory (a : ℕ → M) :
    prime_summatory a = summatory (fun n => if n.Prime then a n else 0) := by
  ext k x
  simp [prime_summatory, summatory, Finset.sum_filter]

end PrimeSummatory

def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, Int.fract t * (t ^ 2)⁻¹

namespace Nat

theorem cast_floor_eq_cast_int_floor {a : ℝ} (ha : 0 ≤ a) : (⌊a⌋₊ : ℝ) = ⌊a⌋ := by
  exact natCast_floor_eq_intCast_floor ha

end Nat

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy

theorem log_lt_self {x : ℝ} (hx : 0 < x) : log x < x :=
  by nlinarith [log_le_sub_one_of_pos hx]

theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log

abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

scoped[Chebyshev] notation "ϑ" => chebyshev_first

theorem chebyshev_first_pos {x : ℝ} (hx : 2 ≤ x) : 0 < chebyshev_first x :=
  Chebyshev.theta_pos hx

theorem prime_counting_eq_card_primes {x : ℕ} :
    π x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (x + 1)]
  congr 1
  ext p
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff, and_assoc]
  constructor
  · rintro ⟨hp1, hp2⟩
    exact ⟨hp2.one_le, hp1, hp2⟩
  · rintro ⟨hp1, hp2, hp3⟩
    exact ⟨hp2, hp3⟩

def partial_euler_product (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹

@[simp] theorem partial_euler_product_zero : partial_euler_product 0 = 1 := by
  simp [partial_euler_product]

theorem partial_euler_trivial_lower_bound {n : ℕ} : 1 ≤ partial_euler_product n := by
  refine Finset.one_le_prod₀ ?_
  intro p hp
  simp only [mem_filter] at hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  exact (one_le_inv₀ hpos).2 (by nlinarith [inv_nonneg.2 (show 0 ≤ (p : ℝ) by positivity)])

theorem trivial_divisor_bound {n : ℕ} : (ArithmeticFunction.sigma 0 n : ℝ) ≤ n := by
  exact_mod_cast (show ArithmeticFunction.sigma 0 n ≤ n by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Nat.card_divisors_le_self n)

theorem my_mul_thing : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
  | 0 => by norm_num
  | n + 1 => by
      simpa using (show (0 : ℝ) ≤ (n : ℝ) * (n + 1) by positivity)

section SummatoryExtra

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

lemma summatory_eq_of_Ico {n k : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a k x = summatory a k n := by
  rw [summatory_eq_floor (a := a) (k := k) x, Nat.floor_eq_on_Ico n x hx]

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx

lemma summatory_zero_eq_of_lt {x : ℝ} (hx : x < 1) :
  summatory a 0 x = a 0 := by
  rw [summatory_eq_floor (a := a) (k := 0) x, Nat.floor_eq_zero.mpr hx, summatory_nat]
  simp

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 := by
  have hk' : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hk
  exact summatory_eq_of_lt_one (a := a) hk hk'

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k := by
  simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 := by
  simp [summatory]

lemma summatory_succ (k n : ℕ) (hk : k ≤ n + 1) :
  summatory a k (n+1) = a (n + 1) + summatory a k n := by
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by exact_mod_cast rfl]
  rw [summatory_nat, summatory_nat]
  have hIcc : Finset.Icc k (n + 1) = insert (n + 1) (Finset.Icc k n) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert]
  · intro hmem
    exact Nat.not_succ_le_self n (Finset.mem_Icc.mp hmem).2

lemma summatory_succ_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) (k : ℕ) (n : ℕ)
  (hk : k ≤ n + 1) :
  a (n + 1) = summatory a k (n + 1) - summatory a k n := by
  rw [summatory_succ (a := a) k n hk, add_sub_cancel_right]

lemma summatory_eq_sub {M : Type*} [AddCommGroup M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a 1 n - summatory a 1 (n - 1) := by
  intro n hn
  cases n with
  | zero =>
      cases hn rfl
  | succ n =>
      simpa using summatory_succ_sub (a := a) 1 n (by omega)

lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))

lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

lemma summatory_nonneg' {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] {a : ℕ → M}
    (k : ℕ) (x : ℝ) (ha : ∀ (i : ℕ), k ≤ i → (i : ℝ) ≤ x → 0 ≤ a i)
    (hk : k ≠ 0) :
  0 ≤ summatory a k x := by
  rw [summatory]
  refine Finset.sum_nonneg ?_
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hi0 : i ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.pos_iff_ne_zero.mpr hk) hi.1)
  exact ha i hi.1 ((Nat.le_floor_iff' hi0).1 hi.2)

lemma summatory_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] (a : ℕ → M)
    (x : ℝ) (k : ℕ) (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a k x := by
  rw [summatory]
  exact Finset.sum_nonneg (fun i _ ↦ ha i)

lemma summatory_monotone_of_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (a : ℕ → M)
  (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  Monotone (summatory a k) := by
  intro i j hij
  rw [summatory, summatory]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hij)
  · intro n _ _; exact ha n

lemma abs_summatory_bound {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M) (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k z, ‖a i‖ := by
  exact (abs_summatory_le_sum a).trans <|
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_of_le hx))
      (by intro i _ _; exact norm_nonneg _)

@[fun_prop] lemma measurable_summatory {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
  {k : ℕ} {a : ℕ → M} :
  Measurable (summatory a k) := by
  change Measurable ((fun y ↦ ∑ i ∈ Finset.Icc k y, a i) ∘ Nat.floor)
  exact measurable_from_nat.comp Nat.measurable_floor

end SummatoryExtra

namespace ArithmeticFunction

lemma sigma_zero_eq_zeta_mul_zeta :
  ArithmeticFunction.sigma 0 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  ArithmeticFunction.sigma 0 i = ∑ _ ∈ i.divisors, 1 := by
  rw [ArithmeticFunction.sigma_apply, Finset.sum_congr rfl]
  intro _ _
  simp

end ArithmeticFunction

namespace Finset

lemma Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

lemma prod_eq_prod_iff_of_le' {ι : Type*}
  {s : Finset ι} {f g : ι → ℕ} (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ g i) :
  ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro hf h
    constructor
    · intro _ i hi
      exact False.elim (Finset.notMem_empty i hi)
    · intro _
      simp
  · intro a s ha ih hf h
    constructor
    · intro hprod
      rw [Finset.prod_insert ha, Finset.prod_insert ha] at hprod
      have hs_le : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        Finset.prod_le_prod (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hs_pos : 0 < ∏ i ∈ s, f i :=
        Finset.prod_pos (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hfa : f a = g a := by
        rcases lt_or_eq_of_le (h a (Finset.mem_insert_self a s)) with hlt | hEq
        · have hlt' : f a * ∏ i ∈ s, f i < g a * ∏ i ∈ s, g i := by
            exact (Nat.mul_lt_mul_of_pos_right hlt hs_pos).trans_le (Nat.mul_le_mul_left _ hs_le)
          exact (False.elim (Nat.lt_irrefl _ (hprod ▸ hlt')))
        · exact hEq
      have hs_eq : ∏ i ∈ s, f i = ∏ i ∈ s, g i := by
        exact Nat.eq_of_mul_eq_mul_left (hf a (Finset.mem_insert_self a s)) (hfa ▸ hprod)
      have hs_all : ∀ i ∈ s, f i = g i :=
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))).1 hs_eq
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hfa
      · exact hs_all i hi
    · intro hall
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [hall a (Finset.mem_insert_self a s)]
      refine congrArg (g a * ·) ?_
      apply (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))).2
      intro i hi
      exact hall i (Finset.mem_insert_of_mem hi)

end Finset

namespace Nat

@[simp] lemma floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp

lemma divisors_nonempty_iff {n : ℕ} : n.divisors.Nonempty ↔ n ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty, Nat.divisors_eq_empty]

end Nat

lemma tendsto_log_log_log_coe_at_top :
    Tendsto (fun x : ℕ ↦ log (log (log (x : ℝ)))) atTop atTop := by
  exact tendsto_log_atTop.comp tendsto_log_log_coe_at_top

lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) := by
  let b := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖
  have hsmul : IntegrableOn (b • f) (Icc x y) := Integrable.smul b hf'
  refine hsmul.integrable.mono ?_ ?_
  · exact measurable_summatory.aestronglyMeasurable.mul hf'.1
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_)
      (norm_nonneg _)
    · exact hz.2.trans (Nat.le_ceil y)
    · rw [Real.norm_eq_abs]
      exact le_abs_self b

theorem partial_summation_nat {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {k : ℕ} {N : ℕ} (hN : k ≤ N)
  (hf : ∀ i ∈ Icc (k : ℝ) N, HasDerivAt f (f' i) i) (hf' : IntegrableOn f' (Icc k N)) :
  ∑ n ∈ Finset.Icc k N, a n * f n =
    summatory a k N * f N - ∫ t in Icc (k : ℝ) N, summatory a k t * f' t := by
  let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
  have hc_sum :
      ∑ n ∈ Finset.Icc k N, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k N, f n * c n := by
    rw [show Finset.Icc k N = (Finset.Ioc k N).cons k Finset.left_notMem_Ioc by
      simpa using (Finset.Icc_eq_cons_Ioc hN)]
    rw [Finset.sum_cons]
    have htail :
        ∑ n ∈ Finset.Ioc k N, a n * f n =
          ∑ n ∈ Finset.Ioc k N, if k ≤ n then a n * f n else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
      simp [hk]
    simp [c, mul_comm, htail]
  have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) N)] deriv f := by
    change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) N)), f' t = deriv f t
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact (hf t ht).deriv.symm
  have hc_abel := sum_mul_eq_sub_sub_integral_mul' (c := c) (f := f) hN
    (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
  have hc_partial : ∀ n, (∑ i ∈ Finset.Icc 0 n, c i) = summatory a k n := by
    intro n
    calc
      ∑ i ∈ Finset.Icc 0 n, c i = ∑ i ∈ Finset.Icc k n, c i := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro i hi
          simp only [Finset.mem_Icc] at hi ⊢
          exact ⟨Nat.zero_le _, hi.2⟩
        · intro i hi0 hi
          have hi0' := Finset.mem_Icc.mp hi0
          have hki : ¬ k ≤ i := by
            intro hk
            exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
          simp [c, hki]
      _ = ∑ i ∈ Finset.Icc k n, a i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
        simp [c, hk]
      _ = summatory a k n := by rw [← summatory_nat]
  have hcongr :
      ∀ᵐ t ∂volume,
        t ∈ Set.Ioc (k : ℝ) N →
          deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, summatory_eq_floor (a := a) (k := k) t,
      mul_comm]
  have hIocIcc :
      (∫ t in Set.Ioc (k : ℝ) N, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
        ∫ t in Set.Icc (k : ℝ) N, summatory a k t * f' t := by
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
      setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [hc_sum, hc_abel, hc_partial, hc_partial, summatory_self, hIocIcc]
  simp [c, mul_comm]
  ring

theorem partial_summation {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  by_cases h : x < k
  · rw [Icc_eq_empty_of_lt h, Measure.restrict_empty, integral_zero_measure, sub_zero,
      summatory_eq_of_lt_one (a := fun n ↦ a n * f n) hk h,
      summatory_eq_of_lt_one (a := a) hk h, zero_mul]
  · have hle : (k : ℝ) ≤ x := le_of_not_gt h
    have hx : k ≤ ⌊x⌋₊ := by rwa [Nat.le_floor_iff' hk]
    let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
    have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) x)] deriv f := by
      change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) x)), f' t = deriv f t
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact (hf t ht).deriv.symm
    have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := f)
      (show 0 ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k) hle
      (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
    rw [Nat.floor_natCast] at habel
    have hc_partial : ∀ t : ℝ, (∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) = summatory a k t := by
      intro t
      calc
        ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = ∑ i ∈ Finset.Icc k ⌊t⌋₊, c i := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            exact ⟨Nat.zero_le _, hi.2⟩
          · intro i hi0 hi
            have hi0' := Finset.mem_Icc.mp hi0
            have hki : ¬ k ≤ i := by
              intro hk
              exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
            simp [c, hki]
        _ = ∑ i ∈ Finset.Icc k ⌊t⌋₊, a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
          simp [c, hk]
        _ = summatory a k t := by rw [summatory]
    have hsum :
        ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k ⌊x⌋₊, f n * c n := by
      rw [show Finset.Icc k ⌊x⌋₊ = (Finset.Ioc k ⌊x⌋₊).cons k Finset.left_notMem_Ioc by
        simpa using (Finset.Icc_eq_cons_Ioc hx)]
      rw [Finset.sum_cons]
      have htail :
          ∑ n ∈ Finset.Ioc k ⌊x⌋₊, a n * f n =
            ∑ n ∈ Finset.Ioc k ⌊x⌋₊, if k ≤ n then a n * f n else 0 := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
        simp [hk]
      simp [c, mul_comm, htail]
    have hcongr :
        ∀ᵐ t ∂volume,
          t ∈ Set.Ioc (k : ℝ) x →
            deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, mul_comm]
    have hIocIcc :
        (∫ t in Set.Ioc (k : ℝ) x, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
          ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
        setIntegral_congr_set Ioc_ae_eq_Icc]
    have hc_k : ∑ i ∈ Finset.Icc 0 k, c i = summatory a k k := by
      simpa using hc_partial (k : ℝ)
    rw [summatory, hsum, habel, hc_partial x, hc_k, summatory_self, hIocIcc]
    simp [c, mul_comm]
    ring

theorem partial_summation_cont {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk hf hf'.integrableOn_Icc

theorem partial_summation' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} (hk : k ≠ 0) (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Ici k)) {x : ℝ} :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono_set Icc_subset_Ici_self)

theorem partial_summation_cont' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Ici k)) (x : ℝ) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation_cont _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono Icc_subset_Ici_self)

lemma fract_mul_integrable {f : ℝ → ℝ} (s : Set ℝ)
  (hf' : IntegrableOn f s) :
  IntegrableOn (Int.fract * f) s := by
  refine Integrable.mono hf' ?_ (Filter.Eventually.of_forall ?_)
  · exact measurable_fract.aestronglyMeasurable.mul hf'.1
  · intro x
    simp only [norm_mul, Pi.mul_apply, norm_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le

private lemma harmonic_series_aux_identity {x : ℝ} (hx : 1 ≤ x) :
    summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
      (1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
        Int.fract x * x⁻¹ := by
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt (fun x ↦ x⁻¹) (-(i ^ 2)⁻¹) i := by
    intro i hi
    exact hasDerivAt_inv (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun i : ℝ ↦ (i ^ 2)⁻¹) (Ici 1) := by
    refine (ContinuousOn.inv₀ (f := fun i : ℝ ↦ i ^ 2) (s := Ici 1)
      (continuous_pow 2).continuousOn ?_)
    · intro i hi
      exact pow_ne_zero 2 (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont.neg) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_floor, sub_mul, Nat.cast_one]
  · have hEqOn :
        EqOn
          (fun a : ℝ ↦ Int.fract a * (a ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 a * -(a ^ 2)⁻¹)
          (fun y : ℝ ↦ y⁻¹) (Ioc 1 x) := by
      intro y hy
      dsimp
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      rw [hs, mul_neg, sub_neg_eq_add, ← add_mul, Int.fract_add_floor]
      have hycalc : y * (y⁻¹ * y⁻¹) = y⁻¹ := by
        field_simp [hy'.ne']
      simpa [sq, mul_inv, mul_assoc] using hycalc
    have hInt0 :
        ∫ t in Ioc 1 x,
            (Int.fract t * (t ^ 2)⁻¹ - summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹) = log x := by
      rw [setIntegral_congr_fun measurableSet_Ioc hEqOn, ← intervalIntegral.integral_of_le hx,
        integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    have hfloor : ((⌊x⌋ : ℝ)) = x - Int.fract x := by
      rw [Int.self_sub_fract]
    have hf :
        Integrable (fun t : ℝ ↦ Int.fract t * (t ^ 2)⁻¹) (volume.restrict (Ioc 1 x)) := by
      exact (fract_mul_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)).integrable
    have hgpos :
        Integrable (fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (volume.restrict (Ioc 1 x)) := by
      exact (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)
        |>.mono_set Ioc_subset_Icc_self).integrable
    have hxinv : x * x⁻¹ = (1 : ℝ) := by
      field_simp [(zero_lt_one.trans_le hx).ne']
    have hA : (x - Int.fract x) * x⁻¹ = 1 - Int.fract x * x⁻¹ := by
      rw [sub_mul, hxinv]
    rw [hfloor, hA] at *
    let I : ℝ := ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹
    let K : ℝ := ∫ t in Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹
    have hIK : I + K = log x := by
      calc
        I + K =
            ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ +
              summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹ := by
                symm
                simpa [I, K] using (integral_add hf hgpos)
        _ = log x := by
          simpa [sub_eq_add_neg, mul_neg, add_comm, add_left_comm, add_assoc] using hInt0
    have hJneg :
        ∫ t in Ioc 1 x, summatory (fun _ ↦ (1 : ℝ)) 1 t * -(t ^ 2)⁻¹ = -K := by
      simpa [K, mul_neg] using
        (integral_neg (f := fun t : ℝ ↦ summatory (fun _ ↦ (1 : ℝ)) 1 t * (t ^ 2)⁻¹)
          (μ := volume.restrict (Ioc 1 x)))
    have hK : K = log x - I := by
      linarith
    rw [hJneg, hK]
    simp [I, sq, hxinv]
    ring_nf

lemma euler_mascheroni_convergence_rate :
  Asymptotics.IsBigOWith 1 atTop
    (fun x : ℝ ↦ 1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨1, ?_⟩
  intro x hx
  have h : IntegrableOn (fun x : ℝ ↦ Int.fract x * (x ^ 2)⁻¹) (Ioi 1) := by
    refine fract_mul_integrable _ ?_
    exact integrable_on_pow_inv_Ioi one_lt_two zero_lt_one
  rw [one_mul, euler_mascheroni, norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx)),
    sub_sub_sub_cancel_left, ← setIntegral_sdiff measurableSet_Ioc h Ioc_subset_Ioi_self,
    Ioi_diff_Icc hx, norm_of_nonneg]
  · refine (setIntegral_mono_on (h.mono_set (Ioi_subset_Ioi hx))
      (integrable_on_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx))
      measurableSet_Ioi ?_).trans ?_
    · intro t ht
      exact mul_le_of_le_one_left (inv_nonneg.2 (sq_nonneg _)) (Int.fract_lt_one _).le
    · rw [integral_pow_inv_Ioi one_lt_two (zero_lt_one.trans_le hx)]
      norm_num
  · exact
      setIntegral_nonneg measurableSet_Ioi
        (fun t ht ↦ div_nonneg (Int.fract_nonneg _) (sq_nonneg _))

lemma euler_mascheroni_integral_Ioc_convergence :
  Tendsto (fun x : ℝ ↦ 1 - ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  simpa using
    (euler_mascheroni_convergence_rate.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

lemma euler_mascheroni_interval_integral_convergence :
  Tendsto (fun x : ℝ ↦ (1 : ℝ) - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹) atTop
    (𝓝 euler_mascheroni) := by
  refine euler_mascheroni_integral_Ioc_convergence.congr' ?_
  change ∀ᶠ x : ℝ in atTop,
    1 - ∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹ =
      1 - ∫ t in 1..x, Int.fract t * (t ^ 2)⁻¹
  rw [eventually_atTop]
  exact ⟨1, fun x hx ↦ by rw [intervalIntegral.integral_of_le hx]⟩

lemma harmonic_series_is_O_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni =
    (1 - (∫ t in Ioc 1 x, Int.fract t * (t ^ 2)⁻¹) - euler_mascheroni) -
      Int.fract x * x⁻¹ := by
  simpa using harmonic_series_aux_identity hx

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  Asymptotics.IsBigOWith 1 atTop (fun (x : ℝ) ↦ Int.fract x * f x) f := by
  apply Asymptotics.IsBigOWith.of_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [one_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one x).le

lemma harmonic_series_is_O_with :
  Asymptotics.IsBigOWith 2 atTop
    (fun x ↦ summatory (fun i ↦ (i : ℝ)⁻¹) 1 x - log x - euler_mascheroni)
    (fun x ↦ x⁻¹) := by
  have hfract :
      Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * x⁻¹) (fun x ↦ x⁻¹) :=
    is_O_with_one_fract_mul _
  refine (euler_mascheroni_convergence_rate.sub hfract).congr' ?_ ?_ Filter.EventuallyEq.rfl
  · norm_num
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (harmonic_series_is_O_aux hx).symm

theorem harmonic_series_real_limit :
    Tendsto (fun x ↦ (∑ i ∈ Finset.Icc 1 ⌊x⌋₊, (i : ℝ)⁻¹) - log x) atTop
      (𝓝 euler_mascheroni) := by
  simpa [summatory] using
    (harmonic_series_is_O_with.isBigO.trans_tendsto tendsto_inv_atTop_zero).add_const
      euler_mascheroni

theorem harmonic_series_limit :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, (i : ℝ)⁻¹) - log n) atTop
      (𝓝 euler_mascheroni) := by
  exact (harmonic_series_real_limit.comp tendsto_natCast_atTop_atTop).congr (fun x ↦ by simp)

lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ log i) 1 x - (x * log x - x) =
    1 + ((∫ t in 1..x, Int.fract t * t⁻¹) - Int.fract x * log x) := by
  rw [intervalIntegral.integral_of_le hx]
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt log (i⁻¹) i := by
    intro i hi
    exact Real.hasDerivAt_log (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ici 1) := by
    refine ContinuousOn.inv₀ (f := fun x : ℝ ↦ x) (s := Ici 1) continuousOn_id ?_
    intro x hx
    exact (zero_lt_one.trans_le hx).ne'
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  clear ps
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_fract, sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left,
    sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← add_assoc, sub_add_cancel, Nat.cast_one,
    ← integral_add]
  · have hEqOn :
        EqOn (fun _ : ℝ ↦ (1 : ℝ))
          (fun y : ℝ ↦ Int.fract y * y⁻¹ + summatory (fun _ ↦ (1 : ℝ)) 1 y * y⁻¹) (Ioc 1 x) := by
      intro y hy
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      dsimp
      rw [hs]
      have hyinv : y * y⁻¹ = (1 : ℝ) := by
        field_simp [hy'.ne']
      calc
        (1 : ℝ) = y * y⁻¹ := by simpa using hyinv.symm
        _ = (Int.fract y + (⌊y⌋ : ℝ)) * y⁻¹ := by
          rw [Int.fract_add_floor]
        _ = Int.fract y * y⁻¹ + (⌊y⌋ : ℝ) * y⁻¹ := by ring
    rw [← integral_one, intervalIntegral.integral_of_le hx,
      setIntegral_congr_fun measurableSet_Ioc hEqOn]
  · refine fract_mul_integrable _ ?_
    exact (cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact
      (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Ioc_subset_Icc_self

lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : Filter ℝ) (h : Tendsto f l atTop)
    (c : ℝ) :
  Asymptotics.IsLittleO l (fun _ : ℝ ↦ c) f := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hbound : ∀ᶠ x : ℝ in atTop, ‖c‖ ≤ ε * ‖x‖ := by
    filter_upwards [eventually_ge_atTop (‖c‖ * ε⁻¹), eventually_ge_atTop (0 : ℝ)] with x hx₁ hx₂
    rw [norm_of_nonneg hx₂]
    calc
      ‖c‖ = ε * (‖c‖ * ε⁻¹) := by
        field_simp [hε.ne']
      _ ≤ ε * x := mul_le_mul_of_nonneg_left hx₁ hε.le
  exact h.eventually hbound

lemma is_o_one_log (c : ℝ) : Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ c) log := by
  exact is_o_const_of_tendsto_at_top _ _ Real.tendsto_log_atTop _

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  Asymptotics.IsBigOWith c atTop
    (fun x ↦ summatory (fun i ↦ log i) 1 x - (x * log x - x))
    (fun x ↦ log x) := by
  have f₁ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * log x) log :=
    is_O_with_one_fract_mul _
  have f₂ : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 : ℝ)) log := is_o_one_log _
  have f₃ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ ∫ t in 1..x, Int.fract t * t⁻¹) log := by
    simp only [Asymptotics.isBigOWith_iff, eventually_atTop, one_mul]
    refine ⟨1, ?_⟩
    intro x hx
    rw [norm_of_nonneg (Real.log_nonneg hx), norm_of_nonneg, ← div_one x,
      ← integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    · have h₁ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 x := by
        simpa [one_div] using
          (intervalIntegral.intervalIntegrable_one_div (μ := volume)
            (fun y hy => by
              rw [uIcc_of_le hx] at hy
              exact (zero_lt_one.trans_le hy.1).ne')
            continuousOn_id)
      have hInvOn : IntegrableOn (fun u : ℝ ↦ u⁻¹) (Icc 1 x) := by
        rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact h₁
      have hfract :
          IntervalIntegrable (fun y : ℝ ↦ Int.fract y * y⁻¹) volume 1 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        simpa only [Pi.mul_def] using fract_mul_integrable (s := Icc 1 x) hInvOn
      have h₂ : ∀ y ∈ Icc 1 x, Int.fract y * y⁻¹ ≤ y⁻¹ := by
        intro y hy
        refine mul_le_of_le_one_left (inv_nonneg.2 (zero_le_one.trans hy.1)) (Int.fract_lt_one _).le
      exact intervalIntegral.integral_mono_on (μ := volume) hx hfract h₁ h₂
    · refine intervalIntegral.integral_nonneg hx ?_
      intro y hy
      exact mul_nonneg (Int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1))
  refine (f₂.add_isBigOWith (f₃.sub f₁) ?_).congr' rfl ?_ Filter.EventuallyEq.rfl
  · norm_num [hc]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simpa using (summatory_log_aux hx).symm

lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (fun n ↦ f n * ⌊x / n⌋) 1 y =
    summatory (fun n ↦ ∑ i ∈ n.divisors, f i) 1 x := by
  simp_rw [summatory, ← Nat.cast_floor_eq_cast_int_floor (div_nonneg hy (Nat.cast_nonneg _)),
    ← summatory_const_one, summatory, Finset.mul_sum, mul_one]
  calc
    ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc 1 ⌊x / i⌋₊, f i
      = ∑ i ∈ Finset.Icc 1 ⌊y⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x / i⌋₊).image (fun j => i * j), f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            refine Finset.sum_image ?_
            intro a ha b hb hab
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            exact Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp hi1) hab
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ i ∈ n.divisors, f i := by
          refine Finset.sum_comm'
            (t := fun i : ℕ => (Finset.Icc 1 ⌊x / i⌋₊).image fun j : ℕ => i * j)
            (t' := (Finset.Icc 1 ⌊x⌋₊ : Finset ℕ)) (s' := fun n : ℕ => n.divisors)
            (f := fun i (_n : ℕ) => f i) ?_
          intro i n
          constructor
          · rintro ⟨hi, hn⟩
            rw [Finset.mem_image] at hn
            rcases hn with ⟨j, hj, rfl⟩
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).1
                  ((Finset.mem_Icc.mp hj).2)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := by
              have hmul : (i : ℝ) * j ≤ (i : ℝ) * (x / i) :=
                mul_le_mul_of_nonneg_left hjx (show 0 ≤ (i : ℝ) by positivity)
              have hdiv : (i : ℝ) * (x / i) = x := by
                field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hi1))]
              simpa [Nat.cast_mul, hdiv] using hmul
            have hi_ne : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
            have hj_ne : j ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hj1)
            have hij_ne : i * j ≠ 0 := Nat.mul_ne_zero hi_ne hj_ne
            refine ⟨?_, ?_⟩
            · rw [Nat.mem_divisors]
              exact ⟨dvd_mul_right i j, hij_ne⟩
            · rw [Finset.mem_Icc]
              exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hij_ne),
                (Nat.le_floor_iff hy).2 hxij⟩
          · rintro ⟨hin, hn⟩
            rw [Nat.mem_divisors] at hin
            rcases hin with ⟨⟨j, rfl⟩, hij_ne⟩
            have hi_ne : i ≠ 0 := by
              intro hi0
              exact hij_ne (by simp [hi0])
            have hj_ne : j ≠ 0 := by
              intro hj0
              exact hij_ne (by simp [hj0])
            have hi1 : 1 ≤ i := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hi_ne)
            have hj1 : 1 ≤ j := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hj_ne)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hy).1 (Finset.mem_Icc.mp hn).2
            have hix : (i : ℝ) ≤ x := by
              exact
                le_trans
                  (by
                    exact_mod_cast Nat.le_mul_of_pos_right i
                      (Nat.pos_iff_ne_zero.mpr hj_ne))
                  hxij
            have hiy : (i : ℝ) ≤ y := le_trans hix xy
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (le_div_iff₀ (Nat.cast_pos.2 hi1)).2
                  (by simpa [Nat.cast_mul, mul_comm] using hxij)
            refine ⟨Finset.mem_Icc.mpr ⟨hi1, (Nat.le_floor_iff (hy.trans xy)).2 hiy⟩, ?_⟩
            rw [Finset.mem_image]
            exact ⟨j, Finset.mem_Icc.mpr ⟨hj1,
              (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).2 hjx⟩, rfl⟩

lemma exp_sub_mul {x c : ℝ} {hc : 0 ≤ c} : c - c * log c ≤ exp x - c * x := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp [(Real.exp_pos _).le]
  suffices hmain : Real.exp (Real.log c) - c * Real.log c ≤ Real.exp x - c * x by
    rwa [Real.exp_log hc] at hmain
  have h₁ : Differentiable ℝ (fun x ↦ Real.exp x - c * x) :=
    Real.differentiable_exp.sub (differentiable_id.const_mul _)
  have h₂ : ∀ t, deriv (fun y ↦ Real.exp y - c * y) t = Real.exp t - c := by
    intro t
    simpa [Pi.sub_def] using ((Real.hasDerivAt_exp t).sub ((hasDerivAt_id t).const_mul c)).deriv
  cases le_total (Real.log c) x with
  | inl hx =>
      have hmono : MonotoneOn (fun y ↦ Real.exp y - c * y) (Icc (Real.log c) x) :=
        monotoneOn_of_deriv_nonneg (convex_Icc (Real.log c) x) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonneg, ← Real.log_le_iff_le_exp hc]
            exact hy.1.le
      exact hmono (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
  | inr hx =>
      have hanti : AntitoneOn (fun y ↦ Real.exp y - c * y) (Icc x (Real.log c)) :=
        antitoneOn_of_deriv_nonpos (convex_Icc x (Real.log c)) h₁.continuous.continuousOn
          h₁.differentiableOn fun y hy => by
            rw [interior_Icc] at hy
            rw [h₂, sub_nonpos, ← Real.le_log_iff_exp_le hc]
            exact hy.2.le
      exact hanti (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx

lemma div_bound_aux1 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ^ K ≤ n) (h2 : 0 < K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) := by
  transitivity (2 : ℝ) ^ (r : ℝ)
  · have hpow : (1 + (1 : ℝ)) ^ r = (2 : ℝ) ^ (r : ℝ) := by
      norm_num
    rw [← hpow, add_comm]
    simpa using (one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num : -2 ≤ (1 : ℝ)) r)
  · have hnonneg : 0 ≤ (2 : ℝ) ^ K := by
      positivity
    refine le_trans ?_ (Real.rpow_le_rpow hnonneg h1 ?_)
    · rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_div_cancel₀ _ h2.ne']
    · exact div_nonneg (Nat.cast_nonneg _) h2.le

lemma bernoulli_aux (x : ℝ) : x + 1 / 2 ≤ 2 ^ x := by
  have h : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have h₁ :
      1 / Real.log 2 - 1 / Real.log 2 * Real.log (1 / Real.log 2) ≤
        Real.exp (Real.log 2 * x) - 1 / Real.log 2 * (Real.log 2 * x) := by
    apply exp_sub_mul
    simp only [one_div, inv_nonneg]
    exact h.le
  rw [Real.rpow_def_of_pos zero_lt_two, ← le_sub_iff_add_le']
  rw [← mul_assoc, div_mul_cancel₀ _ h.ne', one_mul] at h₁
  apply le_trans ?_ h₁
  rw [one_div (Real.log 2), Real.log_inv]
  simp only [one_div, mul_neg, sub_neg_eq_add]
  suffices h2 : Real.log 2 / 2 - 1 ≤ Real.log (Real.log 2) by
    field_simp [h]
    linarith
  transitivity (-1 / 2 : ℝ)
  · linarith [Real.log_two_lt_d9]
  · have hlog : (-1 : ℝ) ≤ 2 * Real.log (Real.log 2) := by
      simpa [Real.log_rpow h] using
        (Real.le_log_iff_exp_le (Real.rpow_pos_of_pos h _)).2 (by
          apply Real.exp_neg_one_lt_d9.le.trans
          apply le_trans _ (Real.rpow_le_rpow (by positivity) Real.log_two_gt_d9.le zero_le_two)
          · rw [Real.rpow_two]
            norm_num)
    nlinarith

lemma div_bound_aux2 (n : ℝ) (r : ℕ) (K : ℝ) (h1 : 2 ≤ n) (h2 : 2 ≤ K) :
  (r : ℝ) + 1 ≤ n ^ ((r : ℝ) / K) * K := by
  have h4 : ((r : ℝ) + 1) / K ≤ 2 ^ ((r : ℝ) / K) := by
    transitivity (r : ℝ) / K + 1 / 2
    · rw [add_div]
      simp only [one_div, add_le_add_iff_left]
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 h2
    · exact bernoulli_aux _
  have hK0 : 0 < K := by
    positivity
  transitivity (2 : ℝ) ^ ((r : ℝ) / K) * K
  · rwa [← div_le_iff₀ hK0]
  · apply mul_le_mul_of_nonneg_right _ hK0.le
    exact Real.rpow_le_rpow (by positivity) h1 (div_nonneg (Nat.cast_nonneg _) hK0.le)

lemma divisor_function_exact_prime_power (r : ℕ) {p : ℕ} (h : p.Prime) :
    ArithmeticFunction.sigma 0 (p ^ r) = r + 1 := by
  simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := r) h

lemma divisor_function_exact {n : ℕ} :
  n ≠ 0 → ArithmeticFunction.sigma 0 n = n.factorization.prod (fun _ k ↦ k + 1) := by
  intro hn
  change ArithmeticFunction.sigma 0 n = n.primeFactors.prod (fun p ↦ n.factorization p + 1)
  simpa [ArithmeticFunction.sigma_zero_apply] using (Nat.card_divisors hn)

lemma divisor_function_div_pow_eq {n : ℕ} (K : ℝ) (hn : n ≠ 0) :
  (ArithmeticFunction.sigma 0 n : ℝ) / (n : ℝ) ^ K⁻¹ =
    n.factorization.prod (fun p k ↦ (k + 1) / ((p : ℝ) ^ ((k : ℝ) / K))) := by
  change
      (ArithmeticFunction.sigma 0 n : ℝ) / (n : ℝ) ^ K⁻¹ =
        n.primeFactors.prod
          (fun p ↦ (n.factorization p + 1) / ((p : ℝ) ^ ((n.factorization p : ℝ) / K)))
  rw [div_eq_mul_inv]
  have hsigma : (ArithmeticFunction.sigma 0 n : ℝ) =
      n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) := by
    exact_mod_cast (divisor_function_exact (n := n) hn)
  rw [hsigma]
  have hpow : (n : ℝ) ^ K⁻¹ =
      n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
    calc
      (n : ℝ) ^ K⁻¹ = (((n.factorization.prod fun p k => p ^ k : ℕ) : ℕ) : ℝ) ^ K⁻¹ := by
        rw [Nat.prod_factorization_pow_eq_self hn]
      _ = (n.primeFactors.prod fun p ↦ ((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹ := by
        simp [Finsupp.prod]
      _ = n.primeFactors.prod (fun p ↦ (((p : ℕ) : ℝ) ^ (n.factorization p)) ^ K⁻¹) := by
        symm
        exact Real.finsetProd_rpow _ (fun p => ((p : ℕ) : ℝ) ^ (n.factorization p))
          (by intro p hp; positivity) _
      _ = n.primeFactors.prod (fun p ↦ (p : ℝ) ^ ((n.factorization p : ℝ) / K)) := by
        congr with p
        rw [← Real.rpow_natCast, ← Real.rpow_mul, div_eq_mul_inv]
        positivity
  rw [hpow]
  simpa [div_eq_mul_inv] using (show
    n.primeFactors.prod (fun p ↦ (n.factorization p + 1 : ℝ)) *
        n.primeFactors.prod (fun p ↦ ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) =
      n.primeFactors.prod
        (fun p ↦ (n.factorization p + 1 : ℝ) * ((p : ℝ) ^ ((n.factorization p : ℝ) / K))⁻¹) by
      rw [← Finset.prod_mul_distrib])

lemma prod_of_subset_le_prod_of_one_le {ι N : Type*} [CommSemiring N] [Preorder N]
    [ZeroLEOneClass N] [PosMulMono N]
    {s t : Finset ι} {f : ι → N} (h : t ⊆ s) (hs : ∀ i ∈ t, 0 ≤ f i)
    (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
  ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  exact Finset.prod_le_prod_of_subset_of_one_le₀ h hs hf

lemma anyk_divisor_bound (n : ℕ) {K : ℝ} (hK : 2 ≤ K) :
  (ArithmeticFunction.sigma 0 n : ℝ) ≤ (n : ℝ) ^ (1 / K) * K ^ ((2 : ℝ) ^ K) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [ArithmeticFunction.sigma_apply, Nat.divisors_zero, Nat.cast_zero, pow_zero]
    rw [zero_rpow]
    · simp
    · simpa [one_div] using inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_two hK))
  rw [show (n : ℝ) ^ (1 / K) = (n : ℝ) ^ K⁻¹ by rw [one_div], mul_comm]
  rw [← div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)]
  rw [divisor_function_div_pow_eq _ hn.ne']
  let s : Finset ℕ := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ K)
  have hsubset : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine (Finset.prod_le_prod_of_subset_of_le_one₀ hsubset ?_ ?_).trans ?_
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp hp'
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpbound : (2 : ℝ) ^ K ≤ p := by
      apply le_of_not_gt
      intro hlt
      exact hp' (by simp [s, hp, hlt])
    rw [div_le_iff₀]
    · simpa using div_bound_aux1 (p : ℝ) (n.factorization p) K hpbound (by linarith)
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  refine (Finset.prod_le_prod₀ ?_ ?_).trans ((Finset.prod_const K).trans_le ?_)
  · intro i hi
    exact div_nonneg (Nat.cast_add_one_pos _).le (by positivity)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors (hsubset hp)
    rw [div_le_iff₀]
    · simpa [mul_comm] using
        div_bound_aux2 (p : ℝ) (n.factorization p) K
          (by exact_mod_cast hpprime.two_le) hK
    · exact Real.rpow_pos_of_pos (by exact_mod_cast hpprime.pos) _
  · rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    have hsIcc : s ⊆ Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊ := by
      intro p hp
      have hp' : p ∈ n.primeFactors ∧ (p : ℝ) < (2 : ℝ) ^ K := by
        simpa [s] using hp
      rw [Finset.mem_Icc]
      refine ⟨Nat.pos_of_mem_primeFactors hp'.1, ?_⟩
      rw [Nat.le_floor_iff (by positivity)]
      exact hp'.2.le
    have hsle : s.card ≤ ⌊((2 : ℝ) ^ K)⌋₊ := by
      calc
        s.card ≤ (Finset.Icc 1 ⌊((2 : ℝ) ^ K)⌋₊).card := Finset.card_le_card hsIcc
        _ = ⌊((2 : ℝ) ^ K)⌋₊ := by
          rw [Nat.card_Icc]
          omega
    exact le_trans (by exact_mod_cast hsle) (Nat.floor_le (by positivity))

lemma log_log_mul_log_div_rpow {ε : ℝ} (hε : 0 < ε) :
  Tendsto (fun x : ℝ ↦ log (log x) * log x / x ^ ε) atTop (𝓝 0) := by
  refine IsLittleO.tendsto_div_nhds_zero ?_
  refine ((isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).mul_isBigO
    (isBigO_refl _ _)).trans ?_
  refine ((isLittleO_log_rpow_atTop (half_pos hε)).pow two_pos).congr' ?_ ?_
  · filter_upwards with x using by simp [sq]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_two, ← Real.rpow_mul hx, div_mul_cancel₀ ε two_ne_zero]

lemma divisor_bound₁ {ε : ℝ} (hε1 : 0 < ε) (hε2 : ε ≤ 1) :
  ∀ᶠ (n : ℕ) in atTop,
      (ArithmeticFunction.sigma 0 n : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := tendsto_log_coe_at_top
  have hx :
      Tendsto
        (fun n : ℕ =>
          2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3)))
        atTop (𝓝 0) := by
    simpa using
      ((log_log_mul_log_div_rpow (div_pos hε1 zero_lt_three)).comp hl).const_mul 2
  have hε : 0 < Real.log 2 * ε / 2 := by
    exact half_pos (mul_pos (Real.log_pos one_lt_two) hε1)
  filter_upwards
    [tendsto_log_log_coe_at_top (eventually_ge_atTop ((Real.log 2 * (1 + ε / 2))⁻¹)),
      tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ)),
      hl (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_log_coe_at_top (eventually_ge_atTop (2 * Real.log 2 * (1 + ε / 2))),
      h (eventually_gt_atTop (0 : ℝ)),
      hx (Metric.closedBall_mem_nhds 0 hε)] with
    n hlln' hlln hln hlln'' hn hx'
  dsimp at hlln hlln' hln hlln'' hn
  set K : ℝ := log (log (n : ℝ)) / (Real.log 2 * (1 + ε / 2)) with hK
  have hpowK_pos : 0 < (2 : ℝ) ^ K := Real.rpow_pos_of_pos zero_lt_two _
  have hε' : 0 < Real.log 2 * (1 + ε / 2) := by
    exact mul_pos (Real.log_pos one_lt_two) (by linarith)
  have hpowK : (2 : ℝ) ^ K ≤ Real.log n ^ (1 - ε / 3) := by
    refine (Real.log_le_log_iff hpowK_pos (Real.rpow_pos_of_pos hln _)).mp ?_
    rw [Real.log_rpow zero_lt_two,
      Real.log_rpow hln, hK, mul_comm (Real.log 2), ← div_div,
      div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne', div_le_iff₀]
    · have hfactor : 1 ≤ (1 - ε / 3) * (1 + ε / 2) := by
        nlinarith [hε1, hε2]
      have hmain :
          log (log (n : ℝ)) ≤
            ((1 - ε / 3) * (1 + ε / 2)) * log (log (n : ℝ)) :=
        le_mul_of_one_le_left hlln.le hfactor
      nlinarith [hmain]
    · linarith
  have hlogK : log K ≤ 2 * log (log (Real.log n)) := by
    have haux : log ((Real.log 2 * (1 + ε / 2))⁻¹) ≤ log (log (Real.log n)) := by
      exact log_le_log_of_le (inv_pos.2 hε') hlln'
    rw [hK, div_eq_mul_inv, Real.log_mul hlln.ne' (inv_ne_zero (ne_of_gt hε')), two_mul]
    linarith
  have hK₂ : 2 ≤ K := by
    rwa [le_div_iff₀ hε', ← mul_assoc]
  have hK₀ : 0 < K := zero_lt_two.trans_le hK₂
  have hK' : 0 < K ^ ((2 : ℝ) ^ K) := Real.rpow_pos_of_pos hK₀ _
  refine (anyk_divisor_bound n hK₂).trans ?_
  refine (Real.log_le_log_iff (mul_pos (Real.rpow_pos_of_pos hn _) hK')
    (Real.rpow_pos_of_pos hn _)).mp ?_
  rw [
    Real.log_mul (Real.rpow_pos_of_pos hn _).ne' hK'.ne', Real.log_rpow hn, Real.log_rpow hK₀,
    Real.log_rpow hn]
  have hmul :
      (2 : ℝ) ^ K * log K ≤
        Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) :=
    mul_le_mul hpowK hlogK (Real.log_nonneg (one_le_two.trans hK₂)) (Real.rpow_nonneg hln.le _)
  have hsum :
      1 / K * log (n : ℝ) + (2 : ℝ) ^ K * log K ≤
        1 / K * log (n : ℝ) +
          Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hmul (1 / K * log (n : ℝ))
  refine hsum.trans ?_
  rw [hK, one_div_div, ← div_mul_eq_mul_div]
  suffices hs :
      Real.log n ^ (1 - ε / 3) * (2 * log (log (log (n : ℝ)))) ≤
        Real.log 2 / log (log (n : ℝ)) * (ε / 2) * log (n : ℝ) by
    linarith
  suffices hs' :
      2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / (log (n : ℝ) ^ (ε / 3))) ≤
        Real.log 2 * ε / 2 by
    rw [Real.rpow_sub hln, div_eq_mul_one_div, Real.rpow_one, div_mul_eq_mul_div,
      mul_comm _ (log (n : ℝ)), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hln.le
    rw [le_div_iff₀ hlln]
    field_simp at hs' ⊢
    simpa [mul_assoc] using hs'
  have hx'' :
      |2 * (log (log (log (n : ℝ))) * log (log (n : ℝ)) / log (n : ℝ) ^ (ε / 3))| ≤
        Real.log 2 * ε / 2 := by
    simpa [mem_closedBall_zero_iff, norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by positivity),
      abs_of_pos (Real.rpow_pos_of_pos hln _)] using hx'
  exact le_of_abs_le hx''

lemma divisor_bound {ε : ℝ} (hε1 : 0 < ε) :
  ∀ᶠ (n : ℕ) in atTop,
      (ArithmeticFunction.sigma 0 n : ℝ) ≤
        n ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) := by
  rcases le_total ε 1 with hε2 | hε2
  · exact divisor_bound₁ hε1 hε2
  · filter_upwards
      [divisor_bound₁ zero_lt_one le_rfl,
        tendsto_log_log_coe_at_top (eventually_ge_atTop (0 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with n hn hn' hn''
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn'') ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Real.log_nonneg one_le_two) hn')

lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ (n : ℕ) in atTop, (ArithmeticFunction.sigma 0 n : ℝ) ≤ (n : ℝ)^ε := by
  rcases le_total (1 : ℝ) ε with hε1 | hε1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine trivial_divisor_bound.trans ?_
    exact Real.le_rpow_self_of_one_le (by exact_mod_cast hn) hε1
  · have hx : Tendsto (fun n : ℕ => Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹) atTop (𝓝 0) := by
      simpa [mul_assoc] using
        (tendsto_log_log_coe_at_top.inv_tendsto_atTop).const_mul (Real.log 2 * 2)
    filter_upwards
      [divisor_bound zero_lt_one,
        eventually_ge_atTop (1 : ℕ),
        hx (Metric.closedBall_mem_nhds 0 hε)] with n hn hn' hx'
    have hx'' : |Real.log 2 * 2 * (log (log (n : ℝ)))⁻¹| ≤ ε := by
      simpa [mem_closedBall_zero_iff, norm_eq_abs] using hx'
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn') ?_)
    rw [div_mul_eq_mul_div, div_eq_mul_inv]
    simpa [one_add_one_eq_two, mul_assoc, mul_left_comm, mul_comm] using le_of_abs_le hx''

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 y = summatory (fun n ↦ Real.log n) 1 x := by
  simpa using
    (summatory_mul_floor_eq_summatory_sum_divisors hx xy (fun n => Λ n)).trans <| by
      simp_rw [ArithmeticFunction.vonMangoldt_sum]

lemma helpful_floor_identity {x : ℝ} :
  ⌊x⌋ - 2 * ⌊x/2⌋ ≤ 1 := by
  have h : (⌊x⌋ - 2 * ⌊x / 2⌋ : Int) < 2 := by
    exact_mod_cast (show ((⌊x⌋ : ℝ) - 2 * ⌊x / 2⌋) < 2 by
      linarith [Int.sub_one_lt_floor (x / 2), Int.floor_le x])
  linarith

lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 := by
  have h₁ : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hx₁, by simpa [one_add_one_eq_two] using hx₂⟩
  have h₂ : ⌊x / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith
  rw [h₁, h₂]
  simp

lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ := by
  have h₄ : (2 * ⌊x / 2⌋ : Int) - 1 < ⌊x⌋ := by
    exact_mod_cast (show (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ by
      linarith [Int.floor_le (x / 2), Int.sub_one_lt_floor x])
  exact Int.sub_one_lt_iff.mp h₄

def chebyshev_error (x : ℝ) : ℝ := by
  exact
    (summatory (fun i ↦ Real.log i) 1 x - (x * log x - x)) -
      2 * (summatory (fun i ↦ Real.log i) 1 (x / 2) - (x / 2 * log (x / 2) - x / 2))

lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x =
    Real.log 2 * x + chebyshev_error x := by
  have hhalf :
      summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Real.log n) 1 (x / 2) := by
    rw [show summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Λ n * ⌊(x / 2) / n⌋) 1 x by
          rw [summatory]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_right_comm]]
    exact von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le)
  have hx2 : (2 : ℝ) * (x / 2) = x := by
    simpa using (mul_div_cancel₀ x two_ne_zero)
  calc
    summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x
      = summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 x -
          2 * summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x := by
            rw [summatory, summatory, summatory, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = summatory (fun n ↦ Real.log n) 1 x - 2 * summatory (fun n ↦ Real.log n) 1 (x / 2) := by
          rw [von_mangoldt_summatory hx₀.le le_rfl, hhalf]
    _ = Real.log 2 * x + chebyshev_error x := by
          rw [chebyshev_error, mul_sub, Real.log_div hx₀.ne' two_ne_zero, mul_sub, hx2]
          ring

def chebyshev_first' (x : ℝ) : ℝ := by
  exact ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Real.log n

def chebyshev_second' (x : ℝ) : ℝ := by
  exact Finset.sum (Finset.range ⌊x⌋₊) fun n => Λ n

lemma chebyshev_first_eq {x : ℝ} :
  chebyshev_first x = ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Λ n := by
  change Chebyshev.theta x =
    ∑ n ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Λ n
  rw [Chebyshev.theta_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]

lemma chebyshev_first'_eq {x : ℝ} :
  chebyshev_first' x = ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Λ n := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]

lemma chebyshev_first_le_chebyshev_second : chebyshev_first ≤ chebyshev_second := by
  intro x
  exact Chebyshev.theta_le_psi x

lemma chebyshev_first'_le_chebyshev_second' : chebyshev_first' ≤ chebyshev_second' := by
  intro x
  rw [chebyshev_first'_eq, chebyshev_second']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma chebyshev_first_nonneg : 0 ≤ chebyshev_first := by
  intro x
  exact Chebyshev.theta_nonneg x

lemma chebyshev_first'_nonneg : 0 ≤ chebyshev_first' := by
  intro x
  rw [chebyshev_first'_eq]
  exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma chebyshev_second_nonneg : 0 ≤ chebyshev_second := by
  intro x
  exact Chebyshev.psi_nonneg x

lemma chebyshev_second'_nonneg : 0 ≤ chebyshev_second' := by
  intro x
  rw [chebyshev_second']
  exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma log_nat_nonneg : ∀ (n : ℕ), 0 ≤ log (n : ℝ) := by
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      exact log_nonneg (by simp)

lemma chebyshev_first_monotone : Monotone chebyshev_first := by
  exact Chebyshev.theta_mono

lemma is_O_chebyshev_first_chebyshev_second :
    Asymptotics.IsBigO atTop chebyshev_first chebyshev_second := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with x
  rw [one_mul, norm_of_nonneg (chebyshev_first_nonneg x),
    norm_of_nonneg (chebyshev_second_nonneg x)]
  exact chebyshev_first_le_chebyshev_second x

lemma chebyshev_second_eq_summatory : chebyshev_second = summatory Λ 1 := by
  ext x
  change Chebyshev.psi x = summatory (⇑Λ) 1 x
  rw [Chebyshev.psi_eq_sum_Icc, summatory]
  rw [Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · simp
  · simp

@[simp] lemma chebyshev_first_zero : chebyshev_first 0 = 0 := by
  exact Chebyshev.theta_eq_zero_of_lt_two (by norm_num)

@[simp] lemma chebyshev_second_zero : chebyshev_second 0 = 0 := by
  exact Chebyshev.psi_eq_zero_of_lt_two (by norm_num)

@[simp] lemma chebyshev_first'_zero : chebyshev_first' 0 = 0 := by
  simp [chebyshev_first']

@[simp] lemma chebyshev_second'_zero : chebyshev_second' 0 = 0 := by
  simp [chebyshev_second']

lemma chebyshev_lower_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_error x ≤ chebyshev_second x - Real.log 2 * x := by
  rw [le_sub_iff_add_le', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hfloor : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) ≤ 1 := by
    exact_mod_cast helpful_floor_identity
  simpa using mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg

lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_second x - chebyshev_second (x / 2) - Real.log 2 * x ≤ chebyshev_error x := by
  rw [sub_le_iff_le_add', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  have hs : Finset.Icc 1 ⌊x / 2⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (half_le_self hx.le))
  rw [summatory, ← Finset.sum_sdiff hs, add_sub_cancel_right]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
  · simp_rw [Finset.mem_sdiff, Finset.mem_Icc, and_imp, not_and, not_le, Nat.le_floor_iff hx.le,
      Nat.floor_lt (div_nonneg hx.le zero_le_two), Nat.succ_le_iff]
    intro i hi₁ hi₂ hi₃
    replace hi₃ := hi₃ hi₁
    have hge1 : 1 ≤ x / i := by
      refine (one_le_div₀ ?_).2 hi₂
      exact_mod_cast hi₁
    have hlt2 : x / i < 2 := by
      have hi_pos : (0 : ℝ) < i := by
        exact_mod_cast hi₁
      have hmul : x < 2 * i := by
        linarith
      exact (div_lt_iff₀ hi_pos).2 (by simpa [mul_comm] using hmul)
    have hEq : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) = 1 := by
      exact_mod_cast (helpful_floor_identity2 (x := x / i) hge1 hlt2)
    rw [hEq, mul_one]
  · intro i _ _
    have hcoeff' : (2 : ℝ) * ↑⌊x / ↑i / 2⌋ ≤ ↑⌊x / ↑i⌋ := by
      exact_mod_cast (helpful_floor_identity3 (x := x / i))
    have hcoeff : 0 ≤ (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) := by
      linarith
    simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hcoeff)

lemma chebyshev_error_O :
  Asymptotics.IsBigO atTop chebyshev_error log := by
  have h23 : (2 : ℝ) < 3 := by norm_num
  refine (summatory_log h23).isBigO.sub ?_
  refine (((summatory_log h23).isBigO.comp_tendsto
    (tendsto_id.atTop_div_const zero_lt_two)).const_mul_left 2).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxhalf : 1 ≤ x / 2 := by linarith
  have hxlog : log (x / 2) ≤ log x := log_le_log_of_le (by linarith) (by linarith)
  simpa [Function.comp_apply, one_mul, norm_of_nonneg (log_nonneg hxhalf),
    norm_of_nonneg (log_nonneg (one_le_two.trans hx))] using hxlog

lemma chebyshev_lower_explicit {c : ℝ} (hc : c < Real.log 2) :
  ∀ᶠ x : ℝ in atTop, c * x ≤ chebyshev_second x := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  filter_upwards [eventually_ge_atTop (1 : ℝ), h₁] with x hx₁ hx₂
  have hx₂' : ‖chebyshev_error x‖ ≤ (Real.log 2 - c) * x := by
    simpa [id, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx₁)] using hx₂
  have hmain := (neg_le_of_abs_le hx₂').trans (chebyshev_lower_aux (zero_lt_one.trans_le hx₁))
  linarith

lemma chebyshev_lower :
  Asymptotics.IsBigO atTop id chebyshev_second := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(Real.log 2 / 2)⁻¹, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    chebyshev_lower_explicit (half_lt_self (Real.log_pos one_lt_two))] with x hx₁ hx₂
  rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ (half_pos (Real.log_pos one_lt_two))]
  simp [id, Real.norm_eq_abs, abs_of_nonneg hx₁, norm_of_nonneg (chebyshev_second_nonneg x)]
  simpa [mul_comm] using hx₂

lemma chebyshev_trivial_upper_nat (n : ℕ) :
  chebyshev_second n ≤ n * Real.log n := by
  rw [chebyshev_second_eq_summatory, summatory_nat, ← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ (Real.log n) ?_).trans ?_
  · intro i hi
    apply von_mangoldt_upper.trans
    simp only [Finset.mem_Icc] at hi
    exact log_le_log_of_le (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  · simp

lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  chebyshev_second x ≤ x * log x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← chebyshev_second_eq_summatory]
  refine (chebyshev_trivial_upper_nat _).trans ?_
  refine mul_le_mul (Nat.floor_le hx₀.le)
    ?_ (log_nonneg (by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff x).2 hx
      exact this)) hx₀.le
  · exact log_le_log_of_le (by
      have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Nat.floor_pos.mpr hx)
      exact hfloorpos) (Nat.floor_le hx₀.le)

lemma chebyshev_upper_inductive {c : ℝ} (hc : Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, chebyshev_second x ≤ 2 * c * x + C * log C := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp h₁
  let C : ℝ := max 1 C₀
  refine ⟨C, le_max_left _ _, ?_⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : (n : ℝ) ≤ C
  · rw [chebyshev_second_eq_summatory]
    refine
      (summatory_monotone_of_nonneg _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg) hn).trans
        ?_
    rw [← chebyshev_second_eq_summatory]
    refine (chebyshev_trivial_upper (le_max_left _ _)).trans ?_
    refine le_add_of_nonneg_left (mul_nonneg ?_ (Nat.cast_nonneg _))
    exact mul_nonneg zero_le_two ((Real.log_nonneg one_le_two).trans hc.le)
  · have hn : C < n := lt_of_not_ge hn
    have hn' : 0 < n := by
      refine Nat.succ_le_iff.mp ?_
      exact Nat.one_le_cast.mp ((le_max_left _ _).trans hn.le)
    have h₁ := chebyshev_upper_aux (Nat.cast_pos.mpr hn')
    rw [sub_sub, sub_le_iff_le_add] at h₁
    apply h₁.trans
    rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← Nat.cast_two,
      Nat.floor_div_eq_div, Nat.cast_two, ← add_assoc]
    have h₃ := hC₀ (n : ℝ) ((le_max_right _ _).trans hn.le)
    rw [Real.norm_eq_abs] at h₃
    replace h₃ := le_of_abs_le h₃
    have h₂ := ih (n / 2) (Nat.div_lt_self hn' one_lt_two)
    rw [← chebyshev_second_eq_summatory]
    have hsum :
        chebyshev_error (n : ℝ) + chebyshev_second (n / 2 : ℕ) + Real.log 2 * (n : ℝ) ≤
          (c - Real.log 2) * ‖(n : ℝ)‖ + (2 * c * (n / 2 : ℕ) + C * log C) +
            Real.log 2 * (n : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right (add_le_add h₃ h₂) (Real.log 2 * (n : ℝ))
    refine hsum.trans ?_
    have hc0 : 0 ≤ c := (Real.log_nonneg one_le_two).trans hc.le
    have hdiv : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := Nat.cast_div_le
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    nlinarith

lemma chebyshev_upper_real {c : ℝ} (hc : 2 * Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧
    Asymptotics.IsBigOWith 1 atTop chebyshev_second (fun x ↦ c * x + C * log C) := by
  have hc' : Real.log 2 < c / 2 := by
    nlinarith
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc'
  refine ⟨C, hC₁, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨0, ?_⟩
  intro x hx
  rw [Real.norm_of_nonneg (chebyshev_second_nonneg x), chebyshev_second_eq_summatory,
    summatory_eq_floor, ← chebyshev_second_eq_summatory, one_mul]
  refine (hC ⌊x⌋₊).trans (le_trans ?_ (le_abs_self _))
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ c := by nlinarith
  have hmul : c * (⌊x⌋₊ : ℝ) ≤ c * x := mul_le_mul_of_nonneg_left hfloor hc0
  have hEq : 2 * (c / 2) * (⌊x⌋₊ : ℝ) = c * (⌊x⌋₊ : ℝ) := by ring
  simpa [hEq, add_assoc, add_left_comm, add_comm] using add_le_add_right hmul (C * log C)

lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * Real.log 2 < c) :
  Asymptotics.IsBigOWith c atTop chebyshev_second id := by
  let c' : ℝ := Real.log 2 + c / 2
  have hc'₁ : c' < c := by
    dsimp [c']
    nlinarith
  have hc'₂ : 2 * Real.log 2 < c' := by
    dsimp [c']
    nlinarith
  have hc'₀ : 0 ≤ c' := by
    dsimp [c']
    nlinarith [Real.log_nonneg one_le_two, hc]
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂
  have hconst : (fun _ : ℝ ↦ C * log C) =o[atTop] id := by
    exact (isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop)
  have hmain : Asymptotics.IsBigOWith c atTop (fun x ↦ c' * x + C * log C) id := by
    have hc'₁' : ‖c'‖ < c := by
      simpa [Real.norm_of_nonneg hc'₀] using hc'₁
    simpa [c'] using
      (Asymptotics.isBigOWith_const_mul_self c' id atTop).add_isLittleO hconst hc'₁'
  exact (hC.trans hmain zero_le_one).congr_const (one_mul c)

lemma chebyshev_upper : Asymptotics.IsBigO atTop chebyshev_second id := by
  exact (chebyshev_upper_explicit (lt_add_one _)).isBigO

lemma chebyshev_first_upper : Asymptotics.IsBigO atTop chebyshev_first id := by
  exact is_O_chebyshev_first_chebyshev_second.trans chebyshev_upper

lemma is_O_sum_one_of_summable {f : ℕ → ℝ} (hf : Summable f) :
  Asymptotics.IsBigO atTop (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
    (fun _ ↦ (1 : ℝ)) := by
  simpa using hf.hasSum.tendsto_sum_nat.isBigO_one ℝ

lemma log_le_thing {x : ℝ} (hx : 1 ≤ x) :
  log x ≤ x^(1/2 : ℝ) - x^(-1/2 : ℝ) := by
  set f : ℝ → ℝ := log
  set g : ℝ → ℝ := fun x ↦ x^(1 / 2 : ℝ) - x^(-1 / 2 : ℝ)
  set f' : ℝ → ℝ := Inv.inv
  set g' : ℝ → ℝ := fun x ↦ 1 / 2 * x^(-3 / 2 : ℝ) + 1 / 2 * x^(-1 / 2 : ℝ)
  suffices h : ∀ y ∈ Icc (1 : ℝ) x, f y ≤ g y by
    exact h x ⟨hx, le_rfl⟩
  have f_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt f (f' y) (Ici y) y := by
    intro y hy
    exact (hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').hasDerivWithinAt
  have g_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt g (g' y) (Ici y) y := by
    intro y hy
    have hy' : 0 < y := zero_lt_one.trans_le hy.1
    change HasDerivWithinAt _ (_ + _) _ _
    rw [add_comm, ← sub_neg_eq_add, neg_mul_eq_neg_mul]
    refine HasDerivWithinAt.sub ?_ ?_
    · convert (hasDerivWithinAt_id y (Set.Ici y)).rpow_const (p := (1 / 2 : ℝ)) (Or.inl hy'.ne') using 1 <;> norm_num
    · convert (hasDerivWithinAt_id y (Set.Ici y)).rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl hy'.ne') using 1 <;> norm_num
  have hmain :=
    image_le_of_deriv_right_le_deriv_boundary
      (f := f) (f' := f') (a := 1) (b := x)
      (continuousOn_log.mono fun y hy ↦ (zero_lt_one.trans_le hy.1).ne')
      f_deriv
      (by simp [f])
      ((continuousOn_id.rpow_const (by simp)).sub
        (continuousOn_id.rpow_const fun y hy ↦ Or.inl (zero_lt_one.trans_le hy.1).ne'))
      g_deriv
      (by
        intro y hy
        dsimp [f', g']
        rw [← mul_add, mul_comm, ← div_eq_mul_one_div,
          le_div_iff₀ (show (0 : ℝ) < 2 by norm_num), ← sub_nonneg, ← Real.rpow_neg_one]
        convert sq_nonneg (y^(-1 / 4 : ℝ) - y^(-3 / 4 : ℝ)) using 1
        have hy' : 0 < y := zero_lt_one.trans_le hy.1
        rw [sub_sq, ← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_two,
          ← Real.rpow_mul hy'.le, mul_assoc, ← Real.rpow_add hy', ← Real.rpow_mul hy'.le]
        norm_num
        ring)
  intro y hy
  exact hmain hy

lemma log_div_sq_sub_le {x : ℝ} (hx : 1 < x) :
  log x * ((x⁻¹)^2 / (1 - x⁻¹)) ≤ x^(-3/2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx' : x ≠ 0 := hx0.ne'
  have hden : 0 < x * (x - 1) := by nlinarith
  have hrewrite : (x⁻¹)^2 / (1 - x⁻¹) = 1 / (x * (x - 1)) := by
    field_simp [hx']
  rw [hrewrite, ← div_eq_mul_one_div]
  rw [div_le_iff₀ hden]
  calc
    log x ≤ x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ) := log_le_thing hx.le
    _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by
      have hx1 : x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
        calc
          x ^ (-3 / 2 : ℝ) * x = x ^ (-3 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-3 / 2 : ℝ) 1]; norm_num
      have hx2 : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
        calc
          x ^ (-1 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-1 / 2 : ℝ) 1]; norm_num
      calc
        x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ)
            = x ^ (-1 / 2 : ℝ) * x - x ^ (-1 / 2 : ℝ) := by rw [hx2]
        _ = x ^ (-1 / 2 : ℝ) * (x - 1) := by ring
        _ = (x ^ (-3 / 2 : ℝ) * x) * (x - 1) := by rw [hx1]
        _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by ring

@[to_additive]
lemma prod_prime_powers' {M : Type*} [CommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.prod_sigma', eq_comm]
  refine Finset.prod_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

@[to_additive]
lemma prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [prod_prime_powers']
  refine Finset.prod_congr rfl ?_
  intro p hp
  refine Finset.prod_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

lemma sum_prime_powers' {M : Type*} [AddCommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.sum_sigma', eq_comm]
  refine Finset.sum_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

lemma sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [sum_prime_powers']
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

@[to_additive]
lemma exact_prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine prod_prime_powers.trans (Finset.prod_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.prod_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

lemma exact_sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine sum_prime_powers.trans (Finset.sum_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

theorem geom_sum_Ico'_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {m n : ℕ} (_hmn : m ≤ n) :
  ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  exact geom_sum_Ico_le_of_lt_one hx₀ hx₁

lemma abs_von_mangoldt_div_self_sub_log_div_self_le {x : ℝ} :
  |∑ n ∈ Icc 1 (⌊x⌋₊), Λ n / (n : ℝ) -
      ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p / (p : ℝ)| ≤
    ∑ n ∈ Icc 1 (⌊x⌋₊), (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h₁ : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) =
      ∑ n ∈ filter IsPrimePow (Icc 1 ⌊x⌋₊), Λ n / (n : ℝ) := by
    symm
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp <| by
      intro hΛ
      exact hne (by simp [hΛ])
  have h₂ : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ) =
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p / (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [h₁, h₂, sum_prime_powers, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  simp only [Finset.mem_Icc, Nat.cast_pow, and_imp]
  intro p hp₁ hp₂
  split_ifs with hp
  · have hp₃ : (p : ℝ) ≤ x := (Nat.le_floor_iff' hp.ne_zero).1 hp₂
    have hInsert :
        insert 1 (filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊)) =
          filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 1 ⌊x⌋₊) := by
      rw [Finset.Icc_eq_insert_Icc_succ (hp₁.trans hp₂), filter_insert, pow_one, ite_eq_left]
      exact hp₃
    have hnotmem : 1 ∉ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊) := by
      simp
    rw [← hInsert, Finset.sum_insert hnotmem, add_comm, pow_one, pow_one]
    have hcancel :
        (∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ)) +
            Λ p / (p : ℝ) - Λ p / (p : ℝ) =
          ∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ) := by
      ring
    rw [hcancel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans ?_
    · intro i hi hmem
      exact abs_nonneg _
    have hsum :
        (∑ i ∈ Icc 2 ⌊x⌋₊, |Λ (p ^ i) / (p ^ i : ℝ)|) =
          ∑ i ∈ Icc 2 ⌊x⌋₊, Λ p / (p ^ i : ℝ) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_pow
          ((zero_lt_two.trans_le (Finset.mem_Icc.mp hk).1).ne'), abs_div,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_pow, Nat.abs_cast]
    rw [hsum, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp only [div_eq_mul_inv, ← mul_sum, ← inv_pow]
    refine le_trans ?_ (log_div_sq_sub_le (by exact_mod_cast hp.one_lt))
    rw [show Finset.Icc 2 ⌊x⌋₊ = Finset.Ico 2 (⌊x⌋₊ + 1) by
      ext i
      simp]
    refine mul_le_mul_of_nonneg_left (geom_sum_Ico'_le ?_ ?_ ?_) ?_
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    · exact Nat.succ_le_succ (hp₁.trans hp₂)
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rw [abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x ↦ Finset.sum (range (⌊x⌋₊ + 1)) (fun n ↦ (n : ℝ) ^ (-3 / 2 : ℝ))
  have hbound : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ)‖ ≤ ‖g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_von_mangoldt_div_self_sub_log_div_self_le (x := x)).trans ?_
    refine le_trans ?_ (le_abs_self _)
    dsimp [g]
    rw [range_eq_Ico]
    exact Finset.sum_mono_set_of_nonneg (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Icc_subset_Icc_left zero_le_one)
  have hbound' : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹‖ ≤ 1 * ‖g x‖ := by
    intro x
    simpa [g, div_eq_mul_inv, one_mul] using hbound x
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound')).trans ?_
  refine (is_O_sum_one_of_summable ((Real.summable_nat_rpow).2 (by norm_num))).comp_tendsto ?_
  exact (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop

lemma summatory_log_sub :
  Asymptotics.IsBigO atTop
    (fun x ↦
      (∑ n ∈ Icc 1 (⌊x⌋₊), log (n : ℝ)) -
        x * ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹)
    (fun x ↦ x) := by
  have hbound : ∀ x : ℝ, 0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ)| ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n := by
    intro x hx
    rw [← summatory, ← von_mangoldt_summatory hx le_rfl, mul_sum, summatory,
      ← Finset.sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [mul_div_left_comm x, abs_sub_comm, ← mul_sub, abs_mul,
      ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg, Int.self_sub_floor, Int.fract_nonneg]
    refine Finset.sum_le_sum fun n hn ↦ ?_
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Int.fract_lt_one _).le
  refine Asymptotics.IsBigO.trans ?_ chebyshev_upper
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [one_mul, norm_eq_abs, chebyshev_second_eq_summatory,
    norm_of_nonneg (summatory_nonneg _ _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg))]
  exact hbound x hx

lemma is_O_von_mangoldt_div_self :
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ - log x)
    (fun _ ↦ (1 : ℝ)) := by
  suffices h :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦ x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ - x * log x)
        (fun x ↦ x) by
    refine ((isBigO_refl (fun x : ℝ ↦ x⁻¹) atTop).mul h).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← mul_sub, inv_mul_cancel_left₀ hx.ne']
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [inv_mul_cancel₀ hx.ne']
  refine summatory_log_sub.symm.triangle ?_
  have h₁ := (summatory_log (lt_add_one 2)).isBigO
  refine ((h₁.trans isLittleO_log_id_atTop.isBigO).sub (isBigO_refl _ _)).congr_left ?_
  intro x
  dsimp [summatory]
  ring

lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [AddCommMonoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 := by
  ext x
  rw [prime_summatory, prime_summatory]
  refine (Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_left one_le_two))
    (fun y hy => ?_) (fun _ _ => rfl)).symm
  rcases Finset.mem_sdiff.mp hy with ⟨hy1, hy2⟩
  rcases Finset.mem_filter.mp hy1 with ⟨hyIcc, hyPrime⟩
  exact False.elim <| hy2 <|
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hyPrime.two_le, (Finset.mem_Icc.mp hyIcc).2⟩, hyPrime⟩

lemma log_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ Real.log p / p) 1 x - log x)
    (fun _ ↦ (1 : ℝ)) := by
  exact is_O_von_mangoldt_div_self_sub_log_div_self.symm.triangle is_O_von_mangoldt_div_self

lemma prime_counting_le_self (x : ℕ) : π x ≤ x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have :
      (Finset.range (x + 1)).filter Nat.Prime ⊆ Finset.Ioc 0 x := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨hn.2.pos, Nat.lt_succ_iff.mp hn.1⟩
  exact (Finset.card_le_card this).trans (by simp)

lemma chebyshev_first_eq_prime_summatory :
  chebyshev_first = prime_summatory (fun n ↦ Real.log n) 1 := by
  ext x
  change Chebyshev.theta x = prime_summatory (fun n ↦ Real.log n) 1 x
  rw [Chebyshev.theta_eq_sum_Icc, prime_summatory]
  congr 1

@[simp] lemma prime_counting'_zero : π' 0 = 0 := by
  rfl

@[simp] lemma prime_counting'_one : π' 1 = 0 := by
  rfl

@[simp] lemma prime_counting'_two : π' 2 = 0 := by
  rfl

lemma chebyshev_first_trivial_bound (x : ℝ) :
  chebyshev_first x ≤ π ⌊x⌋₊ * log x := by
  by_cases hx : x ≤ 0
  · rw [show chebyshev_first = Chebyshev.theta by rfl]
    rw [Chebyshev.theta_eq_zero_of_lt_two (lt_of_le_of_lt hx (by norm_num : (0 : ℝ) < 2))]
    simp [Nat.floor_eq_zero.2 (hx.trans_lt zero_lt_one)]
  · have hx0 : 0 < x := lt_of_not_ge hx
    rw [chebyshev_first_eq_prime_summatory, prime_summatory, prime_counting_eq_card_primes,
      ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ (log x) ?_
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hy
    have hyle : (y : ℝ) ≤ x := by
      exact le_trans (by exact_mod_cast hy.1.2) (Nat.floor_le hx0.le)
    exact log_le_log_of_le (show 0 < (y : ℝ) by exact_mod_cast hy.2.pos) hyle

lemma prime_counting_eq_prime_summatory {x : ℕ} :
  π x = prime_summatory (fun _ ↦ 1) 1 x := by
  simp [prime_summatory, prime_counting_eq_card_primes]

lemma prime_counting_eq_prime_summatory' {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) = prime_summatory (fun _ ↦ (1 : ℝ)) 1 x := by
  rw [prime_counting_eq_prime_summatory]
  simp [prime_summatory]

lemma chebyshev_first_sub_prime_counting_mul_log_eq {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) * log x - chebyshev_first x = ∫ t in Icc 1 x, π ⌊t⌋₊ * t⁻¹ := by
  have hmul :
      (fun n : ℕ ↦ ite (Nat.Prime n) (Real.log n : ℝ) 0) =
        fun n : ℕ ↦ ite (Nat.Prime n) (1 : ℝ) 0 * Real.log n := by
    funext n
    rw [boole_mul]
  simp only [chebyshev_first_eq_prime_summatory, prime_summatory_eq_summatory,
    prime_counting_eq_prime_summatory']
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', hmul,
    partial_summation_cont' (fun n ↦ ite (Nat.Prime n) (1 : ℝ) 0) Real.log (fun y ↦ y⁻¹)
      one_ne_zero (fun y hy ↦ hasDerivAt_log <| by
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        intro hzero
        rw [hzero] at hy'
        norm_num at hy')
      (by
        refine ContinuousOn.inv₀ continuousOn_id ?_
        intro y hy hzero
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        rw [hzero] at hy'
        norm_num at hy') x, Nat.cast_one]

lemma is_O_chebyshev_first_sub_prime_counting_mul_log :
  Asymptotics.IsBigO atTop
    (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x - chebyshev_first x) id := by
  simp only [chebyshev_first_sub_prime_counting_mul_log_eq]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  change ‖∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹‖ ≤ 1 * ‖x‖
  rw [one_mul, Real.norm_of_nonneg hx0]
  have b₁ : ∀ y : ℝ, 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ := by
    intro y hy
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (by linarith))
  have b₃ :
      (fun a : ℝ ↦ (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Icc 1 x)] fun _ : ℝ ↦ (1 : ℝ) := by
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), (π ⌊y⌋₊ : ℝ) * y⁻¹ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [← div_eq_mul_inv]
      have hy0 : 0 < y := by linarith [hy.1]
      rw [div_le_one hy0]
      simpa using
        le_trans (Nat.cast_le.2 (prime_counting_le_self _))
          (Nat.floor_le (zero_le_one.trans hy.1))
  have hnonneg :
      0 ≤ ∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹ := by
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  rw [norm_eq_abs, abs_of_nonneg hnonneg]
  refine (integral_mono_of_nonneg ?_ (by simp) b₃).trans ?_
  · change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  · have hconst : ∫ _ in Icc 1 x, (1 : ℝ) = x - 1 := by
      simp [hx.le]
    rw [hconst]
    linarith

lemma is_O_prime_counting_div_log :
  Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ)) (fun x ↦ x / log x) := by
  have h :
      Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) id := by
    refine (is_O_chebyshev_first_sub_prime_counting_mul_log.add chebyshev_first_upper).congr_left ?_
    intro x
    ring
  refine (Asymptotics.IsBigO.mul h (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_assoc, mul_inv_cancel₀ (Real.log_pos hx).ne', mul_one]
  · filter_upwards with x
    simp [div_eq_mul_inv]

lemma prime_counting_le_const_mul_div_log :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, (π (⌊x⌋₊) : ℝ) ≤ c * ‖x / Real.log x‖ := by
  obtain ⟨c₀, hc₀, hc₀'⟩ := is_O_prime_counting_div_log.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc₀'
  obtain ⟨c₁, hc₁⟩ := hc₀'
  refine ⟨max c₀ c₁, lt_max_of_lt_left hc₀, ?_⟩
  intro x
  have hmax : 0 < max c₀ c₁ := lt_max_of_lt_left hc₀
  have hc₁' :
      ∀ y : ℝ, c₁ ≤ y → ‖(π ⌊y⌋₊ : ℝ)‖ ≤ c₀ * ‖y / Real.log y‖ := by
    intro y hy
    exact hc₁ y hy
  simp only [Real.norm_natCast] at hc₁'
  rcases le_total c₁ x with hx₀ | hx₀
  · exact (hc₁' x hx₀).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rcases lt_trichotomy x 1 with hx₁ | rfl | hx₁
  · rw [Nat.floor_eq_zero.2 hx₁, Nat.primeCounting_zero, Nat.cast_zero]
    exact mul_nonneg (le_max_of_le_left hc₀.le) (norm_nonneg _)
  · simp
  refine (Nat.cast_le.2 (prime_counting_le_self ⌊x⌋₊)).trans ?_
  refine (((Nat.floor_le (zero_le_one.trans hx₁.le)).trans hx₀).trans (le_max_right c₀ c₁)).trans ?_
  rw [le_mul_iff_one_le_right hmax, norm_div, Real.norm_of_nonneg (Real.log_nonneg hx₁.le),
    Real.norm_of_nonneg (zero_le_one.trans hx₁.le), one_le_div (Real.log_pos hx₁)]
  exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hx₁)).trans (by simp)

lemma chebyshev_second_sub_chebyshev_first_eq {x : ℝ} (hx : 2 ≤ x) :
  chebyshev_second x - chebyshev_first x ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
  rw [show chebyshev_second = Chebyshev.psi by rfl, show chebyshev_first = Chebyshev.theta by rfl]
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx, add_tsub_cancel_left]
  refine (Finset.sum_le_card_nsmul _ _ ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * log x) ?_).trans ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hpow : x ^ (1 / k : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (one_le_two.trans hx)
      refine one_div_le_one_div_of_le zero_lt_two hk'
    apply (chebyshev_first_monotone hpow).trans
    refine (chebyshev_first_le_chebyshev_second _).trans ?_
    refine (chebyshev_trivial_upper (one_le_rpow (one_le_two.trans hx) (by positivity))).trans ?_
    rw [Real.log_rpow (zero_lt_two.trans_le hx)]
    ring_nf
    exact le_rfl
  · have hcard :
        ((Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊).card : ℝ) ≤ Real.log x / Real.log 2 := by
      let m : ℕ := ⌊Real.log x / Real.log 2⌋₊
      refine le_trans ?_ (Nat.floor_le ?_)
      · have hsub : Finset.Icc 2 m ⊆ Finset.Icc 1 m := by
          intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          exact ⟨one_le_two.trans hn.1, hn.2⟩
        have hcard' : ((Finset.Icc 2 m).card : ℝ) ≤ ((Finset.Icc 1 m).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        simp [m, Nat.card_Icc] at hcard' ⊢
      · exact div_nonneg (Real.log_nonneg (one_le_two.trans hx)) (Real.log_pos one_lt_two).le
    rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_right hcard ?_).trans ?_
    · exact
        mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.log_nonneg (one_le_two.trans hx))
    have hconst : (1 / 2 : ℝ) / Real.log 2 ≤ 1 := by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]
      linarith [Real.log_two_gt_d9]
    have hfac :
        (Real.log x / Real.log 2) * ((1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * Real.log x) =
          ((1 / 2 : ℝ) / Real.log 2) * (x ^ (1 / 2 : ℝ) * (Real.log x)^2) := by
      field_simp [(Real.log_pos one_lt_two).ne']
    rw [hfac]
    refine (mul_le_mul_of_nonneg_right hconst ?_).trans ?_
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · simp

lemma chebyshev_first_two : chebyshev_first 2 = Real.log 2 := by
  rw [chebyshev_first_eq_prime_summatory, prime_summatory]
  norm_num
  rw [show (Finset.Icc 1 2).filter Nat.Prime = ({2} : Finset ℕ) by decide]
  simp

lemma chebyshev_first_trivial_lower : ∀ x, 2 ≤ x → 0.5 ≤ chebyshev_first x := by
  intro x hx
  have hmono : chebyshev_first 2 ≤ chebyshev_first x := chebyshev_first_monotone hx
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  rw [chebyshev_first_two] at hmono
  linarith

lemma chebyshev_first_lower : Asymptotics.IsBigO atTop id chebyshev_first := by
  have hdiffO :
      Asymptotics.IsBigO atTop
        (fun x ↦ chebyshev_second x - chebyshev_first x)
        (fun x ↦ x ^ (1 / 2 : ℝ) * (log x)^2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hnonneg₁ : 0 ≤ chebyshev_second x - chebyshev_first x := by
      exact sub_nonneg_of_le (chebyshev_first_le_chebyshev_second x)
    have hnonneg₂ : 0 ≤ x ^ (1 / 2 : ℝ) * (log x)^2 := by
      exact mul_nonneg (by positivity) (sq_nonneg _)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hnonneg₁, Real.norm_eq_abs, abs_of_nonneg hnonneg₂]
    exact chebyshev_second_sub_chebyshev_first_eq hx
  have hdiff :
      Asymptotics.IsLittleO atTop
        (fun x ↦ chebyshev_second x - chebyshev_first x) id := by
    refine hdiffO.trans_isLittleO ?_
    have ht : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)^2) (fun x ↦ x ^ (1 / 2 : ℝ)) := by
      refine ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).pow two_pos).congr' ?_ ?_
      · filter_upwards with x using by simp [sq]
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_two, ← Real.rpow_mul hx]
        congr 1
        ring
    refine ((isBigO_refl (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) atTop).mul_isLittleO ht).congr' ?_ ?_
    · filter_upwards with x using by rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx, add_halves, Real.rpow_one]
      rfl
  have haux := hdiff.symm.trans_isBigO chebyshev_lower
  exact (chebyshev_lower.trans haux.right_isBigO_add).congr_right (fun x ↦ by ring)

lemma chebyshev_first_all :
  ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → c * ‖x‖ ≤ ‖chebyshev_first x‖ := by
  obtain ⟨c₀, hc₀, h⟩ := chebyshev_first_lower.exists_pos
  obtain ⟨X, hX⟩ := eventually_atTop.1 h.bound
  let c : ℝ := max c₀ (2 * X)
  have hc : 0 < c := lt_max_of_lt_left hc₀
  refine ⟨c⁻¹, inv_pos.2 hc, ?_⟩
  intro x hx
  rw [inv_mul_le_iff₀ hc]
  rcases le_total X x with hx' | hx'
  · exact (hX x hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [Real.norm_of_nonneg (chebyshev_first_nonneg x), Real.norm_of_nonneg (zero_le_two.trans hx)]
  have hhalf : (1 / 2 : ℝ) ≤ chebyshev_first x := by
    have hlow := chebyshev_first_trivial_lower x hx
    norm_num at hlow ⊢
    exact hlow
  refine hx'.trans ?_
  rw [show X = (2 * X) * (1 / 2 : ℝ) by ring]
  exact
    (mul_le_mul (le_max_right c₀ (2 * X)) hhalf (by norm_num) hc.le)


lemma is_O_div_log_prime_counting :
  Asymptotics.IsBigO atTop (fun x ↦ x / log x) (fun x ↦ (π ⌊x⌋₊ : ℝ)) := by
  have hθ :
      Asymptotics.IsBigO atTop chebyshev_first
        (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with x
    rw [one_mul, Real.norm_of_nonneg (chebyshev_first_nonneg x), Real.norm_eq_abs]
    exact (chebyshev_first_trivial_bound x).trans (le_abs_self _)
  refine ((chebyshev_first_lower.trans hθ).mul
    (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards with x using by simp [id, div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_inv_cancel_right₀ (Real.log_pos hx).ne']

def prime_log_div_sum_error (x : ℝ) : ℝ := by
  exact prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x

lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 2 = log + prime_log_div_sum_error := by
  ext x
  rw [Pi.add_apply, prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two]
  ring

lemma is_O_prime_log_div_sum_error :
    Asymptotics.IsBigO atTop prime_log_div_sum_error (fun _ ↦ (1 : ℝ)) := by
  exact log_reciprocal

@[fun_prop] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability

def prime_reciprocal_integral : ℝ := by
  exact ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹

lemma my_func_continuous_on : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (pow_ne_zero 2 (Real.log_pos hx').ne')

lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ - (log x)⁻¹) ((y * log y ^ 2)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    have hrewrite : (y * log y ^ 2)⁻¹ = -((-y⁻¹) / (log y)^2) := by
      rw [neg_div, neg_neg, div_eq_mul_inv, mul_inv]
    rw [hrewrite]
    exact ((Real.hasDerivAt_log (by linarith)).inv (Real.log_pos hy1).ne').neg
  have hcont : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.uIcc a b) := by
    exact my_func_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont),
    neg_sub_neg]

lemma integral_Ioi_my_func_tendsto_aux {a : ℝ} (ha : 1 < a)
  {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
  Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 (log a)⁻¹) := by
  suffices h :
      Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 ((log a)⁻¹ - 0)) by
    simpa using h
  have hEq :
      ∀ᶠ i in l, ∫ x in a..b i, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log (b i))⁻¹ := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_inv_self_mul_log_sq ha (ha.trans_le hi)]
  rw [tendsto_congr' hEq]
  exact (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hb)).const_sub _

lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log a)⁻¹ a (fun x ↦ ?_) tendsto_id ?_
  · by_cases hx : a ≤ x
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact my_func_continuous_on.mono fun y hy ↦ ha.trans_le hy.1
    · simp [Set.Ioc_eq_empty_of_le (le_of_not_ge hx)]
  · refine (integral_Ioi_my_func_tendsto_aux ha tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop a] with x hx
    have hax : a ≤ x := le_of_lt hx
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    have hy' : y ∈ Set.Icc a x := by simpa [Set.uIcc_of_le hax] using hy
    rw [Real.norm_of_nonneg]
    exact inv_nonneg.2 (mul_nonneg (le_trans (by linarith) hy'.1) (sq_nonneg _))

lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a (integrable_on_my_func_Ioi ha) tendsto_id)
    (integral_Ioi_my_func_tendsto_aux ha tendsto_id)

lemma my_func2_continuous_on : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul (Real.continuousOn_log.mono ?_)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (Real.log_pos hx').ne'

lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ log (log x)) ((y * log y)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    rw [mul_inv, ← div_eq_mul_inv]
    exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos hy1).ne'
  have hcont : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.uIcc a b) := by
    exact my_func2_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]

lemma integrable_on_prime_log_div_sum_error :
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) := by
  obtain ⟨c, hcpos, hcO⟩ := is_O_prime_log_div_sum_error.exists_pos
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hcO.bound
  have hsplit : Ici (2 : ℝ) = Ico 2 k ∪ Ici k := by
    rw [Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Icc 2 k) := by
    refine (continuousOn_id.mul (hlog.pow 2)).inv₀ ?_
    intro y hy
    have hy2 : 2 ≤ y := hy.1
    have hy0 : 0 < y := by linarith
    exact mul_ne_zero hy0.ne' (pow_ne_zero _ (Real.log_pos (by linarith)).ne')
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_congr_set_ae Ico_ae_eq_Icc).2 ?_
    simp only [prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two,
      prime_summatory_eq_summatory, sub_mul]
    refine (partial_summation_integrable _ (ContinuousOn.integrableOn_Icc hlog')).sub ?_
    exact (hlog.mul hlog').integrableOn_Icc
  · have hbound :
        ∀ᵐ x : ℝ ∂volume.restrict (Ici k),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ ‖c * (x * log x ^ 2)⁻¹‖ := by
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul, norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ hx) (norm_nonneg _)).trans ?_
      have hcnorm : c * |(1 : ℝ)| ≤ ‖c‖ := by
        simp [Real.norm_eq_abs, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_right hcnorm (norm_nonneg _)
    refine Integrable.mono (g := fun x ↦ c * (x * log x ^ 2)⁻¹) ?_
      (Measurable.aestronglyMeasurable <| by measurability) hbound
    have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici k) := by
      refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
      exact integrable_on_my_func_Ioi (one_lt_two.trans_le hk₂)
    exact hbase.const_mul c

lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (Real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n * (n : ℝ)⁻¹ else 0
  let f : ℝ → ℝ := fun x ↦ (log x)⁻¹
  let f' : ℝ → ℝ := fun x ↦ (-x⁻¹) / log x ^ 2
  have hdiff : ∀ i ∈ Ici (2 : ℝ), HasDerivAt f (f' i) i := by
    intro i hi
    rw [show f = fun x ↦ (Real.log x)⁻¹ by rfl, show f' i = (-i⁻¹) / log i ^ 2 by rfl]
    have hi2 : (2 : ℝ) ≤ i := hi
    have hi0 : i ≠ 0 := by linarith
    have hi1 : 1 < i := by linarith
    exact (Real.hasDerivAt_log hi0).inv (ne_of_gt (Real.log_pos hi1))
  have hne : ∀ y : ℝ, y ∈ Ici (2 : ℝ) → y ≠ 0 := by
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hcont : ContinuousOn f' (Ici (2 : ℝ)) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_inv₀.mono hne).neg
    · exact (Real.continuousOn_log.mono hne).pow _
    · intro y hy
      exact pow_ne_zero _ (Real.log_pos (one_lt_two.trans_le hy)).ne'
  have hps := partial_summation_cont' a f f' two_ne_zero hdiff hcont x
  rw [sub_eq_iff_eq_add]
  convert hps using 1
  · rw [prime_summatory_eq_summatory]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hpy : y.Prime
    · have hy1 : (1 : ℝ) < y := by
        rw [Nat.one_lt_cast, ← Nat.succ_le_iff]
        exact (Finset.mem_Icc.mp hy).1
      simp [a, f, hpy]
      field_simp [(show (y : ℝ) ≠ 0 by positivity), (Real.log_pos hy1).ne']
    · simp [a, hpy]
  · rw [← prime_summatory_eq_summatory, prime_summatory_log_mul_inv_eq]
    rw [prime_reciprocal_integral]
    simp only [div_eq_mul_inv, Pi.add_apply, add_mul, f', f, neg_mul, mul_neg, integral_neg,
      sub_neg_eq_add, ← mul_inv]
    have h₁ :
        Integrable (fun a ↦ (a * Real.log a)⁻¹)
          (volume.restrict (Icc (((2 : ℕ) : ℝ)) x)) := by
      exact (my_func2_continuous_on.mono fun y hy ↦ one_lt_two.trans_le hy.1).integrableOn_Icc
    have hEq :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, Real.log a * (a * Real.log a ^ 2)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Icc (((2 : ℕ) : ℝ)) x, (a * Real.log a)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro y hy
      dsimp
      rw [mul_inv, mul_inv, mul_left_comm, ← div_eq_mul_inv, sq, div_self_mul_self']
    have hErrIcc :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Ioc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      convert
        (integral_Icc_eq_integral_Ioc
          (f := fun a : ℝ ↦ prime_log_div_sum_error a * (a * log a ^ 2)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
        using 1
    have hErrTail :
        ∫ t in Ici x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      convert
        (integral_Ici_eq_integral_Ioi
          (f := fun t : ℝ ↦ prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
          (x := x) (μ := volume))
        using 1
    have hInvIcc :
        ∫ t in Icc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ =
          ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ := by
      simpa using
        (integral_Icc_eq_integral_Ioc (f := fun t : ℝ ↦ (t * log t)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
    have hInv :
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = log (log x) - log (log 2) := by
      calc
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = ∫ t in (2 : ℝ)..x, (t * log t)⁻¹ := by
          symm
          exact intervalIntegral.integral_of_le (f := fun t : ℝ ↦ (t * log t)⁻¹) hx
        _ = log (log x) - log (log 2) := by
          simpa using integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx)
    have hUnion :
        ∫ t in Ioi (2 : ℝ), prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          (∫ t in Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
            ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      simpa [Ioc_union_Ioi_eq_Ioi hx, add_assoc] using
        (setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
          (integrable_on_prime_log_div_sum_error.mono_set
            (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self))
          (integrable_on_prime_log_div_sum_error.mono_set <| by
            intro y hy
            exact hx.trans hy.le) :
          ∫ t in Set.Ioc (2 : ℝ) x ∪ Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
            (∫ t in Set.Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
              ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
    rw [mul_inv_cancel₀ (Real.log_pos (one_lt_two.trans_le hx)).ne', hEq,
      integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Icc_subset_Ici_self),
      hInvIcc, hInv, hErrIcc, hErrTail, hUnion]
    ring_nf

lemma prime_reciprocal_error :
  Asymptotics.IsBigO atTop (fun x ↦ prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (fun x ↦ (log x)⁻¹) := by
  simp only [div_eq_mul_inv]
  refine Asymptotics.IsBigO.sub ?_ ?_
  · refine (is_O_prime_log_div_sum_error.mul (isBigO_refl _ _)).trans ?_
    simpa using isBigO_refl (fun x : ℝ ↦ (log x)⁻¹) atTop
  · obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
    obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
      (atTop_basis' 2).mem_iff.1 hc
    have hbound :
        ∀ y, k ≤ y → ∀ᵐ x : ℝ ∂volume.restrict (Ici y),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ c * (x * log x ^ 2)⁻¹ := by
      intro y hy
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ (hy.trans hx)) (norm_nonneg _)).trans ?_
      rw [norm_eq_abs, abs_one, mul_one, norm_eq_abs, abs_inv, abs_mul, abs_sq, abs_of_nonneg]
      exact zero_le_two.trans (hk₂.trans (hy.trans hx))
    have hI :
        Asymptotics.IsBigO atTop
          (fun y ↦ ∫ x in Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop k] with y hy
      apply (norm_integral_le_integral_norm _).trans
      rw [norm_eq_abs, one_mul]
      refine le_trans ?_ (le_abs_self _)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        ?_ (hbound _ hy)
      have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici y) := by
        refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
        exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy))
      exact hbase.const_mul c
    have hEq :
        (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) =ᶠ[atTop] fun y ↦ c * (log y)⁻¹ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_my_func_Ioi hy]
    exact hI.trans_eventuallyEq hEq |>.trans (Asymptotics.isBigO_const_mul_self c _ _)

def meissel_mertens : ℝ := by
  exact 1 - log (Real.log 2) + prime_reciprocal_integral

lemma prime_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens))
    (fun x ↦ (log x)⁻¹) := by
  refine prime_reciprocal_error.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [prime_summatory_one_eq_prime_summatory_two, meissel_mertens, ← prime_reciprocal_eq hx]

lemma is_o_log_inv_one {c : ℝ} (hc : c ≠ 0) :
    Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x)⁻¹) (fun _ : ℝ ↦ (c : ℝ)) := by
  exact (Asymptotics.IsLittleO.inv_rev (is_o_one_log c⁻¹) (by simp [hc])).congr_right (by simp)

lemma is_o_const_log_log (c : ℝ) :
    Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ (c : ℝ)) (fun x : ℝ ↦ log (log x)) := by
  exact is_o_const_of_tendsto_at_top _ _ (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop) _

lemma prime_reciprocal_upper :
  Asymptotics.IsBigO atTop (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x)
    (fun x ↦ log (log x)) := by
  refine ((prime_reciprocal.trans
      ((is_o_log_inv_one one_ne_zero).trans (is_o_const_log_log _)).isBigO).add
      ((isBigO_refl _ _).add_isLittleO (is_o_const_log_log meissel_mertens))).congr_left ?_
  intro x
  ring

lemma mul_add_one_inv (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x + 1 ≠ 0) :
  (x * (x + 1))⁻¹ = x⁻¹ - (x + 1)⁻¹ := by
  field_simp [hx₀, hx₁]
  ring

lemma sum_thing_has_sum (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k + 1) * (n + k + 2) : ℝ)⁻¹) ((k + 1 : ℝ)⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => inv_nonneg.2 (by positivity))]
  have htel :
      ∀ i : ℕ,
        ((i + k + 1 : ℝ) * (i + k + 2))⁻¹ =
          (↑(i + (k + 1)) : ℝ)⁻¹ - (↑(i + 1 + (k + 1)) : ℝ)⁻¹ := by
    intro i
    simp only [Nat.cast_add_one, Nat.cast_add, add_right_comm (i : ℝ) 1, ← add_assoc]
    convert mul_add_one_inv (i + k + 1) ?_ ?_ using 2
    · norm_num [add_assoc]
    · exact_mod_cast Nat.succ_ne_zero (i + k)
    · exact_mod_cast Nat.succ_ne_zero (i + k + 1)
  simp only [htel, Finset.sum_range_sub', zero_add, Nat.cast_add_one]
  simpa using
    (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat (k + 1))).const_sub
      ((k + 1 : ℝ)⁻¹)

lemma sum_thing'_has_sum : HasSum (fun n : ℕ ↦ ((n - 1) * n : ℝ)⁻¹) 1 := by
  refine (hasSum_nat_add_iff' 2).1 ?_
  convert sum_thing_has_sum 0 using 1
  · ext n
    norm_num [add_sub_assoc]
  · simp [Finset.sum_range_succ]

lemma sum_thing'''_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum (fun n : ℕ ↦ ((n + k) * (n + k + 1) : ℝ)⁻¹) ((k : ℝ)⁻¹) := by
  convert sum_thing_has_sum (k - 1) using 1
  · ext n
    rw [add_assoc, add_assoc, Nat.cast_sub hk, Nat.cast_one, sub_add_cancel, add_sub, sub_add]
    norm_num [add_assoc]
  · simp [hk]

lemma sum_thing''_indicator_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum ({n | k < n}.indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹)) ((k : ℝ)⁻¹) := by
  have hrange : Set.range (fun i : ℕ => i + (k + 1)) = {n | k < n} := by
    ext n
    constructor
    · rintro ⟨i, rfl⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_left (k + 1) i)
    · intro hn
      refine ⟨n - (k + 1), Nat.sub_add_cancel ?_⟩
      exact Nat.succ_le_of_lt hn
  rw [← hrange]
  have hinj : Function.Injective (fun i : ℕ => i + (k + 1)) := by
    intro a b h
    exact Nat.add_right_cancel h
  apply (Function.Injective.hasSum_iff hinj ?_).1
  · convert sum_thing'''_has_sum hk using 1
    ext n
    simp [Set.indicator_of_mem, ← add_assoc]
  · intro n hn
    simp [Set.indicator_of_notMem, hn]

lemma prime_sum_thing_summable' (s : Set ℕ) :
  Summable (s.indicator (({n : ℕ | Nat.Prime n}).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) := by
  exact (sum_thing'_has_sum.summable.indicator _).indicator _

lemma indicator_mono {α β : Type*} [Zero β] [Preorder β] {s t : Set α} {f : α → β}
    (h : s ⊆ t) (hf : ∀ x, x ∉ s → x ∈ t → 0 ≤ f x) :
  indicator s f ≤ indicator t f := by
  intro x
  by_cases hs : x ∈ s
  · simp [Set.indicator_of_mem, hs, h hs]
  · by_cases ht : x ∈ t
    · simp [Set.indicator_of_notMem, hs, ht, hf x hs ht]
    · simp [Set.indicator_of_notMem, hs, ht]

lemma prime_sum_thing {k : ℕ} (hk : 1 ≤ k) :
  tsum
      ({n | k < n}.indicator (({n : ℕ | Nat.Prime n}).indicator (fun n ↦ ((n - 1) * n : ℝ)⁻¹))) ≤
    ((k : ℝ)⁻¹) := by
  refine hasSum_le ?_ (prime_sum_thing_summable' _).hasSum (sum_thing''_indicator_has_sum hk)
  intro n
  by_cases hkn : k < n
  · by_cases hpn : Nat.Prime n
    · simp [Set.indicator_of_mem, hkn, hpn]
    · have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (lt_of_le_of_lt hk hkn)
      have hnonneg : 0 ≤ (n : ℝ)⁻¹ * ((n : ℝ) - 1)⁻¹ := by
        apply mul_nonneg
        · positivity
        · exact inv_nonneg.2 (sub_nonneg.mpr hn1.le)
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hkn, hpn, hnonneg]
  · simp [Set.indicator_of_notMem, hkn]

lemma my_mul_thing' : ∀ {n : ℕ}, (0 : ℝ) ≤ (((n - 1) * n : ℝ)⁻¹) := by
  intro n
  exact inv_nonneg.2 my_mul_thing

lemma is_O_partial_of_bound {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ range (⌊x⌋₊ + 1), f i - c)
    (fun x ↦ x⁻¹) := by
  have hf'' : Summable f := (sum_thing'_has_sum.summable).of_nonneg_of_le hf' hf
  refine ⟨tsum f, (Asymptotics.IsBigO.of_bound 2 ?_).symm⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ ⌊x⌋₊ := by
    rwa [Nat.le_floor_iff' one_ne_zero, Nat.cast_one]
  have hx'' : (1 : ℝ) ≤ ⌊x⌋₊ := by simpa
  rw [← Summable.sum_add_tsum_nat_add _ hf'', add_tsub_cancel_left, norm_inv,
    norm_of_nonneg (tsum_nonneg fun i ↦ hf' (i + _)), norm_of_nonneg (zero_le_one.trans hx)]
  transitivity (⌊x⌋₊ : ℝ)⁻¹
  · refine hasSum_le (fun n ↦ ?_) ((summable_nat_add_iff _).2 hf'').hasSum
      (sum_thing'''_has_sum hx')
    have hsub : (↑n : ℝ) + (↑⌊x⌋₊ + 1) - 1 = ↑n + ↑⌊x⌋₊ := by ring
    simpa [Nat.cast_add, Nat.cast_add_one, add_assoc, add_left_comm, add_comm, mul_comm,
      mul_left_comm, mul_assoc, hsub] using hf (n + (⌊x⌋₊ + 1))
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := zero_lt_one.trans_le hx''
  field_simp [hxpos.ne', hfloorpos.ne']
  nlinarith [Nat.lt_floor_add_one x]

lemma is_O_partial_of_bound' {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ Icc 1 ⌊x⌋₊, f i - c)
    (fun x ↦ x⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_partial_of_bound hf hf'
  refine ⟨c, hc.congr_left ?_⟩
  intro x
  have hIco : Finset.Ico 0 (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    simpa using (Finset.Ico_succ_right_eq_Icc 0 ⌊x⌋₊)
  rw [Finset.range_eq_Ico, hIco, Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · have h0 : f 0 = 0 := ((hf' 0).antisymm (by simpa using hf 0)).symm
    simp [h0]
  · simp

lemma intermediate_bound :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ x⁻¹) := by
  simp only [prime_summatory, Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · rfl
    · exact my_mul_thing'
  · split_ifs with h
    · exact my_mul_thing'
    · simp

lemma prime_proper_powers {x : ℝ} {f : ℕ → ℝ} :
  (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f q) - prime_summatory f 1 x =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 2 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  rw [exact_sum_prime_powers, prime_summatory, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  have hk : 1 ≤ ⌊log x / Real.log p⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  rw [Finset.Icc_eq_insert_Icc_succ hk, Finset.sum_insert, pow_one, add_comm]
  · rw [Finset.mem_Icc]
    norm_num

lemma is_O_reciprocal_difference_aux {x : ℝ} :
  |(∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
      prime_summatory (fun p ↦ (((p - 1) * p : ℝ)⁻¹)) 1 x| ≤
    ∑ _p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) := by
  rw [prime_proper_powers, prime_summatory, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by simpa using hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  let N : ℕ := ⌊log x / Real.log p⌋₊
  have hk : 1 ≤ N := by
    dsimp [N]
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  have hgeom :
      ∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹ =
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) := by
    simpa [← Finset.Ico_succ_right_eq_Icc, inv_pow] using
      (geom_sum_Ico' (x := (p : ℝ)⁻¹)
        (by simpa using (inv_ne_one.mpr hp1.ne'))
        (Nat.succ_le_succ hk))
  have hdiff :
      |(∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹) - (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    rw [hgeom]
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) -
            (((p - 1) * p : ℝ)⁻¹) =
          -(((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1)) := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      have haux : (p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N = p := by
        rw [inv_pow]
        field_simp [hp0'.ne', pow_ne_zero N hp0'.ne']
      have hrewrite :
          (1 - (p : ℝ) ^ 2 * (1 / (p : ℝ)) ^ (N + 1) - 1) * (p : ℝ) ^ N =
            -((p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N) := by
        ring_nf
      rw [hrewrite, haux]
    rw [hstep, abs_neg, abs_of_nonneg]
    exact div_nonneg (inv_nonneg.2 (pow_nonneg hp0'.le _)) (sub_nonneg.2 hp1.le)
  have hdiff' :
      |(∑ k ∈ Finset.Icc 2 ⌊log x / Real.log p⌋₊, (↑(p ^ k) : ℝ)⁻¹) -
          (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    simpa [N, Nat.cast_pow] using hdiff
  rw [hdiff']
  have hratio :
      ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) ≤ 2 * ((p : ℝ) ^ (N + 1))⁻¹ := by
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) =
          ((p : ℝ) / ((p : ℝ) - 1)) * ((p : ℝ) ^ (N + 1))⁻¹ := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      ring_nf
    rw [hstep]
    have hp_ratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
      have hp_sub : 0 < (p : ℝ) - 1 := sub_pos_of_lt hp1
      rw [div_le_iff₀ hp_sub]
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      nlinarith
    exact mul_le_mul_of_nonneg_right hp_ratio (inv_nonneg.2 (pow_nonneg hp0'.le _))
  have hxp : x < (p : ℝ) ^ (N + 1) := by
    have hlogb : Real.logb p x < (N + 1 : ℝ) := by
      dsimp [N]
      simpa [Real.log_div_log] using Nat.lt_floor_add_one (log x / Real.log p)
    have hxpow : x < (p : ℝ) ^ ((N + 1 : ℕ) : ℝ) := by
      convert (Real.logb_lt_iff_lt_rpow hp1 hx).1 hlogb using 1
      norm_num
    rwa [Real.rpow_natCast] at hxpow
  have hinv : ((p : ℝ) ^ (N + 1))⁻¹ ≤ x⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hx hxp.le)
  exact hratio.trans (mul_le_mul_of_nonneg_left hinv (by positivity))

lemma is_O_reciprocal_difference : ∃ c,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
        prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := intermediate_bound
  refine ⟨c, ?_⟩
  have hc' : Asymptotics.IsBigO atTop
      (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
      (fun x ↦ (log x)⁻¹) := by
    refine hc.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine Asymptotics.IsBigO.triangle ?_ hc'
  have haux0 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ) * x⁻¹)
      (fun x ↦ (log x)⁻¹) := by
    refine (is_O_prime_counting_div_log.mul (isBigO_refl _ _)).congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hx.ne', one_mul]
  have haux : Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ))
      (fun x ↦ (log x)⁻¹) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (haux0.const_mul_left 2)
  have hbound :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦
          (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
            prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
            prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x)
        (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [one_mul, norm_eq_abs, norm_eq_abs]
    have hcard :
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
          (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
      have hcard' :
          ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := by
        rw [Finset.sum_const, prime_counting_eq_card_primes]
      calc
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := hcard'
        _ = (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
          exact nsmul_eq_mul (π ⌊x⌋₊) (2 * x⁻¹)
    exact (is_O_reciprocal_difference_aux).trans (le_trans (le_of_eq hcard) (le_abs_self _))
  exact hbound.trans haux

lemma prime_power_reciprocal : ∃ b,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) - (log (log x) + b))
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_reciprocal_difference
  refine ⟨meissel_mertens + c, ?_⟩
  exact (hc.add prime_reciprocal).congr_left fun x ↦ by ring_nf

lemma summable_indicator_iff_subtype {α β : Type*} [TopologicalSpace α] [AddCommMonoid α]
  {s : Set β} (f : β → α) :
  Summable (f ∘ Subtype.val : s → α) ↔ Summable (s.indicator f) := by
  simpa [Function.comp_def] using (summable_subtype_iff_indicator (s := s) (f := f))

lemma is_unit_of_is_unit_pow {α : Type*} [CommMonoid α] {a : α} :
  ∀ n, n ≠ 0 → (IsUnit (a ^ n) ↔ IsUnit a) := by
  intro n
  induction n with
  | zero =>
      intro h
      exact (h rfl).elim
  | succ n ih =>
      cases n with
      | zero =>
          intro _
          simp
      | succ n =>
          intro _
          rw [pow_succ, IsUnit.mul_iff, ih (Nat.succ_ne_zero _), and_self]

lemma is_prime_pow_and_not_prime_iff {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (x : α) :
  IsPrimePow x ∧ ¬ Prime x ↔ (∃ p k, Prime p ∧ 1 < k ∧ p ^ k = x) := by
  constructor
  · rintro ⟨⟨p, k, hp, hk, rfl⟩, hx⟩
    refine ⟨p, k, hp, ?_, rfl⟩
    rw [← Nat.succ_le_iff] at hk
    exact lt_of_le_of_ne hk fun h => hx (h ▸ by simpa using hp)
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hk0 : k ≠ 0 := by omega
    refine ⟨IsPrimePow.pow hp.isPrimePow hk0, fun hx => ?_⟩
    have hpow : p ^ k = p * p ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_add]
      simp [pow_one, mul_comm]
    have hu : IsUnit (p ^ (k - 1)) :=
      (hx.irreducible.isUnit_or_isUnit hpow).resolve_left hp.not_isUnit
    exact hp.not_isUnit <| (is_unit_of_is_unit_pow (a := p) (k - 1) (by omega)).mp hu

lemma log_one_sub_recip {p : ℕ} (hp : 1 < p) :
  |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ (((p - 1) * p : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hpInv : |(p : ℝ)⁻¹| < 1 := by
    simpa [abs_of_nonneg hp0.le] using (one_div_lt_one_div hp0 zero_lt_one).2 hp1
  have h := Real.abs_log_sub_add_sum_range_le hpInv 1
  have h' :
      |(p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)| ≤ |(p : ℝ)⁻¹| ^ (1 + 1) / (1 - |(p : ℝ)⁻¹|) := by
    simpa [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, div_one, pow_one]
      using h
  have hrew : |(p : ℝ)⁻¹| ^ (1 + 1) / (1 - |(p : ℝ)⁻¹|) = (((p - 1) * p : ℝ)⁻¹) := by
    rw [abs_inv, abs_of_nonneg hp0.le, pow_two, div_eq_mul_inv]
    field_simp [hp0.ne']
  exact h'.trans_eq hrew

lemma my_func_neg {p : ℕ} (hp : 1 < p) : (p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹) ≤ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hsub : 0 < 1 - (p : ℝ)⁻¹ := by
    exact sub_pos_of_lt <| by simpa [one_div] using (one_div_lt_one_div hp0 zero_lt_one).2 hp1
  linarith [log_le_sub_one_of_pos hsub]

lemma mertens_third_log_error :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c)
    (fun x : ℝ ↦ x⁻¹) := by
  simp only [Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · exact neg_le_of_neg_le (neg_le_of_abs_le (log_one_sub_recip h.one_lt))
    · exact my_mul_thing'
  · split_ifs with h
    · rw [neg_nonneg]
      exact my_func_neg h.one_lt
    · rfl

lemma mertens_third_log :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        log (1 - (p : ℝ)⁻¹)⁻¹ - (log (log x) + c))
    (fun x : ℝ ↦ (log x)⁻¹) := by
  obtain ⟨c₂, hc₂⟩ := mertens_third_log_error
  have hc₂' : Asymptotics.IsBigO atTop
      (fun x : ℝ ↦
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          -((p : ℝ)⁻¹ + log (1 - (p : ℝ)⁻¹)) - c₂)
      (fun x ↦ (log x)⁻¹) := by
    refine hc₂.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine ⟨c₂ + meissel_mertens, (prime_reciprocal.add hc₂').congr_left ?_⟩
  intro x
  simp only [Real.log_inv, Finset.sum_neg_distrib, Finset.sum_add_distrib, neg_add,
    prime_summatory]
  ring

lemma partial_euler_trivial_upper_bound {n : ℕ} : partial_euler_product n ≤ 2 ^ π n := by
  rw [partial_euler_product, prime_counting_eq_card_primes, ← Finset.prod_const]
  have hpos : ∀ i : ℕ, i.Prime → 0 < (1 - (i : ℝ)⁻¹) := fun i hi =>
    sub_pos_of_lt <| by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.pos
      simpa using (one_div_lt_one_div hi0 zero_lt_one).2 (by exact_mod_cast hi.one_lt)
  refine Finset.prod_le_prod₀ (fun i hi => (inv_pos.2 (hpos i (Finset.mem_filter.mp hi).2)).le)
    (fun i hi => ?_)
  rcases Finset.mem_filter.mp hi with ⟨_, hip⟩
  have hip0 : (0 : ℝ) < i := by exact_mod_cast hip.pos
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (i : ℝ)⁻¹ := by
    field_simp [hip0.ne']
    nlinarith [show (2 : ℝ) ≤ i by exact_mod_cast hip.two_le]
  have hinv : (1 - (i : ℝ)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (hpos _ hip) (by positivity)]
    exact hhalf
  norm_num at hinv ⊢
  exact hinv

lemma mertens_third :
  ∃ c, 0 < c ∧
    Asymptotics.IsBigO atTop (fun x ↦ partial_euler_product ⌊x⌋₊ - c * Real.log x)
      (fun _ ↦ (1 : ℝ)) := by
  obtain ⟨c, hc⟩ := mertens_third_log
  obtain ⟨k, hk₀, hk⟩ := hc.exists_pos
  refine ⟨Real.exp c, Real.exp_pos _, Asymptotics.IsBigO.of_bound (2 * (k * Real.exp c)) ?_⟩
  filter_upwards [hk.bound, Real.tendsto_log_atTop.eventually (eventually_ge_atTop k)] with x hx hx'
  have hk' : k * (Real.log x)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (hk₀.trans_le hx')]
    simpa using hx'
  rw [norm_eq_abs, norm_inv, Real.norm_of_nonneg (hk₀.le.trans hx')] at hx
  have i := (Real.abs_exp_sub_one_le (hx.trans hk')).trans
    (mul_le_mul_of_nonneg_left hx zero_le_two)
  have hx'' : 0 < Real.log x := hk₀.trans_le hx'
  have hx''' : 0 < Real.exp c * Real.log x := mul_pos (Real.exp_pos _) hx''
  have hp : ∀ p, p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime → 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact inv_pos.2 (sub_pos_of_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.2.one_lt)))
  rw [Real.exp_sub, Real.exp_add, Real.exp_log hx'', ← Real.log_prod (fun p h ↦ (hp p h).ne'),
    Real.exp_log (Finset.prod_pos hp), mul_comm, div_sub_one hx'''.ne', abs_div,
    abs_of_nonneg hx'''.le, div_le_iff₀ hx''', mul_assoc, mul_mul_mul_comm,
    inv_mul_cancel₀ hx''.ne', mul_one] at i
  simpa [partial_euler_product, norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using i

lemma weak_mertens_third_upper :
    Asymptotics.IsBigO atTop (fun x ↦ partial_euler_product ⌊x⌋₊) log := by
  let ⟨c, _, hc⟩ := mertens_third
  exact ((hc.trans (is_o_one_log 1).isBigO).add
    (Asymptotics.isBigO_const_mul_self c _ _)).congr_left (by simp)

lemma weak_mertens_third_lower :
    Asymptotics.IsBigO atTop log (fun x ↦ partial_euler_product ⌊x⌋₊) := by
  obtain ⟨c, hc₀, hc⟩ := mertens_third
  have h := Asymptotics.isBigO_self_const_mul hc₀.ne' log atTop
  have h' := hc.trans_isLittleO ((is_o_one_log 1).trans_isBigO h)
  exact (h.trans h'.right_isBigO_add).congr_right (by simp)

lemma weak_mertens_third_upper_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 2 ≤ x → ‖partial_euler_product (⌊x⌋₊)‖ ≤ c * ‖log x‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_upper.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  refine ⟨max c (2 ^ c₁ / Real.log 2), lt_max_of_lt_left hc₀, fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
    norm_of_nonneg (Real.log_nonneg (one_le_two.trans hx))]
  have hpow : (2 : ℝ) ^ π ⌊x⌋₊ ≤ 2 ^ c₁ := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have hpi : (π ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℕ) := by
      exact_mod_cast (prime_counting_le_self ⌊x⌋₊)
    exact le_trans hpi ((Nat.floor_le (zero_le_two.trans hx)).trans h)
  have hupper : 2 ^ c₁ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
    calc
      2 ^ c₁ = (2 ^ c₁ / Real.log 2) * Real.log 2 := by
        field_simp [(Real.log_pos one_lt_two).ne']
      _ ≤ max c (2 ^ c₁ / Real.log 2) * Real.log x := by
        refine mul_le_mul (le_max_right _ _) (Real.log_le_log zero_lt_two hx)
          (Real.log_nonneg one_le_two) ?_
        exact le_trans (by positivity : 0 ≤ 2 ^ c₁ / Real.log 2) (le_max_right _ _)
  exact (partial_euler_trivial_upper_bound.trans hpow).trans hupper

lemma weak_mertens_third_lower_all :
  ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 1 ≤ x → c * ‖log x‖ ≤ ‖partial_euler_product (⌊x⌋₊)‖ := by
  obtain ⟨c, hc₀, hc⟩ := weak_mertens_third_lower.exists_pos
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc
  obtain ⟨c₁, hc₁⟩ := hc
  let c' := max c (Real.log c₁)
  have hc' : 0 < c' := lt_max_of_lt_left hc₀
  refine ⟨c'⁻¹, inv_pos.2 hc', fun x hx ↦ ?_⟩
  rcases le_total c₁ x with h | h
  · rw [inv_mul_le_iff₀ hc']
    exact (hc₁ _ h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_of_nonneg (Real.log_nonneg hx),
    norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound)]
  have hlog : Real.log x ≤ c' := by
    exact le_trans (Real.log_le_log (zero_lt_one.trans_le hx) h) (le_max_right _ _)
  have hone : c'⁻¹ * Real.log x ≤ 1 := by
    rw [inv_mul_le_iff₀ hc', mul_one]
    exact hlog
  exact hone.trans (partial_euler_trivial_lower_bound (n := ⌊x⌋₊))

lemma two_pow_card_distinct_divisors_le_divisor_count {n : ℕ} (hn : n ≠ 0) :
  2 ^ ω n ≤ ArithmeticFunction.sigma 0 n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.pow_card_le_prod _ _ _ ?_
  intro p hp
  have hp0 : 0 < n.factorization p :=
    Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  omega

lemma mul_eq_mul_iff {a b c d : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b ≤ d) :
  a * b = c * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    rcases hac.eq_or_lt with rfl | hac'
    · exact ⟨rfl, Nat.mul_left_cancel ha (show a * b = a * d by simpa using h)⟩
    rcases hbd.eq_or_lt with rfl | hbd'
    · exact ⟨Nat.mul_right_cancel hb (show a * b = c * b by simpa using h), rfl⟩
    exact False.elim <| (mul_lt_mul'' hac' hbd' ha.le hb.le).ne h
  · rintro ⟨rfl, rfl⟩
    rfl

lemma divisor_count_eq_pow_iff_squarefree {n : ℕ} :
  ArithmeticFunction.sigma 0 n = 2 ^ ω n ↔ Squarefree n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors,
    divisor_function_exact hn, Finsupp.prod, Nat.support_factorization, ← Finset.prod_const,
    Nat.squarefree_iff_factorization_le_one hn, eq_comm]
  rw [Finset.prod_eq_prod_iff_of_le']
  · constructor
    · intro h p
      by_cases hp : p ∈ n.factorization.support
      · have hpEq : 2 = n.factorization p + 1 := h p hp
        omega
      · rw [Finsupp.notMem_support_iff.mp hp]
        exact Nat.zero_le 1
    · intro h p hp
      have hp0 : 0 < n.factorization p :=
        Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hp1 : n.factorization p ≤ 1 := h p
      omega
  · intro _ _
    exact zero_lt_two
  · intro p hp
    have hp0 : 0 < n.factorization p :=
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    omega

lemma tendsto_primorial_at_top :
  Tendsto primorial atTop atTop := by
  apply primorial_monotone.tendsto_atTop_atTop
  intro a
  obtain ⟨p, hp₁, hp₂⟩ := Nat.exists_infinite_primes a
  refine ⟨p, hp₁.trans ?_⟩
  exact Nat.le_of_dvd (primorial_pos _) hp₂.dvd_primorial

lemma primorial_three : primorial 3 = 6 := by
  decide

lemma two_le_primorial {n : ℕ} (hn : 2 ≤ n) : 2 ≤ primorial n := by
  rw [← primorial_two]
  exact primorial_monotone hn

lemma squarefree_prime_prod {ι : Type*} {s : Finset ι} (f : ι → ℕ)
    (hs : ∀ i ∈ s, (f i).Prime) (hf : Set.InjOn f (s : Set ι)) :
  Squarefree (s.prod f) := by
  classical
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp <|
      (Nat.coprime_primes (hs i hi) (hs j hj)).2 fun hEq => hij (hf hi hj hEq)
  · intro i hi
    exact (hs i hi).squarefree

lemma divisor_lower_bound_aux (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ n : ℕ in atTop,
      1 / log (log (n : ℝ)) * (1 - ε) ≤ 1 / (log (log (n : ℝ)) - c) := by
  suffices hmain :
      ∀ᶠ x : ℝ in atTop, 1 / x * (1 - ε) ≤ 1 / (x - c) by
    exact ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually hmain
  filter_upwards [eventually_ge_atTop (c + -c / ε), eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop c] with x hx hx' hx''
  have hx0 : 0 < x - c := sub_pos_of_lt hx''
  have haux : ε * c - c ≤ ε * x := by
    have := mul_le_mul_of_nonneg_left hx hε.le
    simpa [sub_eq_add_neg, mul_add, mul_div_cancel₀ _ hε.ne'] using this
  have hmul : (1 - ε) * (x - c) ≤ x := by
    nlinarith
  have hmid : 1 - ε ≤ x / (x - c) := (le_div_iff₀ hx0).2 hmul
  have hleft : 1 / x * (1 - ε) = (1 - ε) / x := by ring
  rw [hleft]
  exact (div_le_iff₀ hx').2 <| by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmid

lemma factors_primorial {n : ℕ} :
  (primorial n).primeFactorsList = (List.range (n + 1)).filter Nat.Prime := by
  have hrange : (List.range (n + 1)).Nodup := by
    simpa using (List.nodup_range : (List.range (n + 1)).Nodup)
  have hnodup : ((List.range (n + 1)).filter Nat.Prime).Nodup := hrange.filter _
  have htf :
      ((List.range (n + 1)).filter Nat.Prime).toFinset =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext x
    simp
  have hprod : ((List.range (n + 1)).filter Nat.Prime).prod = primorial n := by
    calc
      ((List.range (n + 1)).filter Nat.Prime).prod
          = ((List.range (n + 1)).filter Nat.Prime).toFinset.prod id := by
              simpa using (List.prod_toFinset id hnodup).symm
      _ = primorial n := by
            rw [htf, primorial]
            rfl
  refine
    ((Nat.primeFactorsList_unique hprod (fun p hp => by
        simpa using (List.mem_filter.mp hp).2)).eq_of_pairwise' ?_
      (Nat.primeFactorsList_sorted _).pairwise).symm
  have hpair : List.Pairwise (fun a b : ℕ => a ≤ b) (List.range (n + 1)) := by
    simpa using (List.sortedLT_range (n + 1)).pairwise.imp (@Nat.le_of_lt)
  exact hpair.sublist List.filter_sublist

@[simp] lemma to_finset_filter
  {α : Type*} {l : List α} (p : α → Prop) [DecidableEq α] [DecidablePred p] :
  (l.filter p).toFinset = l.toFinset.filter p := by
  ext x
  simp

@[simp] lemma to_finset_range {n : ℕ} : (List.range n).toFinset = Finset.range n := by
  simpa using List.toFinset_range n

lemma factors_to_finset_primorial {n : ℕ} :
  (primorial n).primeFactorsList.toFinset = (Finset.range (n + 1)).filter Nat.Prime := by
  rw [factors_primorial]
  simp

lemma card_distinct_factors_primorial {n : ℕ} : ω (primorial n) = π n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    factors_to_finset_primorial, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

lemma card_factors_primorial {n : ℕ} : Ω (primorial n) = π n := by
  rw [← card_distinct_factors_primorial, eq_comm,
    ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree (primorial_pos _).ne']
  exact squarefree_primorial _

lemma le_log_sigma_zero_primorial :
  ∃ c : ℝ, ∀ p, 2 ≤ p →
    (log (primorial p : ℝ) * Real.log 2) / (log (log (primorial p : ℝ)) - c) ≤
      Real.log (ArithmeticFunction.sigma 0 (primorial p)) := by
  obtain ⟨c, hc₀, hc⟩ := chebyshev_first_all
  refine ⟨Real.log c, ?_⟩
  intro p hp
  have hp₁ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₂ : 0 < (p : ℝ) := zero_lt_two.trans_le hp₁
  have hp₃ : 0 < chebyshev_first p := chebyshev_first_pos hp₁
  have htheta : log (primorial p : ℝ) = chebyshev_first p := by
    simpa [chebyshev_first] using (Chebyshev.theta_eq_log_primorial (p : ℝ)).symm
  have hpow : ((2 : ℝ) ^ ω (primorial p)) = (2 : ℝ) ^ ((ω (primorial p) : ℝ)) := by
    rw [← Real.rpow_natCast]
  rw [divisor_count_eq_pow_iff_squarefree.2 (squarefree_primorial _), Nat.cast_pow, Nat.cast_two,
    hpow, Real.log_rpow (by positivity), card_distinct_factors_primorial, htheta]
  have h₁ : chebyshev_first p ≤ π p * log (p : ℝ) := by
    simpa using chebyshev_first_trivial_bound (p : ℝ)
  have hcp : c * (p : ℝ) ≤ chebyshev_first p := by
    simpa [Real.norm_of_nonneg hp₂.le, Real.norm_of_nonneg hp₃.le] using hc (p : ℝ) hp₁
  have h₂ : log (p : ℝ) ≤ log (chebyshev_first p) - Real.log c := by
    have hlog := log_le_log_of_le (mul_pos hc₀ hp₂) hcp
    rw [Real.log_mul hc₀.ne' hp₂.ne'] at hlog
    linarith
  have h₃ : 0 < log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hp)
  have h₄ : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg one_le_two
  have h₅ : (0 : ℝ) ≤ π p := Nat.cast_nonneg (π p)
  have hden : 0 < log (chebyshev_first p) - Real.log c := by
    linarith
  refine (div_le_iff₀ hden).2 ?_
  calc
    chebyshev_first p * Real.log 2 ≤ (π p * log (p : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h₁ h₄
    _ ≤ (π p * (log (chebyshev_first p) - Real.log c)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ h₅) h₄
    _ = π p * Real.log 2 * (log (chebyshev_first p) - Real.log c) := by ring

lemma one_le_sigma {k n : ℕ} (hn : n ≠ 0) : 1 ≤ ArithmeticFunction.sigma k n := by
  simpa [ArithmeticFunction.sigma_apply] using
    (Finset.single_le_sum
      (f := fun d : ℕ ↦ d ^ k)
      (fun d _ => Nat.zero_le _)
      (by simp [hn] : 1 ∈ n.divisors))

lemma divisor_lower_bound_log {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
  obtain ⟨c, hc⟩ := le_log_sigma_zero_primorial
  have hmain :
      ∃ᶠ n : ℕ in atTop,
        log (n : ℝ) * Real.log 2 / (log (log (n : ℝ)) - c) ≤
          log (ArithmeticFunction.sigma 0 n : ℝ) := by
    exact tendsto_primorial_at_top.frequently (eventually_atTop.2 ⟨2, hc⟩).frequently
  apply (hmain.and_eventually (divisor_lower_bound_aux c hε)).mp
  simp only [and_imp]
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁ hn₂
  apply hn₁.trans'
  rw [mul_div_assoc, mul_comm (log (n : ℝ))]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (Nat.one_le_cast.2 hn₀))
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hn₂ (Real.log_nonneg one_le_two)

lemma divisor_lower_bound {ε : ℝ} (hε : 0 < ε) :
  ∃ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε)) ≤
        ArithmeticFunction.sigma 0 n := by
  apply (divisor_lower_bound_log hε).mp
  filter_upwards [eventually_ge_atTop 1] with n hn₀ hn₁
  have hn₀' : 0 < n := hn₀
  have hn₀'' : (0 : ℝ) < n := by exact_mod_cast hn₀'
  have hsigma : (0 : ℝ) < ArithmeticFunction.sigma 0 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀'.ne'
  have hlog :
      log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 - ε))) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) := by
    simpa [Real.log_rpow hn₀''] using hn₁
  exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hn₀'' _) hsigma).1 hlog

lemma cobounded_of_frequently {α : Type*} [ConditionallyCompleteLattice α]
  {f : Filter α} (c : α) (hc : ∃ᶠ x in f, c ≤ x) :
  Filter.IsCobounded (· ≤ ·) f := by
  refine ⟨c, ?_⟩
  intro d hd
  obtain ⟨x, hxc, hxd⟩ := (hc.and_eventually hd).exists
  exact hxc.trans hxd

lemma Limsup_eq_of_eventually_of_frequently {f : Filter ℝ} (c : ℝ)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c + ε)
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c - ε ≤ x) :
  limsup id f = c := by
  have hb : f.IsBounded (· ≤ ·) := ⟨c + 1, upper 1 zero_lt_one⟩
  have hb' : f.IsBoundedUnder (· ≤ ·) id := by
    simpa [Filter.IsBoundedUnder]
      using hb
  have hc : f.IsCobounded (· ≤ ·) :=
    cobounded_of_frequently (c - 1) (by simpa using lower 1 zero_lt_one)
  have hc' : f.IsCoboundedUnder (· ≤ ·) id := by
    simpa [Filter.IsCoboundedUnder]
      using hc
  apply le_antisymm
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    simpa using (limsup_le_of_le (u := id) (f := f) (a := c + ε) hc' (upper ε hε))
  · rw [le_iff_forall_pos_le_add]
    intro ε hε
    rw [← sub_le_iff_le_add]
    simpa using (le_limsup_of_frequently_le (u := id) (f := f) (a := c - ε) (lower ε hε) hb')

lemma Limsup_eq_of_eventually_of_frequently_mul {f : Filter ℝ} {c : ℝ} (hc : 0 ≤ c)
  (upper : ∀ ε, 0 < ε → ∀ᶠ x : ℝ in f, x ≤ c * (1 + ε))
  (lower : ∀ ε, 0 < ε → ∃ᶠ x : ℝ in f, c * (1 - ε) ≤ x) :
  limsup id f = c := by
  rcases hc.eq_or_lt with rfl | hc'
  · refine Limsup_eq_of_eventually_of_frequently 0 (fun ε hε => ?_) (fun ε hε => ?_)
    · apply Filter.EventuallyLE.trans (upper 1 zero_lt_one)
        (Filter.Eventually.of_forall fun x => ?_)
      linarith [hε.le]
    · apply (lower 1 zero_lt_one).mono
      intro x hx
      linarith [hε.le]
  · apply Limsup_eq_of_eventually_of_frequently
    · intro ε hε
      refine (upper (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        x ≤ c * (1 + ε / c) := hx
        _ = c + ε := by
          field_simp [hc'.ne']
    · intro ε hε
      refine (lower (ε / c) (div_pos hε hc')).mono ?_
      intro x hx
      calc
        c - ε = c * (1 - ε / c) := by
          field_simp [hc'.ne']
        _ ≤ x := hx

lemma divisor_limsup :
  atTop.limsup
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)) =
    log (2 : ℝ) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have l := Real.tendsto_log_atTop
  refine Limsup_eq_of_eventually_of_frequently_mul
    (f := Filter.map
      (fun n : ℕ ↦
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ))
      atTop)
    (Real.log_nonneg one_le_two) ?_ ?_
  · intro ε hε
    change ∀ᶠ n : ℕ in atTop,
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ) ≤
        Real.log 2 * (1 + ε)
    filter_upwards [divisor_bound hε, eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    have hlog : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        log ((n : ℝ) ^ (Real.log 2 / log (log (n : ℝ)) * (1 + ε))) := by
      exact log_le_log_of_le (by exact_mod_cast ArithmeticFunction.sigma_pos 0 n hn₀.ne') hn
    have hlog' : log (ArithmeticFunction.sigma 0 n : ℝ) ≤
        (Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ) := by
      simpa [Real.log_rpow hn₁] using hlog
    refine (div_le_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hlog' hn₃.le
    have hEq :
        ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) * log (log (n : ℝ)) =
          Real.log 2 * (1 + ε) * log (n : ℝ) := by
      field_simp [hn₃.ne']
    calc
      log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ))
          ≤ ((Real.log 2 / log (log (n : ℝ)) * (1 + ε)) * log (n : ℝ)) *
              log (log (n : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = Real.log 2 * (1 + ε) * log (n : ℝ) := hEq
  · intro ε hε
    change ∃ᶠ n : ℕ in atTop,
      Real.log 2 * (1 - ε) ≤
        log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) / log (n : ℝ)
    refine (divisor_lower_bound_log hε).mp ?_
    filter_upwards [eventually_gt_atTop 0, h (eventually_gt_atTop 0),
      h <| l <| eventually_gt_atTop 0, h <| l <| l <| eventually_gt_atTop 0] with
      n hn₀ hn₁ hn₂ hn₃
    dsimp at hn₁ hn₂ hn₃
    intro hn
    refine (le_div_iff₀ hn₂).2 ?_
    have hmul := mul_le_mul_of_nonneg_right hn hn₃.le
    have hEq :
        Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := by
      field_simp [hn₃.ne']
    calc
      Real.log 2 * (1 - ε) * log (n : ℝ) =
          ((Real.log 2 / log (log (n : ℝ)) * (1 - ε)) * log (n : ℝ)) *
            log (log (n : ℝ)) := hEq
      _ ≤ log (ArithmeticFunction.sigma 0 n : ℝ) * log (log (n : ℝ)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

end

end Erdos319BackgroundBasicEstimates

-- END PINNED ANALYTIC BACKGROUND

set_option autoImplicit false

open Filter Finset
open scoped Topology

namespace Erdos319Formal

def reciprocalSum (A : Finset ℕ) : ℚ := ∑ n ∈ A, (n : ℚ)⁻¹

def signedSum (A : Finset ℕ) (δ : ℕ → ℤˣ) : ℚ :=
  ∑ n ∈ A, (δ n : ℚ) / n

def Primitive (A : Finset ℕ) : Prop :=
  ∃ δ : ℕ → ℤˣ, signedSum A δ = 0 ∧
    ∀ C ⊆ A, signedSum C δ = 0 → C = ∅ ∨ C = A

noncomputable def maxSize (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter Primitive).sup Finset.card

def FullAsymptotic : Prop :=
  Tendsto (fun N : ℕ => (maxSize N : ℝ) / N) atTop (𝓝 1)

def NearFullWitnesses : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Primitive A ∧
      (1 - ε) * N ≤ (A.card : ℝ)

def DIntegral (D : ℕ) (r : ℚ) : Prop := r.den.Coprime D

@[simp] theorem reciprocalSum_empty : reciprocalSum ∅ = 0 := by
  simp [reciprocalSum]

@[simp] theorem signedSum_empty (δ : ℕ → ℤˣ) : signedSum ∅ δ = 0 := by
  simp [signedSum]

theorem primitive_empty : Primitive ∅ := by
  refine ⟨fun _ => 1, by simp, ?_⟩
  intro C hC _
  exact Or.inl (Finset.subset_empty.mp hC)

theorem card_le_maxSize {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hP : Primitive A) : A.card ≤ maxSize N := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hP⟩)

theorem maxSize_le (N : ℕ) : maxSize N ≤ N := by
  classical
  apply Finset.sup_le
  intro A hA
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  simpa using Finset.card_le_card hsub

theorem reciprocalSum_pos {A : Finset ℕ}
    (hpos : ∀ n ∈ A, 0 < n) (hne : A.Nonempty) : 0 < reciprocalSum A := by
  apply Finset.sum_pos
  · intro n hn
    exact inv_pos.mpr (by exact_mod_cast hpos n hn)
  · exact hne

theorem reciprocalSum_eq_zero_iff {A : Finset ℕ}
    (hpos : ∀ n ∈ A, 0 < n) : reciprocalSum A = 0 ↔ A = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_gt (reciprocalSum_pos hpos (Finset.nonempty_iff_ne_empty.mpr hne))) h
  · rintro rfl
    simp

theorem dIntegral_add {D : ℕ} {r s : ℚ}
    (hr : DIntegral D r) (hs : DIntegral D s) : DIntegral D (r + s) := by
  exact Nat.Coprime.of_dvd_left (Rat.add_den_dvd r s) (Nat.Coprime.mul_left hr hs)

theorem dIntegral_reciprocal {D n : ℕ} (hn : n.Coprime D) :
    DIntegral D ((n : ℚ)⁻¹) := by
  by_cases hn0 : n = 0
  · simp [hn0, DIntegral]
  · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    simpa [DIntegral, Rat.den_inv_of_ne_zero hnq] using hn

theorem dIntegral_reciprocalSum {D : ℕ} {A : Finset ℕ}
    (hA : ∀ n ∈ A, n.Coprime D) : DIntegral D (reciprocalSum A) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [DIntegral]
  | @insert n A hn ih =>
      simp only [reciprocalSum, Finset.sum_insert hn]
      apply dIntegral_add
      · exact dIntegral_reciprocal (hA n (Finset.mem_insert_self n A))
      · exact ih (fun m hm => hA m (Finset.mem_insert_of_mem hm))

theorem reciprocalSum_eq_of_subset {A B : Finset ℕ} (hAB : A ⊆ B)
    (hpos : ∀ n ∈ B, 0 < n) (heq : reciprocalSum A = reciprocalSum B) : A = B := by
  have hdiff : reciprocalSum (B \ A) = 0 := by
    have hsum := Finset.sum_sdiff hAB (f := fun n : ℕ => (n : ℚ)⁻¹)
    change reciprocalSum (B \ A) + reciprocalSum A = reciprocalSum B at hsum
    linarith
  have hempty : B \ A = ∅ := (reciprocalSum_eq_zero_iff
    (fun n hn => hpos n (Finset.mem_sdiff.mp hn).1)).mp hdiff
  exact Finset.Subset.antisymm hAB (Finset.sdiff_eq_empty_iff_subset.mp hempty)

noncomputable def sideSigns (E : Finset ℕ) (n : ℕ) : ℤˣ := by
  classical
  exact if n ∈ E then 1 else -1

theorem subset_union_partition {C E F : Finset ℕ} (hC : C ⊆ E ∪ F) :
    C = (C ∩ E) ∪ (C ∩ F) := by
  ext n
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · intro hn
    rcases Finset.mem_union.mp (hC hn) with he | hf
    · exact Or.inl ⟨hn, he⟩
    · exact Or.inr ⟨hn, hf⟩
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn

theorem signedSum_split {C E F : Finset ℕ}
    (hC : C ⊆ E ∪ F) (hdis : Disjoint E F) :
    signedSum C (sideSigns E) = reciprocalSum (C ∩ E) - reciprocalSum (C ∩ F) := by
  classical
  have hd : Disjoint (C ∩ E) (C ∩ F) :=
    hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hp : signedSum (C ∩ E) (sideSigns E) = reciprocalSum (C ∩ E) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [sideSigns, (Finset.mem_inter.mp hn).2]
  have hn : signedSum (C ∩ F) (sideSigns E) = -reciprocalSum (C ∩ F) := by
    unfold signedSum reciprocalSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have he : n ∉ E := by
      intro he
      exact Finset.disjoint_left.mp hdis he (Finset.mem_inter.mp hn).2
    simp [sideSigns, he, div_eq_mul_inv]
  calc
    signedSum C (sideSigns E) =
        signedSum (C ∩ E) (sideSigns E) + signedSum (C ∩ F) (sideSigns E) := by
      unfold signedSum
      rw [← Finset.sum_union hd, ← subset_union_partition hC]
    _ = reciprocalSum (C ∩ E) - reciprocalSum (C ∩ F) := by rw [hp, hn, sub_eq_add_neg]

def MinimalCore (D : ℕ) (E : Finset ℕ) : Prop :=
  (∀ n ∈ E, 0 < n ∧ ¬n.Coprime D) ∧ DIntegral D (reciprocalSum E) ∧
    ∀ C ⊆ E, DIntegral D (reciprocalSum C) → C = ∅ ∨ C = E

theorem primitive_union_of_minimalCore {D : ℕ} {E F : Finset ℕ}
    (hcore : MinimalCore D E) (hFpos : ∀ n ∈ F, 0 < n)
    (hFcop : ∀ n ∈ F, n.Coprime D)
    (heq : reciprocalSum E = reciprocalSum F) : Primitive (E ∪ F) := by
  classical
  have hd : Disjoint E F := Finset.disjoint_left.mpr (fun n he hf => (hcore.1 n he).2 (hFcop n hf))
  have hiE : (E ∪ F) ∩ E = E := Finset.inter_eq_right.mpr Finset.subset_union_left
  have hiF : (E ∪ F) ∩ F = F := Finset.inter_eq_right.mpr Finset.subset_union_right
  refine ⟨sideSigns E, ?_, ?_⟩
  · rw [signedSum_split Finset.Subset.rfl hd, hiE, hiF, heq, sub_self]
  · intro C hC hzero
    have hsides : reciprocalSum (C ∩ E) = reciprocalSum (C ∩ F) := by
      exact sub_eq_zero.mp ((signedSum_split hC hd).symm.trans hzero)
    have hgood : DIntegral D (reciprocalSum (C ∩ E)) := by
      rw [hsides]
      exact dIntegral_reciprocalSum (fun n hn => hFcop n (Finset.mem_inter.mp hn).2)
    rcases hcore.2.2 (C ∩ E) Finset.inter_subset_right hgood with he | he
    · have hf : C ∩ F = ∅ := by
        apply (reciprocalSum_eq_zero_iff
          (fun n hn => hFpos n (Finset.mem_inter.mp hn).2)).mp
        rw [← hsides, he, reciprocalSum_empty]
      exact Or.inl (by rw [subset_union_partition hC, he, hf, Finset.empty_union])
    · have hf : C ∩ F = F := by
        apply reciprocalSum_eq_of_subset Finset.inter_subset_right hFpos
        rw [← hsides, he, heq]
      exact Or.inr (by rw [subset_union_partition hC, he, hf])

theorem maxSize_attained (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Primitive A ∧ A.card = maxSize N := by
  classical
  have hne : ((Finset.Icc 1 N).powerset.filter Primitive).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), primitive_empty⟩⟩
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨A, Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
    (Finset.mem_filter.mp hA).2, hcard.symm⟩

theorem fullAsymptotic_of_nearFullWitnesses (h : NearFullWitnesses) : FullAsymptotic := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [h ((1 - a) / 2) (by linarith), eventually_ge_atTop (1 : ℕ)] with N hN hNpos
    obtain ⟨A, hA, hP, hcard⟩ := hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hle : (A.card : ℝ) ≤ maxSize N := by exact_mod_cast card_le_maxSize hA hP
    apply (lt_div_iff₀ hNp).mpr
    nlinarith
  · intro b hb
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hle : (maxSize N : ℝ) ≤ N := by exact_mod_cast maxSize_le N
    exact lt_of_le_of_lt ((div_le_one hNp).mpr hle) hb

theorem nearFullWitnesses_of_fullAsymptotic (h : FullAsymptotic) : NearFullWitnesses := by
  intro ε hε
  have hlower := (tendsto_order.mp h).1 (1 - ε) (by linarith)
  filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  obtain ⟨A, hA, hP, hcard⟩ := maxSize_attained N
  refine ⟨A, hA, hP, ?_⟩
  rw [hcard]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact le_of_lt ((lt_div_iff₀ hNp).mp hN)

theorem nearFullWitnesses_iff_fullAsymptotic : NearFullWitnesses ↔ FullAsymptotic := by
  exact ⟨fullAsymptotic_of_nearFullWitnesses, nearFullWitnesses_of_fullAsymptotic⟩

theorem primitive_iff_proper_subsets (A : Finset ℕ) : Primitive A ↔
    ∃ δ : ℕ → ℤˣ, signedSum A δ = 0 ∧
      ∀ C ⊂ A, C.Nonempty → signedSum C δ ≠ 0 := by
  constructor
  · rintro ⟨δ, htotal, hminimal⟩
    refine ⟨δ, htotal, ?_⟩
    intro C hC hne hzero
    rcases hminimal C (Finset.ssubset_iff_subset_ne.mp hC).1 hzero with he | he
    · exact hne.ne_empty he
    · exact (Finset.ssubset_iff_subset_ne.mp hC).2 he
  · rintro ⟨δ, htotal, hminimal⟩
    refine ⟨δ, htotal, ?_⟩
    intro C hCA hzero
    by_cases he : C = ∅
    · exact Or.inl he
    · by_cases hfull : C = A
      · exact Or.inr hfull
      · exact False.elim (hminimal C (Finset.ssubset_iff_subset_ne.mpr ⟨hCA, hfull⟩)
          (Finset.nonempty_iff_ne_empty.mpr he) hzero)

theorem maxSize_isGreatest (N : ℕ) : IsGreatest
    {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Primitive A ∧ A.card = k}
    (maxSize N) := by
  refine ⟨maxSize_attained N, ?_⟩
  rintro k ⟨A, hA, hP, rfl⟩
  exact card_le_maxSize hA hP

noncomputable def coprimeDensity (D : ℕ) : ℝ := (D.totient : ℝ) / D

theorem coprimeDensity_pos {D : ℕ} (hD : 0 < D) : 0 < coprimeDensity D := by
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hD) (by exact_mod_cast hD)

theorem coprimeDensity_le_one {D : ℕ} (hD : 0 < D) : coprimeDensity D ≤ 1 := by
  exact (div_le_one (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
    (by exact_mod_cast Nat.totient_le D)

/- The two propositions below specify the remaining major proof obligations.
They are explicit hypotheses in the reduction theorem, never added axioms. -/
def CoreAmplification : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
    ∃ D : ℕ, ∃ E : Finset ℕ, 0 < D ∧ Squarefree D ∧ MinimalCore D E ∧
      0 < reciprocalSum E ∧ 1 - 2 * δ ≤ coprimeDensity D ∧
      Real.log (1 / δ) ≤ (reciprocalSum E : ℝ)

def DenseExpansions : Prop :=
  ∀ D : ℕ, 0 < D → Squarefree D → ∀ r : ℚ, 0 < r → DIntegral D r →
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
      ∃ F : Finset ℕ, F ⊆ Finset.Icc 1 N ∧
        (∀ n ∈ F, n.Coprime D) ∧ reciprocalSum F = r ∧
        (coprimeDensity D * (1 - Real.exp (-(r : ℝ) / coprimeDensity D)) - η) * N ≤
          (F.card : ℝ)

theorem nearFullWitnesses_of_inputs
    (hamp : CoreAmplification) (hdense : DenseExpansions) : NearFullWitnesses := by
  intro ε hε
  let δ : ℝ := min (ε / 8) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  obtain ⟨D, E, hD, hDsf, hcore, hr, hρlower, hrlog⟩ := hamp δ hδ hδsmall
  have hρpos := coprimeDensity_pos hD
  have hρupper := coprimeDensity_le_one hD
  have hrR : (0 : ℝ) < reciprocalSum E := by exact_mod_cast hr
  have hrdiv : (reciprocalSum E : ℝ) ≤ (reciprocalSum E : ℝ) / coprimeDensity D := by
    apply (le_div_iff₀ hρpos).mpr
    nlinarith
  have hexp : Real.exp (-(reciprocalSum E : ℝ) / coprimeDensity D) ≤ δ := by
    calc
      _ ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hprod : (1 - 2 * δ) * (1 - δ) ≤
      coprimeDensity D * (1 - Real.exp (-(reciprocalSum E : ℝ) / coprimeDensity D)) := by
    calc
      _ ≤ coprimeDensity D * (1 - δ) :=
        mul_le_mul_of_nonneg_right hρlower (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hρpos.le
  have hcoeff : 1 - ε ≤
      coprimeDensity D * (1 - Real.exp (-(reciprocalSum E : ℝ) / coprimeDensity D)) - ε / 2 := by
    nlinarith [sq_nonneg δ]
  have hf := hdense D hD hDsf (reciprocalSum E) hr hcore.2.1 (ε / 2) (by linarith)
  filter_upwards [hf, eventually_ge_atTop (E.sup id)] with N hF hEN
  obtain ⟨F, hFsub, hFcop, hFeq, hFcard⟩ := hF
  have hEsub : E ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hcore.1 n hn).1, (Finset.le_sup (f := fun q : ℕ => q) hn).trans hEN⟩
  refine ⟨E ∪ F, Finset.union_subset hEsub hFsub, ?_, ?_⟩
  · exact primitive_union_of_minimalCore hcore
      (fun n hn => (Finset.mem_Icc.mp (hFsub hn)).1) hFcop hFeq.symm
  · calc
      _ ≤ (coprimeDensity D * (1 - Real.exp (-(reciprocalSum E : ℝ) / coprimeDensity D)) - ε / 2) * N :=
        mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N)
      _ ≤ (F.card : ℝ) := hFcard
      _ ≤ ((E ∪ F).card : ℝ) := by exact_mod_cast Finset.card_le_card Finset.subset_union_right

theorem fullAsymptotic_of_inputs
    (hamp : CoreAmplification) (hdense : DenseExpansions) : FullAsymptotic := by
  exact fullAsymptotic_of_nearFullWitnesses (nearFullWitnesses_of_inputs hamp hdense)

theorem dIntegral_mul {D : ℕ} {r s : ℚ}
    (hr : DIntegral D r) (hs : DIntegral D s) : DIntegral D (r * s) := by
  exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd r s) (Nat.Coprime.mul_left hr hs)

theorem dIntegral_div_nat {D a b : ℕ} (hb : b.Coprime D) :
    DIntegral D ((a : ℚ) / b) := by
  rw [div_eq_mul_inv]
  exact dIntegral_mul (by simp [DIntegral]) (dIntegral_reciprocal hb)

theorem dvd_cleared_numerator {D p Q U : ℕ} {r : ℚ}
    (hpD : p ∣ D) (hpQ : p ∣ Q) (hr : DIntegral D r)
    (hclear : (Q : ℚ) * r = U) : p ∣ U := by
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz r
  have hrd : r * (r.den : ℚ) = (r.num : ℚ) :=
    (eq_div_iff hden).mp (Rat.num_div_den r).symm
  have hcrossQ : (Q : ℚ) * (r.num : ℚ) = (U : ℚ) * r.den := by
    rw [← hrd, ← mul_assoc, hclear]
  have hcrossZ : (Q : ℤ) * r.num = (U : ℤ) * (r.den : ℤ) := by exact_mod_cast hcrossQ
  have habs : Q * r.num.natAbs = U * r.den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hcrossZ
  have hprod : p ∣ U * r.den := by
    rw [← habs]
    exact dvd_mul_of_dvd_left hpQ _
  have hcop : p.Coprime r.den := (Nat.Coprime.of_dvd_right hpD hr).symm
  exact hcop.dvd_mul_right.mp hprod

theorem bounded_weight_zero {p B b a : ℕ}
    (hb : b ≤ B) (hB : B < p) (hcop : p.Coprime a)
    (hcong : a * b ≡ 0 [MOD p]) : b = 0 := by
  have hdiv : p ∣ b := hcop.dvd_mul_left.mp (Nat.modEq_zero_iff_dvd.mp hcong)
  exact Nat.eq_zero_of_dvd_of_lt hdiv (hb.trans_lt hB)

theorem bounded_weight_full {p B b a L : ℕ}
    (hb : b ≤ B) (hB : B < p) (hcop : p.Coprime a)
    (hfull : a * B + L ≡ 0 [MOD p])
    (hcong : a * b + L ≡ 0 [MOD p]) : b = B := by
  have hm : a * b ≡ a * B [MOD p] :=
    Nat.ModEq.add_right_cancel' L (hcong.trans hfull.symm)
  exact (Nat.ModEq.cancel_left_of_coprime hcop hm).eq_of_lt_of_lt (hb.trans_lt hB) hB

theorem nat_weight_sum_zero_iff {ι : Type*} {I : Finset ι} {w : ι → ℕ}
    (hpos : ∀ i ∈ I, 0 < w i) : (∑ i ∈ I, w i) = 0 ↔ I = ∅ := by
  constructor
  · intro hsum
    by_contra hne
    have hpositive : 0 < ∑ i ∈ I, w i :=
      Finset.sum_pos hpos (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  · rintro rfl
    simp

theorem nat_weight_sum_eq_of_subset {ι : Type*} {I J : Finset ι} {w : ι → ℕ}
    (hJI : J ⊆ I) (hpos : ∀ i ∈ I, 0 < w i)
    (hsum : (∑ i ∈ J, w i) = ∑ i ∈ I, w i) : J = I := by
  classical
  have hz : (∑ i ∈ I \ J, w i) = 0 := by
    have hs := Finset.sum_sdiff hJI (f := w)
    omega
  have hempty : I \ J = ∅ := (nat_weight_sum_zero_iff
    (fun i hi => hpos i (Finset.mem_sdiff.mp hi).1)).mp hz
  exact Finset.Subset.antisymm hJI (Finset.sdiff_eq_empty_iff_subset.mp hempty)

theorem coherent_group_choices {ι : Type*}
    (P : Finset ℕ) (I : Finset ι) (w : ι → ℕ)
    (J : ℕ → Finset ι) (a : ℕ → ℕ) (L h : ℕ)
    (hpos : ∀ i ∈ I, 0 < w i)
    (hJ : ∀ p ∈ P, J p ⊆ I)
    (hlarge : ∀ p ∈ P, (∑ i ∈ I, w i) < p)
    (hcop : ∀ p ∈ P, p.Coprime (a p))
    (hfull : ∀ p ∈ P, a p * (∑ i ∈ I, w i) + L ≡ 0 [MOD p])
    (hseen : ∀ p ∈ P, a p * (∑ i ∈ J p, w i) + h * L ≡ 0 [MOD p])
    (hbit : h ≤ 1) :
    (h = 0 ∧ ∀ p ∈ P, J p = ∅) ∨ (h = 1 ∧ ∀ p ∈ P, J p = I) := by
  have hcases : h = 0 ∨ h = 1 := by omega
  rcases hcases with rfl | rfl
  · refine Or.inl ⟨rfl, ?_⟩
    intro p hp
    apply (nat_weight_sum_zero_iff (fun i hi => hpos i (hJ p hp hi))).mp
    apply bounded_weight_zero
      (Finset.sum_le_sum_of_subset_of_nonneg (hJ p hp) (fun _ _ _ => Nat.zero_le _))
      (hlarge p hp) (hcop p hp)
    simpa using hseen p hp
  · refine Or.inr ⟨rfl, ?_⟩
    intro p hp
    apply nat_weight_sum_eq_of_subset (hJ p hp) hpos
    apply bounded_weight_full
      (Finset.sum_le_sum_of_subset_of_nonneg (hJ p hp) (fun _ _ _ => Nat.zero_le _))
      (hlarge p hp) (hcop p hp) (hfull p hp)
    simpa using hseen p hp

theorem exists_cancel_residue (p a L : ℕ) (hp : 0 < p) (ha : a.Coprime p) :
    ∃ x : ℕ, a * x + L ≡ 0 [MOD p] := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let x : ZMod p := -(L : ZMod p) * (a : ZMod p)⁻¹
  refine ⟨x.val, (ZMod.natCast_eq_natCast_iff _ 0 p).mp ?_⟩
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_zero, ZMod.natCast_zmod_val]
  calc
    (a : ZMod p) * x + L = -(L : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) + L := by
      dsimp [x]
      ring
    _ = 0 := by rw [ZMod.coe_mul_inv_eq_one a ha]; simp

theorem exists_positive_crt
    (P : Finset ℕ) (hpos : ∀ p ∈ P, 0 < p)
    (hpair : Set.Pairwise (↑P) Nat.Coprime) (res : ℕ → ℕ) :
    ∃ t : ℕ, 0 < t ∧ ∀ p ∈ P, t ≡ res p [MOD p] := by
  let x := Nat.chineseRemainderOfFinset res id P
    (fun p hp => Nat.ne_of_gt (hpos p hp)) hpair
  let D := ∏ p ∈ P, p
  have hDpos : 0 < D := Finset.prod_pos hpos
  refine ⟨x.val + D, by omega, ?_⟩
  intro p hp
  have hpD : p ∣ D := Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp
  simpa using (x.prop p hp).add (Nat.modEq_zero_iff_dvd.mpr hpD)

theorem exists_positive_cancelling_crt
    (P : Finset ℕ) (a : ℕ → ℕ) (L : ℕ)
    (hpos : ∀ p ∈ P, 0 < p)
    (hpair : Set.Pairwise (↑P) Nat.Coprime)
    (hcop : ∀ p ∈ P, (a p).Coprime p) :
    ∃ t : ℕ, 0 < t ∧ ∀ p ∈ P, a p * t + L ≡ 0 [MOD p] := by
  classical
  let res : ℕ → ℕ := fun p => if hp : p ∈ P then
    Classical.choose (exists_cancel_residue p (a p) L (hpos p hp) (hcop p hp)) else 0
  have hres : ∀ p ∈ P, a p * res p + L ≡ 0 [MOD p] := by
    intro p hp
    simp only [res, dite_eq_left hp]
    exact Classical.choose_spec (exists_cancel_residue p (a p) L (hpos p hp) (hcop p hp))
  obtain ⟨t, ht, htr⟩ := exists_positive_crt P hpos hpair res
  refine ⟨t, ht, ?_⟩
  intro p hp
  exact (((htr p hp).mul_left (a p)).add_right L).trans (hres p hp)

theorem primeProduct_div_eq_erase (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p ∈ P) : (∏ q ∈ P, q) / p = ∏ q ∈ P.erase p, q := by
  rw [← Finset.mul_prod_erase P (fun q : ℕ => q) hp,
    Nat.mul_div_cancel_left _ (hprime p hp).pos]

theorem primeProduct_div_coprime (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p ∈ P) : p.Coprime ((∏ q ∈ P, q) / p) := by
  rw [primeProduct_div_eq_erase P hprime hp]
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  obtain ⟨hqp, hqP⟩ := Finset.mem_erase.mp hq
  exact (Nat.coprime_primes (hprime p hp) (hprime q hqP)).mpr hqp.symm

theorem group_denominator_injective (P : Finset ℕ) (K : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p) :
    Set.InjOn (fun z : ℕ × ℕ => z.1 * z.2) (↑(P ×ˢ Finset.Icc 1 K)) := by
  intro x hx y hy heq
  change x.1 * x.2 = y.1 * y.2 at heq
  obtain ⟨hxp, hxm⟩ := Finset.mem_product.mp hx
  obtain ⟨hyp, hym⟩ := Finset.mem_product.mp hy
  have hdiv : x.1 ∣ y.1 * y.2 := by
    rw [← heq]
    exact dvd_mul_right _ _
  have hpq : x.1 = y.1 := by
    rcases (hprime x.1 hxp).dvd_mul.mp hdiv with hdiv | hdiv
    · rcases (Nat.dvd_prime (hprime y.1 hyp)).mp hdiv with he | he
      · exact False.elim ((hprime x.1 hxp).ne_one he)
      · exact he
    · have hle := Nat.le_of_dvd (Finset.mem_Icc.mp hym).1 hdiv
      have := hlarge x.1 hxp
      have := (Finset.mem_Icc.mp hym).2
      omega
  apply Prod.ext hpq
  exact mul_left_cancel₀ (hprime y.1 hyp).ne_zero (by simpa [hpq] using heq)

def groupDenominators (P : Finset ℕ) (K : ℕ) : Finset ℕ :=
  (P ×ˢ Finset.Icc 1 K).image (fun z : ℕ × ℕ => z.1 * z.2)

def crtSupport (P : Finset ℕ) (K t : ℕ) : Finset ℕ :=
  insert ((∏ p ∈ P, p) * t) (groupDenominators P K)

theorem mem_groupDenominators_iff {P : Finset ℕ} {K n : ℕ} :
    n ∈ groupDenominators P K ↔
      ∃ p ∈ P, ∃ m ∈ Finset.Icc 1 K, p * m = n := by
  constructor
  · rintro hn
    obtain ⟨⟨p, m⟩, hz, heq⟩ := Finset.mem_image.mp hn
    exact ⟨p, (Finset.mem_product.mp hz).1, m, (Finset.mem_product.mp hz).2, heq⟩
  · rintro ⟨p, hp, m, hm, heq⟩
    exact Finset.mem_image.mpr ⟨(p, m), Finset.mem_product.mpr ⟨hp, hm⟩, heq⟩

theorem not_coprime_of_common_prime {n D p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hpD : p ∣ D) : ¬n.Coprime D := by
  intro hcop
  have hg : p ∣ n.gcd D := Nat.dvd_gcd hpn hpD
  change n.gcd D = 1 at hcop
  rw [hcop] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

theorem groupDenominators_pos_notCoprime (P : Finset ℕ) (K : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∀ n ∈ groupDenominators P K, 0 < n ∧ ¬n.Coprime (∏ p ∈ P, p) := by
  intro n hn
  obtain ⟨p, hp, m, hm, rfl⟩ := mem_groupDenominators_iff.mp hn
  exact ⟨Nat.mul_pos (hprime p hp).pos (Finset.mem_Icc.mp hm).1,
    not_coprime_of_common_prime (hprime p hp) (dvd_mul_right p m)
      (Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp)⟩

theorem connector_not_groupDenominators (P : Finset ℕ) (K t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p)
    (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q) :
    (∏ p ∈ P, p) * t ∉ groupDenominators P K := by
  intro hmem
  obtain ⟨p, hp, m, hm, heq⟩ := mem_groupDenominators_iff.mp hmem
  obtain ⟨p₀, hp₀, q₀, hq₀, hpq₀⟩ := htwo
  have hother : ∃ q ∈ P, q ≠ p := by
    by_cases he : p₀ = p
    · exact ⟨q₀, hq₀, fun hqp => hpq₀ (he.trans hqp.symm)⟩
    · exact ⟨p₀, hp₀, he⟩
  obtain ⟨q, hq, hqp⟩ := hother
  have hdiv : q ∣ p * m := by
    rw [heq]
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hq) t
  rcases (hprime q hq).dvd_mul.mp hdiv with hdiv | hdiv
  · rcases (Nat.dvd_prime (hprime p hp)).mp hdiv with he | he
    · exact (hprime q hq).ne_one he
    · exact hqp he
  · have hle := Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hdiv
    have := hlarge q hq
    have := (Finset.mem_Icc.mp hm).2
    omega

theorem crtSupport_pos_notCoprime (P : Finset ℕ) (K t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (ht : 0 < t)
    (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q) :
    ∀ n ∈ crtSupport P K t, 0 < n ∧ ¬n.Coprime (∏ p ∈ P, p) := by
  intro n hn
  rcases Finset.mem_insert.mp hn with rfl | hn
  · obtain ⟨p, hp, q, hq, hpq⟩ := htwo
    exact ⟨Nat.mul_pos (Finset.prod_pos (fun p hp => (hprime p hp).pos)) ht,
      not_coprime_of_common_prime (hprime p hp)
        (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp) t)
        (Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp)⟩
  · exact groupDenominators_pos_notCoprime P K hprime n hn

theorem reciprocalSum_groupDenominators (P : Finset ℕ) (K : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p) :
    reciprocalSum (groupDenominators P K) =
      reciprocalSum (Finset.Icc 1 K) * reciprocalSum P := by
  unfold reciprocalSum groupDenominators
  rw [Finset.sum_image (group_denominator_injective P K hprime hlarge), Finset.sum_product]
  simp_rw [Nat.cast_mul, mul_inv_rev, ← Finset.sum_mul]
  rw [← Finset.mul_sum]

theorem reciprocalSum_crtSupport (P : Finset ℕ) (K t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p)
    (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q) :
    reciprocalSum (crtSupport P K t) =
      reciprocalSum (Finset.Icc 1 K) * reciprocalSum P + (((∏ p ∈ P, p) * t : ℕ) : ℚ)⁻¹ := by
  change (∑ n ∈ insert ((∏ p ∈ P, p) * t) (groupDenominators P K), (n : ℚ)⁻¹) = _
  rw [Finset.sum_insert (connector_not_groupDenominators P K t hprime hlarge htwo)]
  change (((∏ p ∈ P, p) * t : ℕ) : ℚ)⁻¹ + reciprocalSum (groupDenominators P K) = _
  rw [reciprocalSum_groupDenominators P K hprime hlarge, add_comm]

def localChoices (C : Finset ℕ) (p K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun m => p * m ∈ C)

def localWeight (C : Finset ℕ) (p K L : ℕ) : ℕ :=
  ∑ m ∈ localChoices C p K, L / m

def connectorBit (P : Finset ℕ) (t : ℕ) (C : Finset ℕ) : ℕ :=
  if (∏ p ∈ P, p) * t ∈ C then 1 else 0

def coreNumerator (P : Finset ℕ) (K L t : ℕ) (C : Finset ℕ) : ℕ :=
  t * (∑ p ∈ P, ((∏ q ∈ P, q) / p) * localWeight C p K L) + connectorBit P t C * L

theorem reciprocalSum_subset_indicator {C E : Finset ℕ} (hC : C ⊆ E) :
    reciprocalSum C = ∑ n ∈ E, if n ∈ C then (n : ℚ)⁻¹ else 0 := by
  have hf : E.filter (fun n => n ∈ C) = C := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun hn => hn.2, fun hn => ⟨hC hn, hn⟩⟩
  unfold reciprocalSum
  rw [← Finset.sum_filter, hf]

theorem clear_group_term {D p m L t : ℕ}
    (hp : p ∣ D) (hm : m ∣ L) (hp0 : 0 < p) (hm0 : 0 < m) :
    ((D * t * L : ℕ) : ℚ) * (((p * m : ℕ) : ℚ)⁻¹) =
      ((t * (D / p) * (L / m) : ℕ) : ℚ) := by
  have hfac : t * (D / p) * (L / m) * (p * m) = D * t * L := by
    calc
      _ = ((D / p) * p) * t * ((L / m) * m) := by ring
      _ = _ := by rw [Nat.div_mul_cancel hp, Nat.div_mul_cancel hm]
  have hpm : ((p * m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hp0) (Nat.ne_of_gt hm0))
  rw [← div_eq_mul_inv]
  apply (div_eq_iff hpm).mpr
  exact_mod_cast hfac.symm

theorem clear_connector_term {D t L : ℕ} (hD : 0 < D) (ht : 0 < t) :
    ((D * t * L : ℕ) : ℚ) * (((D * t : ℕ) : ℚ)⁻¹) = (L : ℚ) := by
  have hDt : ((D * t : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hD) (Nat.ne_of_gt ht))
  rw [Nat.cast_mul (D * t) L]
  calc
    ((D * t : ℕ) : ℚ) * L * (((D * t : ℕ) : ℚ)⁻¹) =
        (((D * t : ℕ) : ℚ) * (((D * t : ℕ) : ℚ)⁻¹)) * L := by ring
    _ = _ := by rw [mul_inv_cancel₀ hDt, one_mul]

theorem clear_local_group (P : Finset ℕ) (K L t : ℕ) (C : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L)
    {p : ℕ} (hp : p ∈ P) :
    (((∏ q ∈ P, q) * t * L : ℕ) : ℚ) *
        (∑ m ∈ Finset.Icc 1 K, if p * m ∈ C then (((p * m : ℕ) : ℚ)⁻¹) else 0) =
      (t : ℚ) * (((∏ q ∈ P, q) / p : ℕ) : ℚ) * (localWeight C p K L : ℚ) := by
  unfold localWeight localChoices
  rw [Nat.cast_sum, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmem : p * m ∈ C
  · simp only [ite_eq_left hmem]
    simpa only [Nat.cast_mul, mul_assoc] using clear_group_term
      (Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp) (hdiv m hm)
      (hprime p hp).pos (Finset.mem_Icc.mp hm).1 (t := t)
  · simp [hmem]

theorem clear_crtSupport_subset (P : Finset ℕ) (K L t : ℕ) (C : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p)
    (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q) (ht : 0 < t)
    (hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L) (hC : C ⊆ crtSupport P K t) :
    (((∏ p ∈ P, p) * t * L : ℕ) : ℚ) * reciprocalSum C =
      (coreNumerator P K L t C : ℚ) := by
  have hsum := reciprocalSum_subset_indicator hC
  unfold crtSupport at hsum
  rw [Finset.sum_insert (connector_not_groupDenominators P K t hprime hlarge htwo),
    groupDenominators, Finset.sum_image (group_denominator_injective P K hprime hlarge),
    Finset.sum_product] at hsum
  have hconn : (((∏ p ∈ P, p) * t * L : ℕ) : ℚ) *
      (if (∏ p ∈ P, p) * t ∈ C then ((((∏ p ∈ P, p) * t : ℕ) : ℚ)⁻¹) else 0) =
      (connectorBit P t C : ℚ) * L := by
    by_cases hc : (∏ p ∈ P, p) * t ∈ C
    · simp only [connectorBit, ite_eq_left hc, Nat.cast_one, one_mul]
      exact clear_connector_term (Finset.prod_pos (fun p hp => (hprime p hp).pos)) ht
    · simp [connectorBit, hc]
  have hgroups : (((∏ p ∈ P, p) * t * L : ℕ) : ℚ) *
      (∑ p ∈ P, ∑ m ∈ Finset.Icc 1 K, if p * m ∈ C then (((p * m : ℕ) : ℚ)⁻¹) else 0) =
      (t : ℚ) * ∑ p ∈ P, (((∏ q ∈ P, q) / p : ℕ) : ℚ) * (localWeight C p K L : ℚ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simpa only [mul_assoc] using clear_local_group P K L t C hprime hdiv hp
  rw [hsum, mul_add, hconn, hgroups]
  simp only [coreNumerator, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  ring

theorem sum_modEq_single (P : Finset ℕ) (f : ℕ → ℕ) {p : ℕ} (hp : p ∈ P)
    (hzero : ∀ q ∈ P, q ≠ p → p ∣ f q) : (∑ q ∈ P, f q) ≡ f p [MOD p] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
  rw [Nat.cast_sum]
  apply Finset.sum_eq_single p
  · intro q hq hqp
    exact (ZMod.natCast_eq_zero_iff (f q) p).mpr (hzero q hq hqp)
  · intro hnot
    exact False.elim (hnot hp)

theorem coreNumerator_modEq (P : Finset ℕ) (K L t : ℕ) (C : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) :
    coreNumerator P K L t C ≡
      (t * ((∏ q ∈ P, q) / p)) * localWeight C p K L + connectorBit P t C * L [MOD p] := by
  have hs := sum_modEq_single P
    (fun q => ((∏ v ∈ P, v) / q) * localWeight C q K L) hp (by
      intro q hq hqp
      apply dvd_mul_of_dvd_left
      rw [primeProduct_div_eq_erase P hprime hq]
      exact Finset.dvd_prod_of_mem (f := fun v : ℕ => v) (Finset.mem_erase.mpr ⟨hqp.symm, hp⟩))
  simpa only [coreNumerator, Nat.mul_assoc] using (hs.mul_left t).add_right (connectorBit P t C * L)

theorem core_subset_dichotomy (P : Finset ℕ) (K t : ℕ) (C : Finset ℕ)
    (hC : C ⊆ crtSupport P K t)
    (hchoices : (connectorBit P t C = 0 ∧ ∀ p ∈ P, localChoices C p K = ∅) ∨
      (connectorBit P t C = 1 ∧ ∀ p ∈ P, localChoices C p K = Finset.Icc 1 K)) :
    C = ∅ ∨ C = crtSupport P K t := by
  rcases hchoices with ⟨hbit, hJ⟩ | ⟨hbit, hJ⟩
  · have hconn : (∏ p ∈ P, p) * t ∉ C := by
      intro hc
      simp [connectorBit, hc] at hbit
    refine Or.inl (Finset.Subset.antisymm ?_ (Finset.empty_subset C))
    intro n hn
    exfalso
    rcases Finset.mem_insert.mp (hC hn) with he | he
    · exact hconn (he ▸ hn)
    · obtain ⟨p, hp, m, hm, heq⟩ := mem_groupDenominators_iff.mp he
      have hmJ : m ∈ localChoices C p K := Finset.mem_filter.mpr ⟨hm, by rwa [heq]⟩
      rw [hJ p hp] at hmJ
      exact Finset.notMem_empty _ hmJ
  · have hconn : (∏ p ∈ P, p) * t ∈ C := by
      by_contra hc
      simp [connectorBit, hc] at hbit
    refine Or.inr (Finset.Subset.antisymm hC ?_)
    intro n hn
    rcases Finset.mem_insert.mp hn with he | he
    · exact he.symm ▸ hconn
    · obtain ⟨p, hp, m, hm, heq⟩ := mem_groupDenominators_iff.mp he
      have hmJ : m ∈ localChoices C p K := by rw [hJ p hp]; exact hm
      exact heq ▸ (Finset.mem_filter.mp hmJ).2

theorem crtSupport_subset_rigidity (P : Finset ℕ) (K L t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p)
    (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q) (ht : 0 < t) (hL : 0 < L)
    (hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L)
    (hB : ∀ p ∈ P, (∑ m ∈ Finset.Icc 1 K, L / m) < p)
    (hcop : ∀ p ∈ P, p.Coprime (t * ((∏ q ∈ P, q) / p)))
    (hfull : ∀ p ∈ P, (t * ((∏ q ∈ P, q) / p)) * (∑ m ∈ Finset.Icc 1 K, L / m) + L ≡ 0 [MOD p])
    (C : Finset ℕ) (hC : C ⊆ crtSupport P K t)
    (hint : DIntegral (∏ p ∈ P, p) (reciprocalSum C)) : C = ∅ ∨ C = crtSupport P K t := by
  have hseen : ∀ p ∈ P,
      (t * ((∏ q ∈ P, q) / p)) * localWeight C p K L + connectorBit P t C * L ≡ 0 [MOD p] := by
    intro p hp
    have hpD : p ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp
    have hpu : p ∣ coreNumerator P K L t C := dvd_cleared_numerator hpD
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpD t) L) hint
      (clear_crtSupport_subset P K L t C hprime hlarge htwo ht hdiv hC)
    exact (coreNumerator_modEq P K L t C hprime hp).symm.trans (Nat.modEq_zero_iff_dvd.mpr hpu)
  apply core_subset_dichotomy P K t C hC
  apply coherent_group_choices P (Finset.Icc 1 K) (fun m => L / m)
    (fun p => localChoices C p K) (fun p => t * ((∏ q ∈ P, q) / p)) L (connectorBit P t C)
  · intro m hm
    exact Nat.div_pos (Nat.le_of_dvd hL (hdiv m hm)) (Finset.mem_Icc.mp hm).1
  · intro p hp
    exact Finset.filter_subset _ _
  · exact hB
  · exact hcop
  · exact hfull
  · exact hseen
  · by_cases hc : (∏ p ∈ P, p) * t ∈ C <;> simp [connectorBit, hc]

theorem primeProduct_dvd_of_all (P : Finset ℕ) (U : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ U) : (∏ p ∈ P, p) ∣ U := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [Finset.prod_insert hp]
      have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr (by
        intro q hq
        apply (Nat.coprime_primes (hprime p (Finset.mem_insert_self p P))
          (hprime q (Finset.mem_insert_of_mem hq))).mpr
        intro he
        exact hp (he.symm ▸ hq))
      exact hcop.mul_dvd_of_dvd_of_dvd (hdiv p (Finset.mem_insert_self p P))
        (ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
          (fun q hq => hdiv q (Finset.mem_insert_of_mem hq)))

theorem primeProduct_squarefree (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr (by
        intro q hq
        apply (Nat.coprime_primes (hprime p (Finset.mem_insert_self p P))
          (hprime q (Finset.mem_insert_of_mem hq))).mpr
        intro he
        exact hp (he.symm ▸ hq))
      rw [Finset.prod_insert hp, Nat.squarefree_mul hcop]
      exact ⟨(hprime p (Finset.mem_insert_self p P)).squarefree,
        ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))⟩

theorem localChoices_crtSupport (P : Finset ℕ) (K t : ℕ) {p : ℕ} (hp : p ∈ P) :
    localChoices (crtSupport P K t) p K = Finset.Icc 1 K := by
  ext m
  simp only [localChoices, Finset.mem_filter]
  constructor
  · exact fun hm => hm.1
  · intro hm
    exact ⟨hm, Finset.mem_insert_of_mem
      (mem_groupDenominators_iff.mpr ⟨p, hp, m, hm, rfl⟩)⟩

theorem coreNumerator_full_dvd (P : Finset ℕ) (K L t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hfull : ∀ p ∈ P, (t * ((∏ q ∈ P, q) / p)) * (∑ m ∈ Finset.Icc 1 K, L / m) + L ≡ 0 [MOD p]) :
    (∏ p ∈ P, p) ∣ coreNumerator P K L t (crtSupport P K t) := by
  apply primeProduct_dvd_of_all P _ hprime
  intro p hp
  apply Nat.modEq_zero_iff_dvd.mp
  apply (coreNumerator_modEq P K L t (crtSupport P K t) hprime hp).trans
  have hbit : connectorBit P t (crtSupport P K t) = 1 := by simp [connectorBit, crtSupport]
  simpa only [localWeight, localChoices_crtSupport P K t hp, hbit, one_mul] using hfull p hp

theorem cancelling_parameter_coprime (P : Finset ℕ) (B L t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hL : 0 < L) (hLp : ∀ p ∈ P, L < p)
    (hfull : ∀ p ∈ P, (t * ((∏ q ∈ P, q) / p)) * B + L ≡ 0 [MOD p]) :
    t.Coprime (∏ p ∈ P, p) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.symm
  apply (hprime p hp).coprime_iff_not_dvd.mpr
  intro hpt
  have hz : (t * ((∏ q ∈ P, q) / p)) * B ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpt _) _)
  have hh : (t * ((∏ q ∈ P, q) / p)) * B + L ≡ L [MOD p] := by
    simpa using hz.add_right L
  have hLd : p ∣ L := Nat.modEq_zero_iff_dvd.mp (hh.symm.trans (hfull p hp))
  exact (not_le_of_gt (hLp p hp)) (Nat.le_of_dvd hL hLd)

theorem small_common_multiple_coprime (P : Finset ℕ) (L : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hL : 0 < L) (hLp : ∀ p ∈ P, L < p) :
    L.Coprime (∏ p ∈ P, p) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.symm
  apply (hprime p hp).coprime_iff_not_dvd.mpr
  exact fun hdiv => (not_le_of_gt (hLp p hp)) (Nat.le_of_dvd hL hdiv)

theorem reciprocalSum_crtSupport_dIntegral (P : Finset ℕ) (K L t : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, K < p)
    (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q) (ht : 0 < t) (hL : 0 < L)
    (hLp : ∀ p ∈ P, L < p) (hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L)
    (hfull : ∀ p ∈ P, (t * ((∏ q ∈ P, q) / p)) * (∑ m ∈ Finset.Icc 1 K, L / m) + L ≡ 0 [MOD p]) :
    DIntegral (∏ p ∈ P, p) (reciprocalSum (crtSupport P K t)) := by
  let D := ∏ p ∈ P, p
  have hD : 0 < D := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have htL : ((t * L : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt ht) (Nat.ne_of_gt hL)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  obtain ⟨u, hu⟩ := coreNumerator_full_dvd P K L t hprime hfull
  have hclear := clear_crtSupport_subset P K L t (crtSupport P K t)
    hprime hlarge htwo ht hdiv Finset.Subset.rfl
  have heq : reciprocalSum (crtSupport P K t) = (u : ℚ) / ((t * L : ℕ) : ℚ) := by
    apply (eq_div_iff htL).mpr
    apply mul_left_cancel₀ hDq
    calc
      (D : ℚ) * (reciprocalSum (crtSupport P K t) * ((t * L : ℕ) : ℚ)) =
          (((∏ p ∈ P, p) * t * L : ℕ) : ℚ) * reciprocalSum (crtSupport P K t) := by
        simp only [Nat.cast_mul, D]
        ring
      _ = (coreNumerator P K L t (crtSupport P K t) : ℚ) := hclear
      _ = (D : ℚ) * (u : ℚ) := by exact_mod_cast hu
  rw [heq]
  exact dIntegral_div_nat (Nat.Coprime.mul_left
    (cancelling_parameter_coprime P _ L t hprime hL hLp hfull)
    (small_common_multiple_coprime P L hprime hL hLp))

theorem totalWeight_ge_K (K L : ℕ) (hL : 0 < L)
    (hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L) : K ≤ ∑ m ∈ Finset.Icc 1 K, L / m := by
  calc
    K = ∑ m ∈ Finset.Icc 1 K, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun m hm =>
      Nat.div_pos (Nat.le_of_dvd hL (hdiv m hm)) (Finset.mem_Icc.mp hm).1)

theorem totalWeight_ge_L (K L : ℕ) (hK : 0 < K) : L ≤ ∑ m ∈ Finset.Icc 1 K, L / m := by
  have h1 : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
  simpa using Finset.single_le_sum (fun m _ => Nat.zero_le (L / m)) h1

theorem exists_crt_minimalCore (P : Finset ℕ) (K L : ℕ)
    (hK : 0 < K) (hL : 0 < L) (hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L)
    (hprime : ∀ p ∈ P, p.Prime) (htwo : ∃ p ∈ P, ∃ q ∈ P, p ≠ q)
    (hB : ∀ p ∈ P, (∑ m ∈ Finset.Icc 1 K, L / m) < p) :
    ∃ t : ℕ, 0 < t ∧ MinimalCore (∏ p ∈ P, p) (crtSupport P K t) ∧
      reciprocalSum (crtSupport P K t) =
        reciprocalSum (Finset.Icc 1 K) * reciprocalSum P + (((∏ p ∈ P, p) * t : ℕ) : ℚ)⁻¹ := by
  let B := ∑ m ∈ Finset.Icc 1 K, L / m
  have hLB : L ≤ B := totalWeight_ge_L K L hK
  have hBpos : 0 < B := hL.trans_le hLB
  have hKB : K ≤ B := totalWeight_ge_K K L hL hdiv
  have hlarge : ∀ p ∈ P, K < p := fun p hp => hKB.trans_lt (hB p hp)
  have hLp : ∀ p ∈ P, L < p := fun p hp => hLB.trans_lt (hB p hp)
  have hpair : Set.Pairwise (↑P) Nat.Coprime := fun p hp q hq hpq =>
    (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  have hcoeff : ∀ p ∈ P, (B * ((∏ q ∈ P, q) / p)).Coprime p := by
    intro p hp
    have hpB : p.Coprime B := (hprime p hp).coprime_iff_not_dvd.mpr
      (fun hd => (not_le_of_gt (hB p hp)) (Nat.le_of_dvd hBpos hd))
    exact (Nat.Coprime.mul_right hpB (primeProduct_div_coprime P hprime hp)).symm
  obtain ⟨t, ht, hcancel⟩ := exists_positive_cancelling_crt P
    (fun p => B * ((∏ q ∈ P, q) / p)) L (fun p hp => (hprime p hp).pos) hpair hcoeff
  have hfull : ∀ p ∈ P,
      (t * ((∏ q ∈ P, q) / p)) * (∑ m ∈ Finset.Icc 1 K, L / m) + L ≡ 0 [MOD p] := by
    intro p hp
    simpa only [B, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcancel p hp
  have htCop := cancelling_parameter_coprime P B L t hprime hL hLp hfull
  have hcop : ∀ p ∈ P, p.Coprime (t * ((∏ q ∈ P, q) / p)) := by
    intro p hp
    have hpt : p.Coprime t := (Nat.Coprime.of_dvd_right
      (Finset.dvd_prod_of_mem (f := fun q : ℕ => q) hp) htCop).symm
    exact Nat.Coprime.mul_right hpt (primeProduct_div_coprime P hprime hp)
  refine ⟨t, ht, ?_, reciprocalSum_crtSupport P K t hprime hlarge htwo⟩
  exact ⟨crtSupport_pos_notCoprime P K t hprime ht htwo,
    reciprocalSum_crtSupport_dIntegral P K L t hprime hlarge htwo ht hL hLp hdiv hfull,
    fun C hC hint => crtSupport_subset_rigidity P K L t hprime hlarge htwo ht hL hdiv
      hB hcop hfull C hC hint⟩

theorem reciprocalSum_real (A : Finset ℕ) :
    (reciprocalSum A : ℝ) = ∑ n ∈ A, (1 : ℝ) / n := by
  simp [reciprocalSum, one_div]

theorem reciprocalSum_nonneg (A : Finset ℕ) : 0 ≤ reciprocalSum A := by
  exact Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))

theorem reciprocalSum_Icc_real (K : ℕ) :
    (reciprocalSum (Finset.Icc 1 K) : ℝ) =
      ∑ i ∈ Finset.range K, (1 / (i + 1) : ℝ) := by
  rw [reciprocalSum_real]
  apply Finset.sum_bij (fun n _ => n - 1)
  · intro n hn
    apply Finset.mem_range.mpr
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hn
    omega
  · intro n hn m hm hnm
    have := (Finset.mem_Icc.mp hn).1
    have := (Finset.mem_Icc.mp hm).1
    omega
  · intro j hj
    refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, by omega⟩
    have := Finset.mem_range.mp hj
    omega
  · intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn1
    rw [hc]

theorem exists_large_harmonic (T : ℝ) :
    ∃ K : ℕ, 0 < K ∧ T ≤ (reciprocalSum (Finset.Icc 1 K) : ℝ) := by
  have ht : Tendsto (fun K : ℕ => (reciprocalSum (Finset.Icc 1 K) : ℝ)) atTop atTop := by
    simpa only [reciprocalSum_Icc_real] using Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨K, hT, hK⟩ := ((ht.eventually (eventually_ge_atTop T)).and (eventually_ge_atTop (1 : ℕ))).exists
  exact ⟨K, hK, hT⟩

theorem exists_subset_sum_window {ι : Type*} (S : Finset ι) (w : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : ∀ i ∈ S, w i < δ) (htotal : δ ≤ ∑ i ∈ S, w i) :
    ∃ P : Finset ι, P ⊆ S ∧ δ ≤ (∑ i ∈ P, w i) ∧ (∑ i ∈ P, w i) < 2 * δ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at htotal; linarith
  | @insert i S hi ih =>
      by_cases hS : δ ≤ ∑ j ∈ S, w j
      · obtain ⟨P, hP, hl, hu⟩ := ih (fun j hj => hsmall j (Finset.mem_insert_of_mem hj)) hS
        exact ⟨P, hP.trans (Finset.subset_insert i S), hl, hu⟩
      · refine ⟨insert i S, Finset.Subset.rfl, htotal, ?_⟩
        rw [Finset.sum_insert hi]
        have hiδ := hsmall i (Finset.mem_insert_self i S)
        linarith

theorem one_sub_sum_le_prod {ι : Type*} (P : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ P, 0 ≤ w i ∧ w i ≤ 1) :
    1 - (∑ i ∈ P, w i) ≤ ∏ i ∈ P, (1 - w i) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert i P hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hiw := hw i (Finset.mem_insert_self i P)
      have hPw := fun j hj => hw j (Finset.mem_insert_of_mem hj)
      have hsum : 0 ≤ ∑ j ∈ P, w j := Finset.sum_nonneg (fun j hj => (hPw j hj).1)
      have hs := mul_le_mul_of_nonneg_left (ih hPw) (sub_nonneg.mpr hiw.2)
      nlinarith [mul_nonneg hiw.1 hsum]

theorem coprimeDensity_primeProduct (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    coprimeDensity (∏ p ∈ P, p) = ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  induction P using Finset.induction_on with
  | empty => simp [coprimeDensity]
  | @insert p P hp ih =>
      have hprimeP := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      have hpprime := hprime p (Finset.mem_insert_self p P)
      have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr (by
        intro q hq
        apply (Nat.coprime_primes hpprime (hprimeP q hq)).mpr
        intro he
        exact hp (he.symm ▸ hq))
      have hpq : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
      have hratio : coprimeDensity p = 1 - (1 : ℝ) / p := by
        unfold coprimeDensity
        rw [Nat.totient_prime hpprime, Nat.cast_sub hpprime.one_lt.le,
          Nat.cast_one, sub_div, div_self hpq]
      calc
        coprimeDensity (∏ q ∈ insert p P, q) = coprimeDensity p * coprimeDensity (∏ q ∈ P, q) := by
          simp only [coprimeDensity, Finset.prod_insert hp, Nat.totient_mul hcop,
            Nat.cast_mul, mul_div_mul_comm]
        _ = (1 - (1 : ℝ) / p) * ∏ q ∈ P, (1 - (1 : ℝ) / q) := by rw [hratio, ih hprimeP]
        _ = _ := (Finset.prod_insert (f := fun q : ℕ => 1 - (1 : ℝ) / q) hp).symm

theorem coprimeDensity_primeProduct_lower (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    1 - (∑ p ∈ P, (1 : ℝ) / p) ≤ coprimeDensity (∏ p ∈ P, p) := by
  rw [coprimeDensity_primeProduct P hprime]
  apply one_sub_sum_le_prod
  intro p hp
  have hppos : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
  exact ⟨div_nonneg zero_le_one hppos.le,
    (div_le_one hppos).mpr (by exact_mod_cast (hprime p hp).one_lt.le)⟩

theorem exists_prime_packet (B : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ p ∈ P, B < p) ∧
      (∃ p ∈ P, ∃ q ∈ P, p ≠ q) ∧
      δ ≤ (∑ p ∈ P, (1 : ℝ) / p) ∧ (∑ p ∈ P, (1 : ℝ) / p) < 2 * δ := by
  let k := max (B + 1) (⌈1 / δ⌉₊ + 1)
  let S := (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hkp : ∀ p ∈ S, k ≤ p := by
    intro p hp
    have hnot := (Finset.mem_sdiff.mp hp).2
    simpa [Nat.primesBelow, hSprime p hp] using hnot
  have hsmall : ∀ p ∈ S, (1 : ℝ) / p < δ := by
    intro p hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast (hSprime p hp).pos
    have hkceil : ⌈1 / δ⌉₊ + 1 ≤ k := le_max_right _ _
    have hceilp : ⌈1 / δ⌉₊ < p := by have := hkp p hp; omega
    have hthreshold : 1 / δ < (p : ℝ) :=
      (Nat.le_ceil (1 / δ)).trans_lt (by exact_mod_cast hceilp)
    have hmul : 1 < (p : ℝ) * δ := (div_lt_iff₀ hδ).mp hthreshold
    exact (div_lt_iff₀ hppos).mpr (by nlinarith)
  have htotal : δ ≤ ∑ p ∈ S, (1 : ℝ) / p :=
    (by linarith : δ ≤ (1 : ℝ) / 2).trans (one_half_le_sum_primes_ge_one_div k)
  obtain ⟨P, hPS, hlower, hupper⟩ := exists_subset_sum_window S (fun p => (1 : ℝ) / p)
    δ hδ hsmall htotal
  have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    have hpositive := hδ.trans_le hlower
    simp [he] at hpositive)
  obtain ⟨p, hp⟩ := hPne
  have hother : ∃ q ∈ P, q ≠ p := by
    by_contra hnot
    have hsub : P ⊆ {p} := by
      intro q hq
      apply Finset.mem_singleton.mpr
      by_contra hqp
      exact hnot ⟨q, hq, hqp⟩
    have heq : P = {p} := Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hp)
    have hl : δ ≤ (1 : ℝ) / p := by simpa [heq] using hlower
    exact (not_le_of_gt (hsmall p (hPS hp))) hl
  obtain ⟨q, hq, hqp⟩ := hother
  refine ⟨P, fun p hp => hSprime p (hPS hp), ?_, ⟨p, hp, q, hq, hqp.symm⟩, hlower, hupper⟩
  intro p hp
  have hkB : B + 1 ≤ k := le_max_left _ _
  have := hkp p (hPS hp)
  omega

theorem coreAmplification_proved : CoreAmplification := by
  intro δ hδ hδsmall
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  obtain ⟨K, hK, hHK⟩ := exists_large_harmonic (Real.log (1 / δ) / δ)
  -- Any common multiple works in the CRT argument; the factorial avoids
  -- additional least-common-multiple bookkeeping.
  let L := K.factorial
  have hL : 0 < L := Nat.factorial_pos K
  have hdiv : ∀ m ∈ Finset.Icc 1 K, m ∣ L := fun m hm =>
    Nat.dvd_factorial (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
  let B := ∑ m ∈ Finset.Icc 1 K, L / m
  obtain ⟨P, hprime, hlargeB, htwo, hsumlower, hsumupper⟩ := exists_prime_packet B δ hδ hδsmall
  obtain ⟨t, ht, hcore, hmass⟩ := exists_crt_minimalCore P K L hK hL hdiv hprime htwo hlargeB
  let D := ∏ p ∈ P, p
  let E := crtSupport P K t
  have hHnonneg : (0 : ℝ) ≤ reciprocalSum (Finset.Icc 1 K) := by
    exact_mod_cast reciprocalSum_nonneg (Finset.Icc 1 K)
  have hmassR := congrArg (fun r : ℚ => (r : ℝ)) hmass
  push_cast at hmassR
  rw [reciprocalSum_real P] at hmassR
  have hterm : (0 : ℝ) ≤ (((∏ p ∈ P, p) * t : ℕ) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hmasslower : (reciprocalSum (Finset.Icc 1 K) : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) ≤
      (reciprocalSum E : ℝ) := by
    calc
      _ ≤ (reciprocalSum (Finset.Icc 1 K) : ℝ) * (∑ p ∈ P, (1 : ℝ) / p) +
          (((∏ p ∈ P, p) * t : ℕ) : ℝ)⁻¹ := le_add_of_nonneg_right hterm
      _ = _ := by simpa only [Nat.cast_mul, Nat.cast_prod, E] using hmassR.symm
  have hRlog : Real.log (1 / δ) ≤ (reciprocalSum E : ℝ) :=
    ((div_le_iff₀ hδ).mp hHK).trans
      ((mul_le_mul_of_nonneg_left hsumlower hHnonneg).trans hmasslower)
  have hρlower : 1 - 2 * δ ≤ coprimeDensity D := by
    have hρ := coprimeDensity_primeProduct_lower P hprime
    change 1 - 2 * δ ≤ coprimeDensity (∏ p ∈ P, p)
    linarith
  exact ⟨D, E, Finset.prod_pos (fun p hp => (hprime p hp).pos),
    primeProduct_squarefree P hprime, hcore,
    by exact_mod_cast hlog.trans_le hRlog, hρlower, hRlog⟩

theorem fullAsymptotic_of_denseExpansions (hdense : DenseExpansions) : FullAsymptotic := by
  exact fullAsymptotic_of_inputs coreAmplification_proved hdense

theorem card_le_N_mul_reciprocalSum {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) : (A.card : ℝ) ≤ N * (reciprocalSum A : ℝ) := by
  calc
    (A.card : ℝ) = ∑ n ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ A, (N : ℝ) * ((1 : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hA hn)).1
      have hnupper : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp (hA hn)).2
      simpa only [mul_one_div] using (one_le_div hnpos).mpr hnupper
    _ = _ := by rw [reciprocalSum_real, Finset.mul_sum]

theorem complement_expansion {N : ℕ} {W G : Finset ℕ} {r : ℚ}
    (hW : W ⊆ Finset.Icc 1 N) (hG : G ⊆ W)
    (hsum : reciprocalSum G = reciprocalSum W - r) :
    reciprocalSum (W \ G) = r ∧
      (W.card : ℝ) - N * (reciprocalSum G : ℝ) ≤ ((W \ G).card : ℝ) := by
  constructor
  · have hs := Finset.sum_sdiff hG (f := fun n : ℕ => (n : ℚ)⁻¹)
    change reciprocalSum (W \ G) + reciprocalSum G = reciprocalSum W at hs
    linarith
  · have hGc := card_le_N_mul_reciprocalSum (hG.trans hW)
    have hcards : (W \ G).card + G.card = W.card := by
      simpa using (Finset.sum_sdiff hG (f := fun _ : ℕ => (1 : ℕ)))
    have hcardsR : ((W \ G).card : ℝ) + G.card = W.card := by exact_mod_cast hcards
    linarith

def WindowDenseExpansions : Prop :=
  ∀ D : ℕ, 0 < D → Squarefree D → ∀ r : ℚ, 0 < r → DIntegral D r →
    ∀ κ : ℝ, 0 < κ → κ < min ((r : ℝ) / 2) (1 / 2) →
      ∀ θ : ℝ, 0 < θ → ∀ᶠ N : ℕ in atTop,
        ∃ F : Finset ℕ, F ⊆ Finset.Icc 1 N ∧
          (∀ n ∈ F, n.Coprime D) ∧ reciprocalSum F = r ∧
          (coprimeDensity D * (1 - Real.exp (-((r : ℝ) + κ) / coprimeDensity D)) - κ - θ) * N ≤
            (F.card : ℝ)

theorem denseExpansions_of_window (hwindow : WindowDenseExpansions) : DenseExpansions := by
  intro D hD hDsf r hr hint η hη
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let κ := min (η / 4) (min ((r : ℝ) / 4) (1 / 4))
  have hκ : 0 < κ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hκη : κ ≤ η / 4 := min_le_left _ _
  have hκr : κ ≤ (r : ℝ) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hκsmall : κ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hκrange : κ < min ((r : ℝ) / 2) (1 / 2) := lt_min (by linarith) (by linarith)
  have hρpos := coprimeDensity_pos hD
  have hnegative : -((r : ℝ) + κ) / coprimeDensity D ≤ -(r : ℝ) / coprimeDensity D :=
    div_le_div_of_nonneg_right (by linarith) hρpos.le
  have hexp := Real.exp_le_exp.mpr hnegative
  have hγ : coprimeDensity D * (1 - Real.exp (-(r : ℝ) / coprimeDensity D)) ≤
      coprimeDensity D * (1 - Real.exp (-((r : ℝ) + κ) / coprimeDensity D)) :=
    mul_le_mul_of_nonneg_left (by linarith) hρpos.le
  have hcoeff : coprimeDensity D * (1 - Real.exp (-(r : ℝ) / coprimeDensity D)) - η ≤
      coprimeDensity D * (1 - Real.exp (-((r : ℝ) + κ) / coprimeDensity D)) - κ - η / 4 := by
    linarith
  filter_upwards [hwindow D hD hDsf r hr hint κ hκ hκrange (η / 4) (by linarith)] with N hN
  obtain ⟨F, hF, hcop, hsum, hcard⟩ := hN
  exact ⟨F, hF, hcop, hsum,
    (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N)).trans hcard⟩

theorem fullAsymptotic_of_windowDenseExpansions (hwindow : WindowDenseExpansions) : FullAsymptotic := by
  exact fullAsymptotic_of_denseExpansions (denseExpansions_of_window hwindow)

/-! Finite Fourier foundations for the remaining analytic input. -/

noncomputable def selectionWeight {ι : Type*} (A : Finset ι) (p : ι → ℝ) (B : Finset ι) : ℝ := by
  classical
  exact (∏ i ∈ B, p i) * ∏ i ∈ A \ B, (1 - p i)

theorem selectionWeight_nonneg {ι : Type*} (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) {B : Finset ι} (hB : B ⊆ A) :
    0 ≤ selectionWeight A p B := by
  classical
  exact mul_nonneg (Finset.prod_nonneg (fun i hi => (hp i (hB hi)).1))
    (Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hp i (Finset.mem_sdiff.mp hi).1).2))

theorem selectionWeight_sum {ι : Type*} (A : Finset ι) (p : ι → ℝ) :
    (∑ B ∈ A.powerset, selectionWeight A p B) = 1 := by
  classical
  unfold selectionWeight
  rw [← Finset.prod_add]
  simp

theorem selectionWeight_cast {ι : Type*} [DecidableEq ι] (A : Finset ι) (p : ι → ℝ) (B : Finset ι) :
    (selectionWeight A p B : ℂ) =
      (∏ i ∈ B, (p i : ℂ)) * ∏ i ∈ A \ B, (1 - (p i : ℂ)) := by
  classical
  unfold selectionWeight
  push_cast
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem character_orthogonality {Q : ℕ} [NeZero Q] (t : ZMod Q) :
    (∑ h : ZMod Q, ZMod.stdAddChar (t * h)) = if t = 0 then (Q : ℂ) else 0 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [ite_eq_right ht]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar Q ht)

theorem character_finset_sum {ι : Type*} {Q : ℕ} [NeZero Q]
    (B : Finset ι) (w : ι → ZMod Q) (h : ZMod Q) :
    ZMod.stdAddChar (h * ∑ i ∈ B, w i) = ∏ i ∈ B, ZMod.stdAddChar (h * w i) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert i B hi ih =>
      rw [Finset.sum_insert hi, mul_add, AddChar.map_add_eq_mul, ih, Finset.prod_insert hi]

theorem weighted_characteristic {ι : Type*} {Q : ℕ} [NeZero Q]
    (A : Finset ι) (p : ι → ℝ) (w : ι → ZMod Q) (h : ZMod Q) :
    (∑ B ∈ A.powerset, (selectionWeight A p B : ℂ) *
      ZMod.stdAddChar (h * ∑ i ∈ B, w i)) =
      ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (h * w i)) := by
  classical
  symm
  calc
    _ = ∏ i ∈ A, ((p i : ℂ) * ZMod.stdAddChar (h * w i) + (1 - (p i : ℂ))) := by
      apply Finset.prod_congr rfl
      intro i hi
      push_cast
      ring
    _ = ∑ B ∈ A.powerset,
        (∏ i ∈ B, (p i : ℂ) * ZMod.stdAddChar (h * w i)) *
          ∏ i ∈ A \ B, (1 - (p i : ℂ)) := Finset.prod_add _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.prod_mul_distrib, selectionWeight_cast, character_finset_sum]
      ring

theorem weighted_fourier_identity {ι : Type*} {Q : ℕ} [NeZero Q]
    (A : Finset ι) (p : ι → ℝ) (w : ι → ZMod Q) (a : ZMod Q) :
    (∑ h : ZMod Q, ZMod.stdAddChar (-(h * a)) *
      ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (h * w i))) =
      (Q : ℂ) * ((∑ B ∈ A.powerset,
        if (∑ i ∈ B, w i) = a then selectionWeight A p B else 0 : ℝ) : ℂ) := by
  classical
  calc
    _ = ∑ h : ZMod Q, ∑ B ∈ A.powerset,
        (selectionWeight A p B : ℂ) * ZMod.stdAddChar (((∑ i ∈ B, w i) - a) * h) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [← weighted_characteristic, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      rw [show ((∑ i ∈ B, w i) - a) * h = -(h * a) + h * (∑ i ∈ B, w i) by ring,
        AddChar.map_add_eq_mul]
      ring
    _ = ∑ B ∈ A.powerset, (selectionWeight A p B : ℂ) *
        ∑ h : ZMod Q, ZMod.stdAddChar (((∑ i ∈ B, w i) - a) * h) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [character_orthogonality, sub_eq_zero]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      by_cases he : (∑ i ∈ B, w i) = a <;> simp [he, mul_comm]

theorem bernoulli_norm_sq (p : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * z‖ ^ 2 =
      1 - 2 * p * (1 - p) * (1 - z.re) := by
  have hnorm : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  have hzsq : z.re * z.re + z.im * z.im = 1 := by
    simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] using hnorm
  calc
    _ = (1 - p) ^ 2 + p ^ 2 * (z.re * z.re + z.im * z.im) +
        2 * p * (1 - p) * z.re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, add_zero, sub_zero]
      ring
    _ = _ := by rw [hzsq]; ring

theorem bernoulli_norm_le_one (p : ℝ) (z : ℂ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz : ‖z‖ = 1) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * z‖ ≤ 1 := by
  calc
    _ ≤ ‖((1 - p : ℝ) : ℂ)‖ + ‖(p : ℂ) * z‖ := norm_add_le _ _
    _ = (1 - p) + p := by
      rw [norm_mul, hz]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0,
        abs_of_nonneg (sub_nonneg.mpr hp1), mul_one]
    _ = _ := by ring

theorem cosine_phase_bound {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.cos (2 * Real.pi * x) ≤ 1 - 8 * x ^ 2 := by
  have harg : |2 * Real.pi * x| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  calc
    _ ≤ 1 - 2 / Real.pi ^ 2 * (2 * Real.pi * x) ^ 2 :=
      Real.cos_le_one_sub_mul_cos_sq harg
    _ = _ := by field_simp [Real.pi_ne_zero]; ring

theorem bernoulli_norm_contraction (p x : ℝ) (z : ℂ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz : ‖z‖ = 1)
    (hre : z.re ≤ 1 - 8 * x ^ 2) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * z‖ ≤ 1 - 8 * p * (1 - p) * x ^ 2 := by
  let T := 8 * p * (1 - p) * x ^ 2
  have ha : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hscaled := mul_le_mul_of_nonneg_left hre (by nlinarith : 0 ≤ 2 * p * (1 - p))
  have hsq : ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * z‖ ^ 2 ≤ 1 - 2 * T := by
    rw [bernoulli_norm_sq p z hz]
    dsimp [T]
    nlinarith only [hscaled]
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hright : 0 ≤ 1 - T := by
    nlinarith only [hsq, sq_nonneg ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * z‖]
  have hsquares : ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * z‖ ^ 2 ≤ (1 - T) ^ 2 := by
    nlinarith only [hsq, sq_nonneg T]
  exact (sq_le_sq₀ (norm_nonneg _) hright).mp hsquares

theorem bernoulli_phase_contraction (p x : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : |x| ≤ 1 / 2) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)‖ ≤
      1 - 8 * p * (1 - p) * x ^ 2 := by
  apply bernoulli_norm_contraction p x _ hp0 hp1
  · rw [Complex.norm_exp]
    simp
  · simpa [Complex.exp_re] using cosine_phase_bound hx

theorem bernoulli_phase_norm_le_exp (p x : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : |x| ≤ 1 / 2) :
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)‖ ≤
      Real.exp (-(8 * p * (1 - p) * x ^ 2)) := by
  exact (bernoulli_phase_contraction p x hp0 hp1 hx).trans
    (Real.one_sub_le_exp_neg (8 * p * (1 - p) * x ^ 2))

theorem norm_prod_le_exp_neg_sum {ι : Type*} (A : Finset ι)
    (f : ι → ℂ) (c : ι → ℝ) (h : ∀ i ∈ A, ‖f i‖ ≤ Real.exp (-(c i))) :
    ‖∏ i ∈ A, f i‖ ≤ Real.exp (-(∑ i ∈ A, c i)) := by
  calc
    _ = ∏ i ∈ A, ‖f i‖ := norm_prod _ _
    _ ≤ ∏ i ∈ A, Real.exp (-(c i)) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg (f i)) h
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem exists_subset_of_positive_fourier {ι : Type*} {Q : ℕ} [NeZero Q]
    (A : Finset ι) (p : ι → ℝ) (w : ι → ZMod Q) (a : ZMod Q)
    (hpositive : 0 < (∑ h : ZMod Q, ZMod.stdAddChar (-(h * a)) *
      ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (h * w i))).re) :
    ∃ B ⊆ A, (∑ i ∈ B, w i) = a := by
  classical
  by_contra hnone
  have hmass : (∑ B ∈ A.powerset,
      if (∑ i ∈ B, w i) = a then selectionWeight A p B else 0 : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro B hB
    apply ite_eq_right
    intro heq
    exact hnone ⟨B, Finset.mem_powerset.mp hB, heq⟩
  rw [weighted_fourier_identity, hmass] at hpositive
  simp at hpositive

noncomputable def selectionMass {ι : Type*} (A : Finset ι) (p : ι → ℝ)
    (event : Finset ι → Prop) : ℝ := by
  classical
  exact ∑ B ∈ A.powerset, if event B then selectionWeight A p B else 0

theorem selectionMass_mono {ι : Type*} (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (E F : Finset ι → Prop)
    (hEF : ∀ B ⊆ A, E B → F B) : selectionMass A p E ≤ selectionMass A p F := by
  classical
  apply Finset.sum_le_sum
  intro B hB
  have hw := selectionWeight_nonneg A p hp (Finset.mem_powerset.mp hB)
  by_cases he : E B
  · simp only [ite_eq_left he, ite_eq_left (hEF B (Finset.mem_powerset.mp hB) he)]
    exact le_rfl
  · by_cases hf : F B <;> simp [he, hf, hw]

theorem clear_reciprocalSum {A : Finset ℕ} {Q : ℕ}
    (hdiv : ∀ n ∈ A, n ∣ Q) :
    (Q : ℚ) * reciprocalSum A = ((∑ n ∈ A, Q / n : ℕ) : ℚ) := by
  unfold reciprocalSum
  rw [Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Rat.natCast_div Q n (hdiv n hn), div_eq_mul_inv]

theorem integer_difference_of_residue {Q x : ℕ} [NeZero Q] {B : Finset ℕ}
    (hdiv : ∀ n ∈ B, n ∣ Q)
    (hresidue : (∑ n ∈ B, ((Q / n : ℕ) : ZMod Q)) = (x : ZMod Q)) :
    ∃ z : ℤ, reciprocalSum B - (x : ℚ) / Q = (z : ℚ) := by
  let U := ∑ n ∈ B, Q / n
  have hres : (U : ZMod Q) = (x : ZMod Q) := by
    simpa only [U, Nat.cast_sum] using hresidue
  have hd : (Q : ℤ) ∣ (x : ℤ) - (U : ℤ) :=
    Nat.modEq_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff U x Q).mp hres)
  obtain ⟨k, hk⟩ := hd
  refine ⟨-k, ?_⟩
  have hQ : (Q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hclear := clear_reciprocalSum hdiv
  have hr : reciprocalSum B = (U : ℚ) / Q :=
    (eq_div_iff hQ).mpr (by simpa only [mul_comm, U] using hclear)
  have hcross : (x : ℚ) - (U : ℚ) = (Q : ℚ) * (k : ℚ) := by exact_mod_cast hk
  rw [hr, ← sub_div]
  apply (div_eq_iff hQ).mpr
  push_cast
  nlinarith only [hcross]

theorem rational_eq_of_integer_difference {a b : ℚ}
    (hint : ∃ z : ℤ, a - b = (z : ℚ))
    (hclose : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  obtain ⟨z, hz⟩ := hint
  have hzR : (a : ℝ) - (b : ℝ) = (z : ℝ) := by exact_mod_cast hz
  rw [hzR] at hclose
  have hlow : (-1 : ℤ) < z := by exact_mod_cast (abs_lt.mp hclose).1
  have hhigh : z < 1 := by exact_mod_cast (abs_lt.mp hclose).2
  have hz0 : z = 0 := by omega
  rw [hz0, Int.cast_zero] at hz
  exact sub_eq_zero.mp hz

theorem exact_reciprocalSum_of_residue_and_close {Q x : ℕ} [NeZero Q] {B : Finset ℕ}
    (hdiv : ∀ n ∈ B, n ∣ Q)
    (hresidue : (∑ n ∈ B, ((Q / n : ℕ) : ZMod Q)) = (x : ZMod Q))
    (hclose : |(reciprocalSum B : ℝ) - (x : ℝ) / Q| < 1) :
    reciprocalSum B = (x : ℚ) / Q := by
  apply rational_eq_of_integer_difference (integer_difference_of_residue hdiv hresidue)
  simpa only [Rat.cast_div, Rat.cast_natCast] using hclose

theorem exact_subset_of_modular_mass_gt_far_mass {Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) (hdiv : ∀ n ∈ A, n ∣ Q)
    (hgap : selectionMass A p (fun B => 1 ≤ |(reciprocalSum B : ℝ) - (x : ℝ) / Q|) <
      selectionMass A p (fun B => (∑ n ∈ B, ((Q / n : ℕ) : ZMod Q)) = (x : ZMod Q))) :
    ∃ B ⊆ A, reciprocalSum B = (x : ℚ) / Q := by
  classical
  by_contra hnone
  have hle := selectionMass_mono A p hp
    (fun B => (∑ n ∈ B, ((Q / n : ℕ) : ZMod Q)) = (x : ZMod Q))
    (fun B => 1 ≤ |(reciprocalSum B : ℝ) - (x : ℝ) / Q|) (by
      intro B hBA hres
      by_contra hfar
      exact hnone ⟨B, hBA, exact_reciprocalSum_of_residue_and_close
        (fun n hn => hdiv n (hBA hn)) hres (lt_of_not_ge hfar)⟩)
  exact (not_lt_of_ge hle) hgap

theorem weighted_fourier_real_identity {ι : Type*} {Q : ℕ} [NeZero Q]
    (A : Finset ι) (p : ι → ℝ) (w : ι → ZMod Q) (a : ZMod Q) :
    (∑ h : ZMod Q, ZMod.stdAddChar (-(h * a)) *
      ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (h * w i))).re =
      (Q : ℝ) * selectionMass A p (fun B => (∑ i ∈ B, w i) = a) := by
  rw [weighted_fourier_identity]
  rw [show (Q : ℂ) = ((Q : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  congr 1
  unfold selectionMass
  apply Finset.sum_congr rfl
  intro B hB
  by_cases he : (∑ i ∈ B, w i) = a <;> simp [he]

theorem exact_subset_of_fourier_and_tail {Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) (hdiv : ∀ n ∈ A, n ∣ Q) (α : ℝ)
    (hFourier : α ≤ (∑ h : ZMod Q, ZMod.stdAddChar (-(h * (x : ZMod Q))) *
      ∏ n ∈ A, (((1 - p n : ℝ) : ℂ) + (p n : ℂ) *
        ZMod.stdAddChar (h * ((Q / n : ℕ) : ZMod Q)))).re)
    (hTail : selectionMass A p (fun B => 1 ≤ |(reciprocalSum B : ℝ) - (x : ℝ) / Q|) <
      α / (Q : ℝ)) : ∃ B ⊆ A, reciprocalSum B = (x : ℚ) / Q := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hbound : α / (Q : ℝ) ≤
      selectionMass A p (fun B => (∑ n ∈ B, ((Q / n : ℕ) : ZMod Q)) = (x : ZMod Q)) := by
    apply (div_le_iff₀ hQ).mpr
    simpa only [weighted_fourier_real_identity, mul_comm] using hFourier
  exact exact_subset_of_modular_mass_gt_far_mass A p hp hdiv (hTail.trans_le hbound)

theorem real_exp_le_quadratic {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hu
  linarith [le_abs_self (Real.exp u - 1 - u)]

theorem centered_bernoulli_exp_le (p s : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : |s| ≤ 1) :
    (1 - p) * Real.exp (-p * s) + p * Real.exp ((1 - p) * s) ≤
      Real.exp (s ^ 2 / 4) := by
  have harg (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : |a * s| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact (mul_le_mul_of_nonneg_right ha1 (abs_nonneg s)).trans (by simpa using hs)
  have hfirst : |-p * s| ≤ 1 := by simpa only [neg_mul, abs_neg] using harg p hp0 hp1
  have hsecond := harg (1 - p) (sub_nonneg.mpr hp1) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left (real_exp_le_quadratic hfirst) (sub_nonneg.mpr hp1)
  have h2 := mul_le_mul_of_nonneg_left (real_exp_le_quadratic hsecond) hp0
  have hvar : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * p - 1)]
  calc
    _ ≤ 1 + p * (1 - p) * s ^ 2 := by nlinarith only [h1, h2]
    _ ≤ 1 + s ^ 2 / 4 := by nlinarith [mul_le_mul_of_nonneg_right hvar (sq_nonneg s)]
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (s ^ 2 / 4)

theorem weighted_laplace_identity {ι : Type*}
    (A : Finset ι) (p u : ι → ℝ) :
    (∑ B ∈ A.powerset, selectionWeight A p B * Real.exp (∑ i ∈ B, u i)) =
      ∏ i ∈ A, ((1 - p i) + p i * Real.exp (u i)) := by
  classical
  symm
  calc
    _ = ∏ i ∈ A, (p i * Real.exp (u i) + (1 - p i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = ∑ B ∈ A.powerset,
        (∏ i ∈ B, p i * Real.exp (u i)) * ∏ i ∈ A \ B, (1 - p i) := Finset.prod_add _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      unfold selectionWeight
      rw [Finset.prod_mul_distrib, Real.exp_sum]
      ring

noncomputable def centeredLaplace {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ B ∈ A.powerset, selectionWeight A p B *
    Real.exp (t * ((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i))

theorem centeredLaplace_product {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (t : ℝ) :
    centeredLaplace A p v t =
      ∏ i ∈ A, ((1 - p i) * Real.exp (-t * p i * v i) +
        p i * Real.exp (t * (1 - p i) * v i)) := by
  classical
  have hterm (B : Finset ι) :
      Real.exp (t * ((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i)) =
        Real.exp (-t * ∑ i ∈ A, p i * v i) * Real.exp (∑ i ∈ B, t * v i) := by
    rw [← Real.exp_add, ← Finset.mul_sum]
    congr 1
    ring
  have hmu : -t * (∑ i ∈ A, p i * v i) = ∑ i ∈ A, -t * p i * v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold centeredLaplace
  simp_rw [hterm]
  calc
    _ = Real.exp (-t * ∑ i ∈ A, p i * v i) *
        ∑ B ∈ A.powerset, selectionWeight A p B * Real.exp (∑ i ∈ B, t * v i) := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      ring
    _ = _ := by
      rw [weighted_laplace_identity, hmu, Real.exp_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have he : Real.exp (-t * p i * v i) * Real.exp (t * v i) =
          Real.exp (t * (1 - p i) * v i) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (1 - p i) * Real.exp (-t * p i * v i) +
            p i * (Real.exp (-t * p i * v i) * Real.exp (t * v i)) := by ring
        _ = _ := by rw [he]

theorem centeredLaplace_le_exp {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (t : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (hsmall : ∀ i ∈ A, |t * v i| ≤ 1) :
    centeredLaplace A p v t ≤ Real.exp ((t ^ 2 / 4) * ∑ i ∈ A, (v i) ^ 2) := by
  rw [centeredLaplace_product]
  calc
    _ ≤ ∏ i ∈ A, Real.exp ((t * v i) ^ 2 / 4) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hp i hi).2) (Real.exp_pos _).le)
          (mul_nonneg (hp i hi).1 (Real.exp_pos _).le)
      · intro i hi
        have hfirst : -p i * (t * v i) = -t * p i * v i := by ring
        have hsecond : (1 - p i) * (t * v i) = t * (1 - p i) * v i := by ring
        simpa only [hfirst, hsecond] using centered_bernoulli_exp_le (p i) (t * v i)
          (hp i hi).1 (hp i hi).2 (hsmall i hi)
    _ = _ := by
      rw [← Real.exp_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem selectionMass_union_le {ι : Type*} (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (E F : Finset ι → Prop) :
    selectionMass A p (fun B => E B ∨ F B) ≤ selectionMass A p E + selectionMass A p F := by
  classical
  unfold selectionMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro B hB
  have hw := selectionWeight_nonneg A p hp (Finset.mem_powerset.mp hB)
  by_cases he : E B <;> by_cases hf : F B <;> simp [he, hf]
  linarith

theorem selectionMass_chernoff {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (t ε : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (ht : 0 ≤ t) :
    selectionMass A p (fun B => ε ≤ (∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) ≤
      Real.exp (-t * ε) * centeredLaplace A p v t := by
  classical
  unfold selectionMass centeredLaplace
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hw := selectionWeight_nonneg A p hp (Finset.mem_powerset.mp hB)
  by_cases he : ε ≤ (∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i
  · rw [ite_eq_left he]
    have hpos : 0 ≤ -t * ε + t * ((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr he)]
    have hExp : 1 ≤ Real.exp (-t * ε) *
        Real.exp (t * ((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i)) := by
      rw [← Real.exp_add]
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hpos
    have hh := mul_le_mul_of_nonneg_left hExp hw
    simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using hh
  · rw [ite_eq_right he]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hw (Real.exp_pos _).le)

theorem centeredLaplace_uniform {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (M N : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (hM : 0 < M) (hN : 0 < N)
    (hMN : M ≤ N) (hcard : (A.card : ℝ) ≤ N) (hv : ∀ i ∈ A, |v i| ≤ 1 / M) :
    centeredLaplace A p v (M ^ 2 / N) ≤ Real.exp ((M ^ 2 / N) / 4) := by
  let t := M ^ 2 / N
  have ht : 0 ≤ t := div_nonneg (sq_nonneg M) hN.le
  have hsmall : ∀ i ∈ A, |t * v i| ≤ 1 := by
    intro i hi
    rw [abs_mul, abs_of_nonneg ht]
    calc
      _ ≤ t * (1 / M) := mul_le_mul_of_nonneg_left (hv i hi) ht
      _ = M / N := by dsimp [t]; field_simp [hM.ne', hN.ne']
      _ ≤ 1 := (div_le_one hN).mpr hMN
  have hsquares : (∑ i ∈ A, (v i) ^ 2) ≤ N * (1 / M) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ A, (1 / M) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hsq := (sq_le_sq₀ (abs_nonneg (v i)) (div_nonneg zero_le_one hM.le)).mpr (hv i hi)
        simpa only [sq_abs] using hsq
      _ = (A.card : ℝ) * (1 / M) ^ 2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  have hconst : (t ^ 2 / 4) * (N * (1 / M) ^ 2) = t / 4 := by
    dsimp [t]
    field_simp [hM.ne', hN.ne']
  calc
    _ ≤ Real.exp ((t ^ 2 / 4) * ∑ i ∈ A, (v i) ^ 2) :=
      centeredLaplace_le_exp A p v t hp hsmall
    _ ≤ Real.exp ((t ^ 2 / 4) * (N * (1 / M) ^ 2)) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hsquares (by positivity))
    _ = _ := by rw [hconst]

theorem selectionMass_upper_uniform {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (M N : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (hM : 0 < M) (hN : 0 < N)
    (hMN : M ≤ N) (hcard : (A.card : ℝ) ≤ N) (hv : ∀ i ∈ A, |v i| ≤ 1 / M) :
    selectionMass A p (fun B => 1 ≤ (∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) ≤
      Real.exp (-(M ^ 2 / N) / 2) := by
  let t := M ^ 2 / N
  have ht : 0 ≤ t := div_nonneg (sq_nonneg M) hN.le
  have hMGF := centeredLaplace_uniform A p v M N hp hM hN hMN hcard hv
  calc
    _ ≤ Real.exp (-t * 1) * centeredLaplace A p v t := selectionMass_chernoff A p v t 1 hp ht
    _ ≤ Real.exp (-t) * Real.exp (t / 4) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hMGF (Real.exp_pos (-t)).le
    _ = Real.exp (-t + t / 4) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem selectionMass_abs_uniform {ι : Type*} (A : Finset ι) (p v : ι → ℝ) (M N : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (hM : 0 < M) (hN : 0 < N)
    (hMN : M ≤ N) (hcard : (A.card : ℝ) ≤ N) (hv : ∀ i ∈ A, |v i| ≤ 1 / M) :
    selectionMass A p (fun B => 1 ≤ |(∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i|) ≤
      2 * Real.exp (-(M ^ 2 / N) / 2) := by
  have hneg (B : Finset ι) :
      (∑ i ∈ B, -(v i)) - (∑ i ∈ A, p i * -(v i)) =
        -((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) := by
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  have hUpper := selectionMass_upper_uniform A p v M N hp hM hN hMN hcard hv
  have hLower : selectionMass A p
      (fun B => 1 ≤ -((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i)) ≤
        Real.exp (-(M ^ 2 / N) / 2) := by
    simpa only [hneg] using selectionMass_upper_uniform A p (fun i => -(v i)) M N
      hp hM hN hMN hcard (fun i hi => by simpa only [abs_neg] using hv i hi)
  have hcontain := selectionMass_mono A p hp
    (fun B => 1 ≤ |(∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i|)
    (fun B => (1 ≤ (∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) ∨
      (1 ≤ -((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i))) (by
      intro B hBA hfar
      rcases le_total 0 ((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) with hpos | hnonpos
      · exact Or.inl (by rwa [abs_of_nonneg hpos] at hfar)
      · exact Or.inr (by rwa [abs_of_nonpos hnonpos] at hfar))
  calc
    _ ≤ selectionMass A p (fun B => 1 ≤ (∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i) +
        selectionMass A p (fun B => 1 ≤ -((∑ i ∈ B, v i) - ∑ i ∈ A, p i * v i)) :=
      hcontain.trans (selectionMass_union_le A p hp _ _)
    _ ≤ Real.exp (-(M ^ 2 / N) / 2) + Real.exp (-(M ^ 2 / N) / 2) := add_le_add hUpper hLower
    _ = _ := by ring

theorem reciprocal_selection_tail {N Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (M : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1)
    (hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q) :
    selectionMass A p (fun B => 1 ≤ |(reciprocalSum B : ℝ) - (x : ℝ) / Q|) ≤
      2 * Real.exp (-(M ^ 2 / N) / 2) := by
  have hcard : (A.card : ℝ) ≤ N := by
    exact_mod_cast (show A.card ≤ N by simpa using Finset.card_le_card hA)
  have hv : ∀ n ∈ A, |(1 : ℝ) / n| ≤ 1 / M := by
    intro n hn
    have hnpos : (0 : ℝ) < n := hM.trans_le (hmin n hn)
    rw [abs_of_nonneg (div_nonneg zero_le_one hnpos.le)]
    exact (div_le_div_iff₀ hnpos hM).mpr (by simpa using hmin n hn)
  have htail := selectionMass_abs_uniform A p (fun n => (1 : ℝ) / n) M (N : ℝ)
    hp hM (by exact_mod_cast hN) hMN hcard hv
  simpa only [← reciprocalSum_real, mul_one_div, hExpected] using htail

noncomputable def fourierValue {ι : Type*} {Q : ℕ} [NeZero Q]
    (A : Finset ι) (p : ι → ℝ) (w : ι → ZMod Q) (a : ZMod Q) : ℂ :=
  ∑ h : ZMod Q, ZMod.stdAddChar (-(h * a)) *
    ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (h * w i))

theorem exact_subset_of_fourier_interval {N Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (M : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) (hdiv : ∀ n ∈ A, n ∣ Q)
    (hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q)
    (hFourier : (1 : ℝ) / 2 ≤
      (fourierValue A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q)).re)
    (hQgrowth : (Q : ℝ) ≤ Real.exp ((M ^ 2 / N) / 4))
    (hlarge : Real.log 4 < (M ^ 2 / N) / 4) :
    ∃ B ⊆ A, reciprocalSum B = (x : ℚ) / Q := by
  let a := M ^ 2 / (N : ℝ)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hsmallExp : Real.exp (-a / 4) < 1 / 4 := by
    calc
      _ < Real.exp (-Real.log 4) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num
  have hTailSmall : 2 * Real.exp (-a / 2) < ((1 : ℝ) / 2) / Q := by
    apply (lt_div_iff₀ hQpos).mpr
    calc
      _ ≤ (2 * Real.exp (-a / 2)) * Real.exp (a / 4) :=
        mul_le_mul_of_nonneg_left hQgrowth (by positivity)
      _ = 2 * Real.exp (-a / 4) := by
        rw [mul_assoc, ← Real.exp_add, show -a / 2 + a / 4 = -a / 4 by ring]
      _ < _ := by linarith
  apply exact_subset_of_fourier_and_tail A p hp hdiv (1 / 2) hFourier
  exact (reciprocal_selection_tail A p M hN hM hMN hA hmin hp hExpected).trans_lt hTailSmall

theorem complex_exp_quadratic_remainder (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ ≤ Real.exp 1 * ‖z‖ ^ 3 := by
  have hpoly : (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) = 1 + z + z ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  calc
    _ = ‖Complex.exp z - ∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)‖ := by rw [hpoly]
    _ ≤ ‖z‖ ^ 3 * Real.exp ‖z‖ := Complex.norm_exp_sub_sum_le_norm_mul_exp z 3
    _ ≤ ‖z‖ ^ 3 * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (by positivity)
    _ = _ := mul_comm _ _

noncomputable def centeredBernoulli (p θ : ℝ) : ℂ :=
  ((1 - p : ℝ) : ℂ) * Complex.exp ((-p * θ : ℝ) * Complex.I) +
    (p : ℂ) * Complex.exp (((1 - p) * θ : ℝ) * Complex.I)

theorem norm_imaginary (u : ℝ) : ‖(u : ℂ) * Complex.I‖ = |u| := by
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem centeredBernoulli_quadratic_remainder (p θ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hθ : |θ| ≤ 1) :
    ‖centeredBernoulli p θ - ((1 - p * (1 - p) * θ ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      Real.exp 1 * |θ| ^ 3 := by
  let z₁ : ℂ := (-p * θ : ℝ) * Complex.I
  let z₂ : ℂ := ((1 - p) * θ : ℝ) * Complex.I
  have hn₁ : ‖z₁‖ ≤ |θ| := by
    rw [norm_imaginary, abs_mul, abs_neg, abs_of_nonneg hp0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 (abs_nonneg θ)
  have hn₂ : ‖z₂‖ ≤ |θ| := by
    rw [norm_imaginary, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp1)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show 1 - p ≤ 1 by linarith) (abs_nonneg θ)
  have hr₁ : ‖Complex.exp z₁ - (1 + z₁ + z₁ ^ 2 / 2)‖ ≤ Real.exp 1 * |θ| ^ 3 :=
    (complex_exp_quadratic_remainder z₁ (hn₁.trans hθ)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn₁ 3) (Real.exp_pos 1).le)
  have hr₂ : ‖Complex.exp z₂ - (1 + z₂ + z₂ ^ 2 / 2)‖ ≤ Real.exp 1 * |θ| ^ 3 :=
    (complex_exp_quadratic_remainder z₂ (hn₂.trans hθ)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn₂ 3) (Real.exp_pos 1).le)
  have hpoly : ((1 - p : ℝ) : ℂ) * (1 + z₁ + z₁ ^ 2 / 2) +
      (p : ℂ) * (1 + z₂ + z₂ ^ 2 / 2) = ((1 - p * (1 - p) * θ ^ 2 / 2 : ℝ) : ℂ) := by
    dsimp [z₁, z₂]
    push_cast
    simp only [mul_pow, Complex.I_sq]
    ring
  have hdec : centeredBernoulli p θ - ((1 - p * (1 - p) * θ ^ 2 / 2 : ℝ) : ℂ) =
      ((1 - p : ℝ) : ℂ) * (Complex.exp z₁ - (1 + z₁ + z₁ ^ 2 / 2)) +
        (p : ℂ) * (Complex.exp z₂ - (1 + z₂ + z₂ ^ 2 / 2)) := by
    change ((1 - p : ℝ) : ℂ) * Complex.exp z₁ + (p : ℂ) * Complex.exp z₂ - _ = _
    rw [← hpoly]
    ring
  rw [hdec]
  calc
    _ ≤ ‖((1 - p : ℝ) : ℂ) * (Complex.exp z₁ - (1 + z₁ + z₁ ^ 2 / 2))‖ +
        ‖(p : ℂ) * (Complex.exp z₂ - (1 + z₂ + z₂ ^ 2 / 2))‖ := norm_add_le _ _
    _ = (1 - p) * ‖Complex.exp z₁ - (1 + z₁ + z₁ ^ 2 / 2)‖ +
        p * ‖Complex.exp z₂ - (1 + z₂ + z₂ ^ 2 / 2)‖ := by
      rw [norm_mul, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0,
        abs_of_nonneg (sub_nonneg.mpr hp1)]
    _ ≤ (1 - p) * (Real.exp 1 * |θ| ^ 3) + p * (Real.exp 1 * |θ| ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_left hr₁ (sub_nonneg.mpr hp1))
        (mul_le_mul_of_nonneg_left hr₂ hp0)
    _ = _ := by ring

theorem centeredBernoulli_base_lower (p θ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hθ : |θ| ≤ 1) :
    1 / 2 ≤ 1 - p * (1 - p) * θ ^ 2 / 2 := by
  have hvar0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hvar1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * p - 1)]
  have hθsq : θ ^ 2 ≤ 1 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hθ
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hθsq hvar0
  nlinarith

theorem norm_prod_sub_one_le_exp_sum {ι : Type*} (A : Finset ι) (z : ι → ℂ) (ε : ι → ℝ)
    (hε : ∀ i ∈ A, 0 ≤ ε i) (herror : ∀ i ∈ A, ‖z i - 1‖ ≤ ε i) :
    ‖(∏ i ∈ A, z i) - 1‖ ≤ Real.exp (∑ i ∈ A, ε i) - 1 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
      have hiε := hε i (Finset.mem_insert_self i A)
      have hir := herror i (Finset.mem_insert_self i A)
      have hAε := fun j hj => hε j (Finset.mem_insert_of_mem hj)
      have hAr := fun j hj => herror j (Finset.mem_insert_of_mem hj)
      have hprod := ih hAε hAr
      have hzi : ‖z i‖ ≤ 1 + ε i := by
        calc
          _ = ‖(z i - 1) + 1‖ := by ring_nf
          _ ≤ ‖z i - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ _ := by simpa only [norm_one, add_comm] using add_le_add_right hir 1
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        _ = ‖z i * ((∏ j ∈ A, z j) - 1) + (z i - 1)‖ := by congr 1; ring
        _ ≤ ‖z i * ((∏ j ∈ A, z j) - 1)‖ + ‖z i - 1‖ := norm_add_le _ _
        _ ≤ (1 + ε i) * ‖(∏ j ∈ A, z j) - 1‖ + ε i := by
          rw [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hzi (norm_nonneg _)) hir
        _ ≤ (1 + ε i) * (Real.exp (∑ j ∈ A, ε j) - 1) + ε i := by
          simpa only [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ 1 + ε i)) (ε i)
        _ = (1 + ε i) * Real.exp (∑ j ∈ A, ε j) - 1 := by ring
        _ ≤ Real.exp (ε i) * Real.exp (∑ j ∈ A, ε j) - 1 := by
          have hh : 1 + ε i ≤ Real.exp (ε i) := by simpa only [add_comm] using Real.add_one_le_exp (ε i)
          exact sub_le_sub_right (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le) 1
        _ = _ := by rw [Real.exp_add]

theorem re_prod_nonneg_of_small_errors {ι : Type*} (A : Finset ι) (z : ι → ℂ) (ε : ι → ℝ)
    (hε : ∀ i ∈ A, 0 ≤ ε i) (herror : ∀ i ∈ A, ‖z i - 1‖ ≤ ε i)
    (hsum : (∑ i ∈ A, ε i) ≤ Real.log (3 / 2)) : 0 ≤ (∏ i ∈ A, z i).re := by
  have hn := norm_prod_sub_one_le_exp_sum A z ε hε herror
  have he : Real.exp (∑ i ∈ A, ε i) ≤ 3 / 2 := by
    calc
      _ ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr hsum
      _ = _ := Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)
  have hre := Complex.re_le_norm (-((∏ i ∈ A, z i) - 1))
  simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, norm_neg] at hre
  linarith

theorem re_prod_nonneg_of_relative_errors {ι : Type*}
    (A : Finset ι) (f : ι → ℂ) (a ε : ι → ℝ)
    (ha : ∀ i ∈ A, 0 < a i) (hε : ∀ i ∈ A, 0 ≤ ε i)
    (herror : ∀ i ∈ A, ‖f i - (a i : ℂ)‖ ≤ ε i * a i)
    (hsum : (∑ i ∈ A, ε i) ≤ Real.log (3 / 2)) :
    0 ≤ (∏ i ∈ A, f i).re := by
  let z : ι → ℂ := fun i => f i / (a i : ℂ)
  have hz : ∀ i ∈ A, ‖z i - 1‖ ≤ ε i := by
    intro i hi
    have hai := ha i hi
    have hane : (a i : ℂ) ≠ 0 := by exact_mod_cast hai.ne'
    have hdiff : z i - 1 = (f i - (a i : ℂ)) / (a i : ℂ) := by
      dsimp [z]
      field_simp [hane]
    rw [hdiff, norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hai]
    exact (div_le_iff₀ hai).mpr (herror i hi)
  have hzRe := re_prod_nonneg_of_small_errors A z ε hε hz hsum
  have hscale : (∏ i ∈ A, f i) = ((∏ i ∈ A, a i : ℝ) : ℂ) * ∏ i ∈ A, z i := by
    calc
      _ = ∏ i ∈ A, ((a i : ℂ) * z i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hane : (a i : ℂ) ≠ 0 := by exact_mod_cast (ha i hi).ne'
        dsimp [z]
        field_simp [hane]
      _ = (∏ i ∈ A, (a i : ℂ)) * ∏ i ∈ A, z i := Finset.prod_mul_distrib
      _ = _ := by simp
  rw [hscale, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (Finset.prod_nonneg (fun i hi => (ha i hi).le)) hzRe

theorem centered_major_re_nonneg {ι : Type*} (A : Finset ι) (p θ : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (hθ : ∀ i ∈ A, |θ i| ≤ 1)
    (hbudget : (2 * Real.exp 1) * (∑ i ∈ A, |θ i| ^ 3) ≤ Real.log (3 / 2)) :
    0 ≤ (∏ i ∈ A, centeredBernoulli (p i) (θ i)).re := by
  let a := fun i => 1 - p i * (1 - p i) * (θ i) ^ 2 / 2
  let ε := fun i => (2 * Real.exp 1) * |θ i| ^ 3
  have ha : ∀ i ∈ A, 1 / 2 ≤ a i := by
    intro i hi
    exact centeredBernoulli_base_lower (p i) (θ i) (hp i hi).1 (hp i hi).2 (hθ i hi)
  apply re_prod_nonneg_of_relative_errors A (fun i => centeredBernoulli (p i) (θ i)) a ε
  · intro i hi
    have := ha i hi
    linarith
  · intro i hi
    dsimp [ε]
    positivity
  · intro i hi
    have hr := centeredBernoulli_quadratic_remainder (p i) (θ i) (hp i hi).1 (hp i hi).2 (hθ i hi)
    have heps : 0 ≤ ε i := by dsimp [ε]; positivity
    have hh := mul_le_mul_of_nonneg_left (ha i hi) heps
    have hbound : Real.exp 1 * |θ i| ^ 3 ≤ ε i * a i := by
      dsimp [ε] at hh ⊢
      nlinarith only [hh]
    exact hr.trans hbound
  · simpa only [ε, ← Finset.mul_sum] using hbudget

theorem centered_frequency_re_nonneg {ι : Type*}
    (A : Finset ι) (p v : ι → ℝ) (h H M N : ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i ∧ p i ≤ 1) (hM : 0 < M) (hH : 0 ≤ H)
    (hcard : (A.card : ℝ) ≤ N) (hv : ∀ i ∈ A, |v i| ≤ 1 / M) (hh : |h| ≤ H)
    (hsmall : 2 * Real.pi * H / M ≤ 1)
    (hbudget : (2 * Real.exp 1) * (N * (2 * Real.pi * H / M) ^ 3) ≤ Real.log (3 / 2)) :
    0 ≤ (∏ i ∈ A, centeredBernoulli (p i) (2 * Real.pi * h * v i)).re := by
  let b := 2 * Real.pi * H / M
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hθbound : ∀ i ∈ A, |2 * Real.pi * h * v i| ≤ b := by
    intro i hi
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    calc
      _ ≤ (2 * Real.pi * H) * (1 / M) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity)) (hv i hi)
          (abs_nonneg _) (by positivity)
      _ = _ := by dsimp [b]; ring
  apply centered_major_re_nonneg A p (fun i => 2 * Real.pi * h * v i) hp
  · intro i hi
    exact (hθbound i hi).trans hsmall
  · have hsum : (∑ i ∈ A, |2 * Real.pi * h * v i| ^ 3) ≤ N * b ^ 3 := by
      calc
        _ ≤ ∑ i ∈ A, b ^ 3 := Finset.sum_le_sum
          (fun i hi => pow_le_pow_left₀ (abs_nonneg _) (hθbound i hi) 3)
        _ = (A.card : ℝ) * b ^ 3 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hb 3)
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hbudget

theorem centeredBernoulli_factorization (p θ : ℝ) :
    centeredBernoulli p θ = Complex.exp ((-p * θ : ℝ) * Complex.I) *
      (((1 - p : ℝ) : ℂ) + (p : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  have he : Complex.exp ((-p * θ : ℝ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp (((1 - p) * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  symm
  calc
    _ = ((1 - p : ℝ) : ℂ) * Complex.exp ((-p * θ : ℝ) * Complex.I) +
        (p : ℂ) * (Complex.exp ((-p * θ : ℝ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [he]; rfl

theorem centeredBernoulli_product_factorization {ι : Type*}
    (A : Finset ι) (p θ : ι → ℝ) :
    (∏ i ∈ A, centeredBernoulli (p i) (θ i)) =
      Complex.exp ((-(∑ i ∈ A, p i * θ i) : ℝ) * Complex.I) *
        ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)) := by
  simp_rw [centeredBernoulli_factorization]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [neg_mul, ← Finset.sum_mul, Finset.sum_neg_distrib]

theorem character_reciprocal {Q n : ℕ} [NeZero Q]
    (h : ℤ) (hn : 0 < n) (hdiv : n ∣ Q) :
    ZMod.stdAddChar ((h : ZMod Q) * ((Q / n : ℕ) : ZMod Q)) =
      Complex.exp ((2 * Real.pi * (h : ℝ) / n : ℝ) * Complex.I) := by
  have hcast : (h : ZMod Q) * ((Q / n : ℕ) : ZMod Q) =
      ((h * Int.ofNat (Q / n) : ℤ) : ZMod Q) := by
    rw [Int.cast_mul, Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [hcast, ZMod.stdAddChar_coe]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hQC : (Q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hmul : ((Q / n : ℕ) : ℂ) * (n : ℂ) = (Q : ℂ) := by
    exact_mod_cast Nat.div_mul_cancel hdiv
  have hquot : ((Q / n : ℕ) : ℂ) = (Q : ℂ) / (n : ℂ) := (eq_div_iff hnC).mpr hmul
  congr 1
  simp only [Int.cast_mul, Int.ofNat_eq_natCast, Int.cast_natCast, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    Complex.ofReal_natCast]
  rw [hquot]
  field_simp [hQC, hnC]

theorem character_target_phase {Q x : ℕ} [NeZero Q] (h : ℤ) :
    ZMod.stdAddChar (-((h : ZMod Q) * (x : ZMod Q))) =
      Complex.exp ((-(2 * Real.pi * (h : ℝ) * x / Q) : ℝ) * Complex.I) := by
  have hcast : -((h : ZMod Q) * (x : ZMod Q)) = ((-h * (x : ℤ) : ℤ) : ZMod Q) := by
    push_cast
    ring
  rw [hcast, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

noncomputable def fourierTerm {ι : Type*} {Q : ℕ} [NeZero Q]
    (A : Finset ι) (p : ι → ℝ) (w : ι → ZMod Q) (a h : ZMod Q) : ℂ :=
  ZMod.stdAddChar (-(h * a)) *
    ∏ i ∈ A, (((1 - p i : ℝ) : ℂ) + (p i : ℂ) * ZMod.stdAddChar (h * w i))

theorem fourierTerm_eq_centered {Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ)
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ Q)
    (hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q) :
    fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) (h : ZMod Q) =
      ∏ n ∈ A, centeredBernoulli (p n) (2 * Real.pi * (h : ℝ) / n) := by
  have hsum : (∑ n ∈ A, p n * (2 * Real.pi * (h : ℝ) / n)) =
      2 * Real.pi * (h : ℝ) * x / Q := by
    calc
      _ = (2 * Real.pi * (h : ℝ)) * ∑ n ∈ A, p n / n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by rw [hExpected]; ring
  unfold fourierTerm
  rw [centeredBernoulli_product_factorization, hsum, character_target_phase]
  congr 1
  apply Finset.prod_congr rfl
  intro n hn
  rw [character_reciprocal h (hpos n hn) (hdiv n hn)]

theorem fourierTerm_re_nonneg_of_small_frequency {Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (H M N : ℝ)
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ Q)
    (hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) (hM : 0 < M) (hH : 0 ≤ H)
    (hcard : (A.card : ℝ) ≤ N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ)) (hh : |(h : ℝ)| ≤ H)
    (hsmall : 2 * Real.pi * H / M ≤ 1)
    (hbudget : (2 * Real.exp 1) * (N * (2 * Real.pi * H / M) ^ 3) ≤ Real.log (3 / 2)) :
    0 ≤ (fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) (h : ZMod Q)).re := by
  rw [fourierTerm_eq_centered A p h hpos hdiv hExpected]
  have hv : ∀ n ∈ A, |(1 : ℝ) / n| ≤ 1 / M := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hpos n hn
    rw [abs_of_nonneg (div_nonneg zero_le_one hnR.le)]
    exact (div_le_div_iff₀ hnR hM).mpr (by simpa using hmin n hn)
  simpa only [mul_one_div] using centered_frequency_re_nonneg A p (fun n => (1 : ℝ) / n)
    (h : ℝ) H M N hp hM hH hcard hv hh hsmall hbudget

theorem fourierTerm_norm_small_frequency {Q x N : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (M τ : ℝ)
    (hN : 0 < N) (_hM : 0 < M)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, n ∣ Q) (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1)
    (hτ : 0 ≤ τ) (hvar : ∀ n ∈ A, τ ≤ p n * (1 - p n))
    (hh : |(h : ℝ)| ≤ M / 2) :
    ‖fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) (h : ZMod Q)‖ ≤
      Real.exp (-(8 * τ * A.card * (h : ℝ) ^ 2 / (N : ℝ) ^ 2)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hphase : ∀ n ∈ A, |(h : ℝ) / n| ≤ 1 / 2 := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hpos n hn
    rw [abs_div, abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    linarith [hmin n hn]
  have hlocal : ∀ n ∈ A,
      ‖((1 - p n : ℝ) : ℂ) + (p n : ℂ) *
        ZMod.stdAddChar ((h : ZMod Q) * ((Q / n : ℕ) : ZMod Q))‖ ≤
      Real.exp (-(8 * τ * (h : ℝ) ^ 2 / (N : ℝ) ^ 2)) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hpos n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp (hA hn)).2
    have hratio : (h : ℝ) ^ 2 / (N : ℝ) ^ 2 ≤ ((h : ℝ) / n) ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hnR)
        (pow_le_pow_left₀ hnR.le hnN 2)
    have hdecay : 8 * τ * (h : ℝ) ^ 2 / (N : ℝ) ^ 2 ≤
        8 * p n * (1 - p n) * ((h : ℝ) / n) ^ 2 := by
      calc
        _ = (8 * τ) * ((h : ℝ) ^ 2 / (N : ℝ) ^ 2) := by ring
        _ ≤ (8 * τ) * ((h : ℝ) / n) ^ 2 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (hvar n hn) (sq_nonneg ((h : ℝ) / n))]
    rw [character_reciprocal h (hpos n hn) (hdiv n hn)]
    have he : (2 * Real.pi * (h : ℝ) / n : ℝ) = 2 * Real.pi * ((h : ℝ) / n) := by ring
    rw [he]
    exact (bernoulli_phase_norm_le_exp (p n) ((h : ℝ) / n)
      (hp n hn).1 (hp n hn).2 (hphase n hn)).trans (Real.exp_le_exp.mpr (neg_le_neg hdecay))
  unfold fourierTerm
  rw [norm_mul, AddChar.norm_apply, one_mul]
  calc
    _ = ∏ n ∈ A, ‖((1 - p n : ℝ) : ℂ) + (p n : ℂ) *
        ZMod.stdAddChar ((h : ZMod Q) * ((Q / n : ℕ) : ZMod Q))‖ := norm_prod _ _
    _ ≤ ∏ _n ∈ A, Real.exp (-(8 * τ * (h : ℝ) ^ 2 / (N : ℝ) ^ 2)) :=
      Finset.prod_le_prod₀ (fun n hn => norm_nonneg _) hlocal
    _ = _ := by
      rw [← Real.exp_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      ring

theorem bounded_frequency_card {Q N : ℕ} [NeZero Q] (S : Finset (ZMod Q))
    (hbound : ∀ h ∈ S, |(h.valMinAbs : ℝ)| ≤ N) : S.card ≤ 2 * N + 1 := by
  classical
  have hsub : S.image ZMod.valMinAbs ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro a ha
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ha
    have habs : |h.valMinAbs| ≤ (N : ℤ) := by exact_mod_cast hbound h hh
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S ZMod.injective_valMinAbs] at hc
  have heq : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  rwa [heq] at hc

theorem fourier_middle_sum_norm {Q x N : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (S : Finset (ZMod Q)) (H M τ : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) (hH : 0 ≤ H)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, n ∣ Q) (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1)
    (hτ : 0 ≤ τ) (hvar : ∀ n ∈ A, τ ≤ p n * (1 - p n))
    (hfreq : ∀ h ∈ S, H ≤ |(h.valMinAbs : ℝ)| ∧ |(h.valMinAbs : ℝ)| ≤ M / 2) :
    ‖∑ h ∈ S, fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ ≤
      (2 * N + 1 : ℝ) * Real.exp (-(8 * τ * A.card * H ^ 2 / (N : ℝ) ^ 2)) := by
  have hterm : ∀ h ∈ S,
      ‖fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ ≤
        Real.exp (-(8 * τ * A.card * H ^ 2 / (N : ℝ) ^ 2)) := by
    intro h hh
    have hb := fourierTerm_norm_small_frequency (x := x) A p h.valMinAbs M τ
      hN hM hA hmin hdiv hp hτ hvar (hfreq h hh).2
    rw [ZMod.coe_valMinAbs] at hb
    have hsq : H ^ 2 ≤ (h.valMinAbs : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hH (hfreq h hh).1 2
    have hscale : 0 ≤ 8 * τ * (A.card : ℝ) / (N : ℝ) ^ 2 := by positivity
    apply hb.trans
    apply Real.exp_le_exp.mpr
    have hc := mul_le_mul_of_nonneg_left hsq hscale
    convert neg_le_neg hc using 1 <;> ring
  have hcard : (S.card : ℝ) ≤ 2 * N + 1 := by
    exact_mod_cast bounded_frequency_card S (fun h hh => by linarith [(hfreq h hh).2])
  calc
    _ ≤ ∑ h ∈ S, ‖fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ S, Real.exp (-(8 * τ * A.card * H ^ 2 / (N : ℝ) ^ 2)) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * Real.exp (-(8 * τ * A.card * H ^ 2 / (N : ℝ) ^ 2)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le

theorem finite_three_arc_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℂ) (zero : ι) (L T U : Finset ι) (a b : ℝ)
    (hz : zero ∈ L) (hf : f zero = 1)
    (hcover : ∀ i, (if i ∈ L then f i else 0) +
      (if i ∈ T then f i else 0) + (if i ∈ U then f i else 0) = f i)
    (hL : ∀ i ∈ L, 0 ≤ (f i).re)
    (hT : ‖∑ i ∈ T, f i‖ ≤ a) (hU : ‖∑ i ∈ U, f i‖ ≤ b) :
    1 - a - b ≤ (∑ i, f i).re := by
  classical
  have hsplit : (∑ i, f i) = (∑ i ∈ L, f i) + (∑ i ∈ T, f i) + ∑ i ∈ U, f i := by
    have hsum (V : Finset ι) : (∑ i ∈ V, f i) = ∑ i, if i ∈ V then f i else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hsum L, hsum T, hsum U, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => (hcover i).symm)
  have hlo : (1 : ℝ) ≤ (∑ i ∈ L, f i).re := by
    rw [Complex.re_sum]
    have hh := Finset.single_le_sum hL hz
    simpa only [hf, Complex.one_re] using hh
  have htre : -a ≤ (∑ i ∈ T, f i).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm (∑ i ∈ T, f i))).1
    linarith
  have hure : -b ≤ (∑ i ∈ U, f i).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm (∑ i ∈ U, f i))).1
    linarith
  rw [hsplit, Complex.add_re, Complex.add_re]
  linarith

theorem fourier_lower_bound_of_large_frequency_bound {Q x N : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (H M τ : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) (hH : 0 ≤ H) (hHM : H ≤ M / 2)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, n ∣ Q) (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1)
    (hτ : 0 ≤ τ) (hvar : ∀ n ∈ A, τ ≤ p n * (1 - p n))
    (hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q)
    (hsmall : 2 * Real.pi * H / M ≤ 1)
    (hbudget : (2 * Real.exp 1) * (N * (2 * Real.pi * H / M) ^ 3) ≤ Real.log (3 / 2))
    (hdecay : (2 * N + 1 : ℝ) * Real.exp (-(8 * τ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 4)
    (hlarge : ‖∑ h ∈ Finset.univ.filter (fun h : ZMod Q => M / 2 < |(h.valMinAbs : ℝ)|),
      fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ ≤ 1 / 4) :
    (1 : ℝ) / 2 ≤ (fourierValue A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q)).re := by
  classical
  let f := fun h : ZMod Q => fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h
  let L := Finset.univ.filter (fun h : ZMod Q => |(h.valMinAbs : ℝ)| ≤ H)
  let T := Finset.univ.filter (fun h : ZMod Q => H < |(h.valMinAbs : ℝ)| ∧ |(h.valMinAbs : ℝ)| ≤ M / 2)
  let U := Finset.univ.filter (fun h : ZMod Q => M / 2 < |(h.valMinAbs : ℝ)|)
  have hz : (0 : ZMod Q) ∈ L := by simp [L, hH]
  have hf : f 0 = 1 := by
    dsimp [f, fourierTerm]
    simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    have hprod : (∏ n ∈ A, (((1 - p n : ℝ) : ℂ) + (p n : ℂ))) = 1 := by
      apply Finset.prod_eq_one
      intro n hn
      push_cast
      ring
    simpa only [one_mul] using hprod
  have hcover : ∀ h, (if h ∈ L then f h else 0) +
      (if h ∈ T then f h else 0) + (if h ∈ U then f h else 0) = f h := by
    intro h
    by_cases hlo : |(h.valMinAbs : ℝ)| ≤ H
    · have hmid : |(h.valMinAbs : ℝ)| ≤ M / 2 := hlo.trans hHM
      simp [L, T, U, hlo, hmid, not_lt.mpr hlo, not_lt.mpr hmid]
    · have hhlo := lt_of_not_ge hlo
      by_cases hmid : |(h.valMinAbs : ℝ)| ≤ M / 2
      · simp [L, T, U, hlo, hmid, hhlo, not_lt.mpr hmid]
      · simp [L, T, U, hlo, hmid, lt_of_not_ge hmid]
  have hlow : ∀ h ∈ L, 0 ≤ (f h).re := by
    intro h hh
    have hb : |(h.valMinAbs : ℝ)| ≤ H := (Finset.mem_filter.mp hh).2
    have hc := fourierTerm_re_nonneg_of_small_frequency A p h.valMinAbs H M N
      (fun n hn => (Finset.mem_Icc.mp (hA hn)).1) hdiv hExpected hp hM hH
      (by exact_mod_cast (show A.card ≤ N by simpa using Finset.card_le_card hA))
      hmin hb hsmall hbudget
    simpa only [ZMod.coe_valMinAbs] using hc
  have hmiddle : ‖∑ h ∈ T, f h‖ ≤ 1 / 4 := by
    apply (fourier_middle_sum_norm A p T H M τ hN hM hMN hH hA hmin hdiv hp hτ hvar ?_).trans hdecay
    intro h hh
    have ht := (Finset.mem_filter.mp hh).2
    exact ⟨ht.1.le, ht.2⟩
  have hresult := finite_three_arc_lower_bound f 0 L T U (1 / 4) (1 / 4)
    hz hf hcover hlow hmiddle hlarge
  norm_num only [show (1 : ℝ) - 1 / 4 - 1 / 4 = 1 / 2 by norm_num] at hresult
  exact hresult

theorem exact_subset_of_large_frequency_bound {Q x N : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (H M τ : ℝ)
    (hN : 0 < N) (hM : 0 < M) (hMN : M ≤ N) (hH : 0 ≤ H) (hHM : H ≤ M / 2)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, n ∣ Q) (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1)
    (hτ : 0 ≤ τ) (hvar : ∀ n ∈ A, τ ≤ p n * (1 - p n))
    (hExpected : (∑ n ∈ A, p n / n) = (x : ℝ) / Q)
    (hsmall : 2 * Real.pi * H / M ≤ 1)
    (hbudget : (2 * Real.exp 1) * (N * (2 * Real.pi * H / M) ^ 3) ≤ Real.log (3 / 2))
    (hdecay : (2 * N + 1 : ℝ) * Real.exp (-(8 * τ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 4)
    (hlarge : ‖∑ h ∈ Finset.univ.filter (fun h : ZMod Q => M / 2 < |(h.valMinAbs : ℝ)|),
      fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ ≤ 1 / 4)
    (hQgrowth : (Q : ℝ) ≤ Real.exp ((M ^ 2 / N) / 4))
    (hsize : Real.log 4 < (M ^ 2 / N) / 4) :
    ∃ B ⊆ A, reciprocalSum B = (x : ℚ) / Q := by
  apply exact_subset_of_fourier_interval A p M hN hM hMN hA hmin hp hdiv hExpected
    (fourier_lower_bound_of_large_frequency_bound A p H M τ hN hM hMN hH hHM
      hA hmin hdiv hp hτ hvar hExpected hsmall hbudget hdecay hlarge) hQgrowth hsize

noncomputable def balancedPhase (h : ℤ) (n : ℕ) : ℝ :=
  (((h : ZMod n).valMinAbs : ℤ) : ℝ) / n

theorem balancedPhase_abs_le (h : ℤ) {n : ℕ} (hn : 0 < n) :
    |balancedPhase h n| ≤ 1 / 2 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper : (((h : ZMod n).valMinAbs : ℤ) : ℝ) * 2 ≤ n := by
    exact_mod_cast (h : ZMod n).valMinAbs_mem_Ioc.2
  have hlower : -(n : ℝ) < (((h : ZMod n).valMinAbs : ℤ) : ℝ) * 2 := by
    exact_mod_cast (h : ZMod n).valMinAbs_mem_Ioc.1
  unfold balancedPhase
  rw [abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  rw [abs_le]
  constructor <;> linarith

theorem character_reciprocal_eq_balanced {Q n : ℕ} [NeZero Q]
    (h : ℤ) (hn : 0 < n) (hdiv : n ∣ Q) :
    ZMod.stdAddChar ((h : ZMod Q) * ((Q / n : ℕ) : ZMod Q)) =
      Complex.exp ((2 * Real.pi * balancedPhase h n : ℝ) * Complex.I) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hlocal : ZMod.stdAddChar (h : ZMod n) =
      Complex.exp ((2 * Real.pi * (h : ℝ) / n : ℝ) * Complex.I) := by
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [character_reciprocal h hn hdiv, ← hlocal]
  conv_lhs => rw [← ZMod.coe_valMinAbs (h : ZMod n)]
  rw [ZMod.stdAddChar_coe]
  congr 1
  unfold balancedPhase
  push_cast
  ring

theorem fourierTerm_norm_le_balanced_energy {Q x : ℕ} [NeZero Q]
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ)
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ Q)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) :
    ‖fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) (h : ZMod Q)‖ ≤
      Real.exp (-8 * ∑ n ∈ A, p n * (1 - p n) * balancedPhase h n ^ 2) := by
  unfold fourierTerm
  rw [norm_mul, AddChar.norm_apply, one_mul]
  have hbound : ∀ n ∈ A,
      ‖((1 - p n : ℝ) : ℂ) + (p n : ℂ) *
        ZMod.stdAddChar ((h : ZMod Q) * ((Q / n : ℕ) : ZMod Q))‖ ≤
        Real.exp (-(8 * p n * (1 - p n) * balancedPhase h n ^ 2)) := by
    intro n hn
    rw [character_reciprocal_eq_balanced h (hpos n hn) (hdiv n hn)]
    exact bernoulli_phase_norm_le_exp (p n) (balancedPhase h n)
      (hp n hn).1 (hp n hn).2 (balancedPhase_abs_le h (hpos n hn))
  have hb := norm_prod_le_exp_neg_sum A
    (fun n => ((1 - p n : ℝ) : ℂ) + (p n : ℂ) *
      ZMod.stdAddChar ((h : ZMod Q) * ((Q / n : ℕ) : ZMod Q)))
    (fun n => 8 * p n * (1 - p n) * balancedPhase h n ^ 2) hbound
  convert hb using 1
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem group_energy_double_count {ι κ : Type*} [DecidableEq ι]
    (A : Finset ι) (B : Finset κ) (G : κ → Finset ι) (w : ι → ℝ) (E L : ℝ)
    (hw : ∀ i ∈ A, 0 ≤ w i) (hG : ∀ q ∈ B, G q ⊆ A)
    (hmult : ∀ i ∈ A, ((B.filter (fun q => i ∈ G q)).card : ℝ) ≤ L)
    (henergy : ∀ q ∈ B, E ≤ ∑ i ∈ G q, w i) :
    E * B.card ≤ L * ∑ i ∈ A, w i := by
  classical
  have hsum : (∑ q ∈ B, ∑ i ∈ G q, w i) =
      ∑ i ∈ A, ((B.filter (fun q => i ∈ G q)).card : ℝ) * w i := by
    calc
      _ = ∑ q ∈ B, ∑ i ∈ A, if i ∈ G q then w i else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← Finset.sum_filter]
        congr 1
        exact (Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hG q hq))).symm
      _ = ∑ i ∈ A, ∑ q ∈ B, if i ∈ G q then w i else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_filter]
        simp
  calc
    _ = ∑ _q ∈ B, E := by simp [mul_comm]
    _ ≤ ∑ q ∈ B, ∑ i ∈ G q, w i := Finset.sum_le_sum henergy
    _ = _ := hsum
    _ ≤ ∑ i ∈ A, L * w i := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hmult i hi) (hw i hi))
    _ = _ := (Finset.mul_sum A w L).symm

theorem fourierTerm_norm_le_group_energy {Q x : ℕ} [NeZero Q] {κ : Type*}
    (A : Finset ℕ) (B : Finset κ) (G : κ → Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (E L : ℝ)
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ Q)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) (hL : 0 < L)
    (hG : ∀ q ∈ B, G q ⊆ A)
    (hmult : ∀ n ∈ A, ((B.filter (fun q => n ∈ G q)).card : ℝ) ≤ L)
    (henergy : ∀ q ∈ B, E ≤ ∑ n ∈ G q, p n * (1 - p n) * balancedPhase h n ^ 2) :
    ‖fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) (h : ZMod Q)‖ ≤
      Real.exp (-(8 * E * B.card / L)) := by
  have hcount := group_energy_double_count A B G
    (fun n => p n * (1 - p n) * balancedPhase h n ^ 2) E L
    (fun n hn => mul_nonneg (mul_nonneg (hp n hn).1 (sub_nonneg.mpr (hp n hn).2)) (sq_nonneg _))
    hG hmult henergy
  apply (fourierTerm_norm_le_balanced_energy A p h hpos hdiv hp).trans
  apply Real.exp_le_exp.mpr
  have hh : E * B.card / L ≤ ∑ n ∈ A, p n * (1 - p n) * balancedPhase h n ^ 2 :=
    (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hcount)
  convert neg_le_neg (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 8)) using 1 <;> ring

theorem clean_divisor_groups (η : ℝ) (hη : 0 ≤ η) :
    ∀ S : Finset ℕ, (∀ q ∈ S, 0 < q) → ∀ A : Finset ℕ,
      ∃ F ⊆ A,
        (∀ q ∈ S, F.filter (fun n => q ∣ n) = ∅ ∨
          η ≤ (q : ℝ) * ∑ n ∈ F.filter (fun n => q ∣ n), (1 : ℝ) / n) ∧
        (∑ n ∈ A, (1 : ℝ) / n) - (∑ n ∈ F, (1 : ℝ) / n) ≤
          η * ∑ q ∈ S, (1 : ℝ) / q := by
  classical
  intro S
  refine Finset.strongInductionOn S (fun S ih => ?_)
  · intro hS A
    let R := fun B : Finset ℕ => ∑ n ∈ B, (1 : ℝ) / n
    by_cases hrich : ∀ q ∈ S, A.filter (fun n => q ∣ n) = ∅ ∨
        η ≤ (q : ℝ) * R (A.filter (fun n => q ∣ n))
    · refine ⟨A, Finset.Subset.refl _, hrich, ?_⟩
      rw [sub_self]
      exact mul_nonneg hη (Finset.sum_nonneg (fun q hq => by positivity))
    · have hbad : ∃ q ∈ S, A.filter (fun n => q ∣ n) ≠ ∅ ∧
          (q : ℝ) * R (A.filter (fun n => q ∣ n)) < η := by
        by_contra hnone
        apply hrich
        intro q hq
        by_cases he : A.filter (fun n => q ∣ n) = ∅
        · exact Or.inl he
        · exact Or.inr (le_of_not_gt (fun hh => hnone ⟨q, hq, he, hh⟩))
      obtain ⟨q, hq, _hne, hqbad⟩ := hbad
      let G := A.filter (fun n => q ∣ n)
      have hGA : G ⊆ A := Finset.filter_subset _ _
      obtain ⟨F, hFB, hFgood, hLoss⟩ := ih (S.erase q) (Finset.erase_ssubset hq)
        (fun t ht => hS t (Finset.mem_of_mem_erase ht)) (A \ G)
      refine ⟨F, hFB.trans Finset.sdiff_subset, ?_, ?_⟩
      · intro t ht
        by_cases htq : t = q
        · left
          subst t
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro n hn
          have hnF := (Finset.mem_filter.mp hn).1
          have hnB := Finset.mem_sdiff.mp (hFB hnF)
          exact hnB.2 (Finset.mem_filter.mpr ⟨hnB.1, (Finset.mem_filter.mp hn).2⟩)
        · exact hFgood t (Finset.mem_erase.mpr ⟨htq, ht⟩)
      · have hqpos : (0 : ℝ) < q := by exact_mod_cast hS q hq
        have hqmass : R G ≤ η / q := (le_div_iff₀ hqpos).mpr (by
          simpa only [mul_comm] using hqbad.le)
        have hsplit : R (A \ G) + R G = R A := Finset.sum_sdiff hGA
        have hbudget : (∑ t ∈ S.erase q, (1 : ℝ) / t) + 1 / q =
            ∑ t ∈ S, (1 : ℝ) / t := Finset.sum_erase_add _ _ hq
        change R A - R F ≤ _
        change R (A \ G) - R F ≤ _ at hLoss
        calc
          _ = R G + (R (A \ G) - R F) := by linarith only [hsplit]
          _ ≤ η / q + η * ∑ t ∈ S.erase q, (1 : ℝ) / t := add_le_add hqmass hLoss
          _ = _ := by rw [← hbudget]; ring

theorem reciprocalSum_den_dvd_common {Q : ℕ} [NeZero Q] (A : Finset ℕ)
    (hdiv : ∀ n ∈ A, n ∣ Q) : (reciprocalSum A).den ∣ Q := by
  let U := ∑ n ∈ A, Q / n
  have hQ : (Q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hr : reciprocalSum A = (U : ℚ) / Q :=
    (eq_div_iff hQ).mpr (by simpa only [U, mul_comm] using clear_reciprocalSum hdiv)
  rw [hr]
  have hd := Rat.den_dvd (U : ℤ) (Q : ℤ)
  simp only [Rat.divInt_eq_div, Int.cast_natCast] at hd
  exact Int.natCast_dvd_natCast.mp hd

theorem exists_numerator_over_common {Q : ℕ} [NeZero Q] (r : ℚ)
    (hr : 0 ≤ r) (hdiv : r.den ∣ Q) : ∃ x : ℕ, r = (x : ℚ) / Q := by
  have hnum : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr)
  have hnumQ : (r.num.toNat : ℚ) = r.num := by exact_mod_cast hnum
  have hQ : (Q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  refine ⟨r.num.toNat * (Q / r.den), ?_⟩
  calc
    r = (r.num : ℚ) / r.den := r.num_div_den.symm
    _ = _ := by
      rw [Nat.cast_mul, hnumQ, Rat.natCast_div Q r.den hdiv]
      field_simp [hQ, hden]

theorem constant_probability_mean (A : Finset ℕ) (y : ℝ)
    (hR : 0 < (reciprocalSum A : ℝ)) :
    (∑ n ∈ A, (y / (reciprocalSum A : ℝ)) / n) = y := by
  calc
    _ = (y / (reciprocalSum A : ℝ)) * ∑ n ∈ A, (1 : ℝ) / n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by rw [← reciprocalSum_real]; field_simp [hR.ne']

theorem constant_probability_bounds (A : Finset ℕ) (y : ℝ)
    (hy : 0 < y) (hupper : y < (reciprocalSum A : ℝ)) :
    0 < y / (reciprocalSum A : ℝ) ∧ y / (reciprocalSum A : ℝ) < 1 := by
  have hR := hy.trans hupper
  exact ⟨div_pos hy hR, (div_lt_one hR).mpr hupper⟩

theorem major_angle_identity (m x : ℝ) (hx : 0 < x) :
    2 * Real.pi * x ^ (3 / 5 : ℝ) / (m * x) =
      (2 * Real.pi / m) * x ^ (-(2 / 5 : ℝ)) := by
  have hp : x ^ (3 / 5 : ℝ) / x = x ^ (-(2 / 5 : ℝ)) := by
    rw [show (-(2 / 5 : ℝ)) = (3 / 5 : ℝ) - 1 by norm_num,
      Real.rpow_sub hx, Real.rpow_one]
  calc
    _ = (2 * Real.pi / m) * (x ^ (3 / 5 : ℝ) / x) := by ring
    _ = _ := by rw [hp]

theorem major_cubic_identity (m x : ℝ) (hx : 0 < x) :
    (2 * Real.exp 1) * (x * (2 * Real.pi * x ^ (3 / 5 : ℝ) / (m * x)) ^ 3) =
      ((2 * Real.exp 1) * (2 * Real.pi / m) ^ 3) * x ^ (-(1 / 5 : ℝ)) := by
  have hp : x * (x ^ (-(2 / 5 : ℝ))) ^ 3 = x ^ (-(1 / 5 : ℝ)) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ ((-(2 / 5 : ℝ)) * 3) := by
        rw [Real.rpow_one, Real.rpow_mul hx.le]
        simp only [Real.rpow_ofNat]
      _ = _ := by rw [← Real.rpow_add hx]; norm_num
  rw [major_angle_identity m x hx, mul_pow]
  calc
    _ = ((2 * Real.exp 1) * (2 * Real.pi / m) ^ 3) *
        (x * (x ^ (-(2 / 5 : ℝ))) ^ 3) := by ring
    _ = _ := by rw [hp]

theorem tendsto_major_angle (m : ℝ) :
    Tendsto (fun x : ℝ => 2 * Real.pi * x ^ (3 / 5 : ℝ) / (m * x)) atTop (𝓝 0) := by
  have hpow := tendsto_rpow_neg_atTop (by norm_num : 0 < (2 / 5 : ℝ))
  have hlim : Tendsto (fun x : ℝ => (2 * Real.pi / m) * x ^ (-(2 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (major_angle_identity m x hx).symm

theorem tendsto_major_cubic_budget (m : ℝ) :
    Tendsto (fun x : ℝ =>
      (2 * Real.exp 1) * (x * (2 * Real.pi * x ^ (3 / 5 : ℝ) / (m * x)) ^ 3)) atTop (𝓝 0) := by
  have hpow := tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 5 : ℝ))
  have hlim : Tendsto (fun x : ℝ =>
      ((2 * Real.exp 1) * (2 * Real.pi / m) ^ 3) * x ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (major_cubic_identity m x hx).symm

theorem eventually_major_parameters (m : ℝ) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (3 / 5 : ℝ) ≤ m * N / 2 ∧
      2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (m * N) ≤ 1 ∧
      (2 * Real.exp 1) * (N * (2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (m * N)) ^ 3) ≤
        Real.log (3 / 2) := by
  have hangle : ∀ᶠ N : ℕ in atTop,
      2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (m * N) < 1 := by
    exact ((tendsto_major_angle m).comp tendsto_natCast_atTop_atTop).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbudget : ∀ᶠ N : ℕ in atTop,
      (2 * Real.exp 1) * (N * (2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) / (m * N)) ^ 3) <
        Real.log (3 / 2) := by
    exact ((tendsto_major_cubic_budget m).comp tendsto_natCast_atTop_atTop).eventually
      (Iio_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)))
  filter_upwards [hangle, hbudget, eventually_gt_atTop (0 : ℕ)] with N ha hb hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmult : 2 * Real.pi * (N : ℝ) ^ (3 / 5 : ℝ) < m * N := by
    simpa only [one_mul] using (div_lt_iff₀ (mul_pos hm hNR)).mp ha
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hpow : 0 ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_nonneg hNR.le _
  refine ⟨?_, ha.le, hb.le⟩
  nlinarith [mul_le_mul_of_nonneg_right hpi hpow]

theorem middle_exponent_identity (x : ℝ) (hx : 0 < x) :
    x * (x ^ (3 / 5 : ℝ)) ^ 2 / x ^ 2 = x ^ (1 / 5 : ℝ) := by
  have hp : x * (x ^ (3 / 5 : ℝ)) ^ 2 = x ^ (11 / 5 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ ((3 / 5 : ℝ) * 2) := by
        rw [Real.rpow_one, Real.rpow_mul hx.le]
        simp only [Real.rpow_ofNat]
      _ = _ := by rw [← Real.rpow_add hx]; norm_num
  rw [hp, ← Real.rpow_natCast x 2, ← Real.rpow_sub hx]
  norm_num

theorem tendsto_middle_decay (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (2 * x + 1) * Real.exp (-b * x ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
  have hroot := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)
  have hp (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 5 : ℝ)) ^ (5 : ℝ) = x := by
    rw [← Real.rpow_mul hx]
    norm_num
  have hweighted : Tendsto (fun x : ℝ => x * Real.exp (-b * x ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 5 b hb).comp hroot
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def, hp x hx]
  have hbare : Tendsto (fun x : ℝ => Real.exp (-b * x ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb).comp hroot
  have hsum := (hweighted.const_mul 2).add hbare
  simp only [mul_zero, zero_add] at hsum
  apply hsum.congr'
  filter_upwards with x using by ring

theorem eventually_middle_parameters (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ C : ℝ, α * N ≤ C →
      (2 * N + 1 : ℝ) *
        Real.exp (-(8 * τ * C * ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 4 := by
  have hlim := (tendsto_middle_decay (8 * τ * α) (by positivity)).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (2 * N + 1 : ℝ) * Real.exp (-(8 * τ * α) * (N : ℝ) ^ (1 / 5 : ℝ)) < 1 / 4 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with N hNlarge hN C hC
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpower := Real.rpow_nonneg hNR.le (3 / 5 : ℝ)
  have hexponent : (8 * τ * α) * (N : ℝ) ^ (1 / 5 : ℝ) ≤
      8 * τ * C * ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
    calc
      _ = 8 * τ * (α * N) * ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (N : ℝ) ^ 2 := by
        rw [← middle_exponent_identity (N : ℝ) hNR]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by positivity)) (sq_nonneg _))
        (sq_nonneg _)
  have he := Real.exp_le_exp.mpr (neg_le_neg hexponent)
  have hbound := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  exact hbound.trans (by simpa only [neg_mul] using hNlarge.le)

theorem prime_power_cleanup {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (η : ℝ) (hη : 0 ≤ η) :
    ∃ F ⊆ A,
      (∀ q : ℕ, IsPrimePow q → (∃ n ∈ F, q ∣ n) →
        η ≤ (q : ℝ) * (reciprocalSum (F.filter (fun n => q ∣ n)) : ℝ)) ∧
      (reciprocalSum A : ℝ) - (reciprocalSum F : ℝ) ≤
        η * ∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, (1 : ℝ) / q := by
  classical
  let S := (Finset.Icc 1 N).filter IsPrimePow
  obtain ⟨F, hFA, hrich, hloss⟩ := clean_divisor_groups η hη S
    (fun q hq => (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1) A
  refine ⟨F, hFA, ?_, ?_⟩
  · intro q hqpp hqF
    obtain ⟨n, hnF, hqn⟩ := hqF
    have hnN := Finset.mem_Icc.mp (hA (hFA hnF))
    have hqS : q ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqpp.pos, (Nat.le_of_dvd hnN.1 hqn).trans hnN.2⟩, hqpp⟩
    rcases hrich q hqS with he | hg
    · have hnlocal : n ∈ F.filter (fun n => q ∣ n) := Finset.mem_filter.mpr ⟨hnF, hqn⟩
      rw [he] at hnlocal
      exact False.elim (Finset.notMem_empty n hnlocal)
    · simpa only [reciprocalSum_real] using hg
  · simpa only [reciprocalSum_real] using hloss

theorem divisor_class_survives_small_loss (A F : Finset ℕ) (q : ℕ) (hFA : F ⊆ A)
    (hloss : (reciprocalSum A : ℝ) - (reciprocalSum F : ℝ) <
      (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) :
    ∃ n ∈ F, q ∣ n := by
  classical
  by_contra hnone
  have hsub : A.filter (fun n => q ∣ n) ⊆ A \ F := by
    intro n hn
    have hh := Finset.mem_filter.mp hn
    exact Finset.mem_sdiff.mpr ⟨hh.1, fun hnF => hnone ⟨n, hnF, hh.2⟩⟩
  have hm : (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ) ≤ (reciprocalSum (A \ F) : ℝ) := by
    rw [reciprocalSum_real, reciprocalSum_real]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnnot
    positivity
  have hsplit : (reciprocalSum (A \ F) : ℝ) + (reciprocalSum F : ℝ) = (reciprocalSum A : ℝ) := by
    simp only [reciprocalSum_real]
    exact Finset.sum_sdiff hFA
  linarith

theorem divisor_dvd_lcm_of_primePower_classes (b : ℕ) (F : Finset ℕ)
    (hclasses : ∀ q : ℕ, IsPrimePow q → q ∣ b → ∃ n ∈ F, q ∣ n) :
    b ∣ F.lcm id := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  · have hpp : IsPrimePow (p ^ k) := IsPrimePow.pow hp.isPrimePow hk
    obtain ⟨n, hn, hpn⟩ := hclasses (p ^ k) hpp hpk
    exact hpn.trans (Finset.dvd_lcm hn)

theorem eventually_primePower_reciprocal_bound :
    ∀ᶠ N : ℕ in atTop,
      (∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, (1 : ℝ) / q) ≤
        2 * Real.log (Real.log N) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound.bound,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (|b| + C))]
      with N hest hlog hloglog
  have hlogpos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlog
  have hh : |(∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, (q : ℝ)⁻¹) -
      (Real.log (Real.log N) + b)| ≤ C * (Real.log N)⁻¹ := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_inv, abs_of_pos hlogpos] using hest
  have hinv : (Real.log N)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hlog
  have hupper := (abs_le.mp hh).2
  have hscale := mul_le_mul_of_nonneg_left hinv hC.le
  have hbabs := le_abs_self b
  simp only [one_div]
  linarith

theorem tendsto_primePower_cleanup_budget :
    Tendsto (fun N : ℕ =>
      (∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, (1 : ℝ) / q) /
        (Real.log (Real.log N)) ^ 2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 2 / Real.log (Real.log N)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (tendsto_log_log_coe_at_top.inv_tendsto_atTop.const_mul 2)
  apply squeeze_zero' ?_ ?_ hlim
  · exact Filter.Eventually.of_forall (fun N => by
      apply div_nonneg
      · exact Finset.sum_nonneg (fun q hq => by positivity)
      · positivity)
  · filter_upwards [eventually_primePower_reciprocal_bound,
      tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hS hL
    apply (div_le_div_iff₀ (sq_pos_of_pos hL) hL).mpr
    nlinarith [mul_le_mul_of_nonneg_right hS hL.le]

theorem exists_prime_power_cleaning_sequence (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) :
    ∃ F : ℕ → Finset ℕ,
      (∀ N, F N ⊆ A N) ∧
      (∀ N q, IsPrimePow q → (∃ n ∈ F N, q ∣ n) →
        ((Real.log (Real.log N)) ^ 2)⁻¹ ≤
          (q : ℝ) * (reciprocalSum ((F N).filter (fun n => q ∣ n)) : ℝ)) ∧
      Tendsto (fun N => (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0) := by
  classical
  choose F hSub hRich hLoss using fun N => prime_power_cleanup (A N) (hA N)
    (((Real.log (Real.log N)) ^ 2)⁻¹) (by positivity)
  refine ⟨F, hSub, hRich, ?_⟩
  apply squeeze_zero ?_ ?_ tendsto_primePower_cleanup_budget
  · intro N
    rw [sub_nonneg, reciprocalSum_real, reciprocalSum_real]
    apply Finset.sum_le_sum_of_subset_of_nonneg (hSub N)
    intro n hn hnnot
    positivity
  · intro N
    simpa only [div_eq_mul_inv, mul_comm] using hLoss N

theorem cleaning_preserves_reciprocal_limit (A F : ℕ → Finset ℕ) (r : ℝ)
    (hA : Tendsto (fun N => (reciprocalSum (A N) : ℝ)) atTop (𝓝 r))
    (hLoss : Tendsto (fun N =>
      (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (reciprocalSum (F N) : ℝ)) atTop (𝓝 r) := by
  have hh := hA.sub hLoss
  simpa only [sub_zero, sub_sub_cancel] using hh

theorem eventually_divisor_class_survives (A F : ℕ → Finset ℕ) (q : ℕ) (c : ℝ)
    (hSub : ∀ N, F N ⊆ A N) (hc : 0 < c)
    (hLocal : Tendsto (fun N =>
      (reciprocalSum ((A N).filter (fun n => q ∣ n)) : ℝ)) atTop (𝓝 c))
    (hLoss : Tendsto (fun N =>
      (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∃ n ∈ F N, q ∣ n := by
  have hLow := hLocal.eventually (Ioi_mem_nhds (by linarith : c / 2 < c))
  have hSmall := hLoss.eventually (Iio_mem_nhds (half_pos hc))
  filter_upwards [hLow, hSmall] with N hNlocal hNloss
  exact divisor_class_survives_small_loss (A N) (F N) q (hSub N) (hNloss.trans hNlocal)

theorem eventually_denominator_dvd_cleaned_lcm (A F : ℕ → Finset ℕ) (b : ℕ)
    (hb : 0 < b) (hSub : ∀ N, F N ⊆ A N)
    (hLocal : ∀ q : ℕ, IsPrimePow q → q ∣ b → ∃ c : ℝ, 0 < c ∧
      Tendsto (fun N => (reciprocalSum ((A N).filter (fun n => q ∣ n)) : ℝ)) atTop (𝓝 c))
    (hLoss : Tendsto (fun N =>
      (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, b ∣ (F N).lcm id := by
  classical
  let S := b.divisors.filter IsPrimePow
  have hClasses : ∀ q ∈ S, ∀ᶠ N : ℕ in atTop, ∃ n ∈ F N, q ∣ n := by
    intro q hq
    have hh := Finset.mem_filter.mp hq
    have hqb := (Nat.mem_divisors.mp hh.1).1
    obtain ⟨c, hc, hlimit⟩ := hLocal q hh.2 hqb
    exact eventually_divisor_class_survives A F q c hSub hc hlimit hLoss
  have hAll := (Filter.eventually_all_finset S).mpr hClasses
  filter_upwards [hAll] with N hN
  apply divisor_dvd_lcm_of_primePower_classes b (F N)
  intro q hqpp hqb
  exact hN q (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqb, hb.ne'⟩, hqpp⟩)

theorem cleaning_preserves_card_density (A F : ℕ → Finset ℕ) (α : ℝ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) (hSub : ∀ N, F N ⊆ A N)
    (hDensity : Tendsto (fun N => (A N).card / (N : ℝ)) atTop (𝓝 α))
    (hLoss : Tendsto (fun N =>
      (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (F N).card / (N : ℝ)) atTop (𝓝 α) := by
  have hDifference : Tendsto (fun N => ((A N).card - (F N).card : ℝ) / N) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hLoss
    · exact Filter.Eventually.of_forall (fun N => div_nonneg
        (sub_nonneg.mpr (by exact_mod_cast Finset.card_le_card (hSub N))) (Nat.cast_nonneg N))
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hcard := card_le_N_mul_reciprocalSum ((Finset.sdiff_subset : A N \ F N ⊆ A N).trans (hA N))
      have hcardsNat : (A N \ F N).card + (F N).card = (A N).card := by
        simpa using (Finset.sum_sdiff (hSub N) (f := fun _ : ℕ => (1 : ℕ)))
      have hcards : ((A N \ F N).card : ℝ) + (F N).card = (A N).card := by exact_mod_cast hcardsNat
      have hsplit : (reciprocalSum (A N \ F N) : ℝ) + (reciprocalSum (F N) : ℝ) =
          (reciprocalSum (A N) : ℝ) := by
        simp only [reciprocalSum_real]
        exact Finset.sum_sdiff (hSub N)
      have hsumdiff : (reciprocalSum (A N \ F N) : ℝ) =
          (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ) := by linarith
      have hcarddiff : ((A N \ F N).card : ℝ) = (A N).card - (F N).card := by linarith
      rw [hsumdiff, hcarddiff] at hcard
      exact (div_le_iff₀ hNR).mpr (by simpa only [mul_comm] using hcard)
  simpa only [sub_zero, sub_div, sub_sub_cancel] using hDensity.sub hDifference

open scoped Classical

noncomputable def primePowerRecipSum (x : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (1 : ℝ) / q

noncomputable def primePowerTail (N : ℕ) (S : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ S < (q : ℝ)), (1 : ℝ) / q

def PrimePowerSmooth (S : ℝ) (n : ℕ) : Prop :=
  ∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ S

theorem exists_primePower_mertens_limit :
    ∃ b : ℝ, Tendsto (fun x : ℝ => primePowerRecipSum x - (Real.log (Real.log x) + b))
      atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  refine ⟨b, ?_⟩
  have hlim : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  simpa only [primePowerRecipSum, one_div] using hb.trans_tendsto hlim

theorem primePowerTail_eq_difference {N : ℕ} {S : ℝ} (hS : 0 ≤ S) (hSN : S ≤ N) :
    primePowerTail N S = primePowerRecipSum (N : ℝ) - primePowerRecipSum S := by
  classical
  let P := (Finset.Icc 1 N).filter IsPrimePow
  have hlow : P.filter (fun q : ℕ => (q : ℝ) ≤ S) = (Finset.Icc 1 ⌊S⌋₊).filter IsPrimePow := by
    ext q
    simp only [P, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hq1, hqN⟩, hqpp⟩, hqS⟩
      exact ⟨⟨hq1, (Nat.le_floor_iff hS).mpr hqS⟩, hqpp⟩
    · rintro ⟨⟨hq1, hqS⟩, hqpp⟩
      have hqSR := (Nat.le_floor_iff hS).mp hqS
      exact ⟨⟨⟨hq1, by exact_mod_cast hqSR.trans hSN⟩, hqpp⟩, hqSR⟩
  have hhigh : P.filter (fun q : ℕ => ¬ (q : ℝ) ≤ S) =
      (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ S < (q : ℝ)) := by
    ext q
    simp only [P, Finset.mem_filter, not_le, and_assoc]
  have hsum := Finset.sum_filter_add_sum_filter_not P (fun q => (q : ℝ) ≤ S) (fun q => (1 : ℝ) / q)
  rw [hlow, hhigh] at hsum
  unfold primePowerTail primePowerRecipSum
  rw [Nat.floor_natCast]
  linarith only [hsum]

theorem tendsto_primePowerTail (S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop) (hSN : ∀ᶠ N : ℕ in atTop, S N ≤ N)
    (hLogs : Tendsto (fun N : ℕ => Real.log (Real.log N) - Real.log (Real.log (S N))) atTop (𝓝 0)) :
    Tendsto (fun N => primePowerTail N (S N)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePower_mertens_limit
  have hNerr := hb.comp tendsto_natCast_atTop_atTop
  have hSerr := hb.comp hS
  have hlim := (hNerr.sub hSerr).add hLogs
  simp only [sub_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hSN, hS.eventually (eventually_ge_atTop (0 : ℝ))] with N hNS hS0
  rw [primePowerTail_eq_difference hS0 hNS]
  dsimp [Function.comp_def]
  ring

theorem card_divisible_interval (N q : ℕ) (hq : 0 < q) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card = N / q := by
  have hcard : (Finset.Icc 1 (N / q)).card = N / q := by simp
  rw [← hcard]
  refine (Finset.card_bij (fun n _ => n * q) ?_ ?_ ?_).symm
  · intro n hn
    have hi := Finset.mem_Icc.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨one_le_mul hi.1 hq, (Nat.le_div_iff_mul_le hq).mp hi.2⟩, dvd_mul_left _ _⟩
  · intro n hn m hm heq
    exact Nat.eq_of_mul_eq_mul_right hq (by simpa only [mul_comm] using heq)
  · intro n hn
    obtain ⟨hnI, hqn⟩ := Finset.mem_filter.mp hn
    obtain ⟨m, rfl⟩ := hqn
    have hi := Finset.mem_Icc.mp hnI
    refine ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, by simp only [mul_comm]⟩
    · exact Nat.succ_le_of_lt (Nat.pos_of_mul_pos_left hi.1)
    · exact (Nat.le_div_iff_mul_le hq).mpr (by simpa only [mul_comm] using hi.2)

theorem nonsmooth_card_bound {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (S : ℝ) :
    ((A.filter (fun n => ¬ PrimePowerSmooth S n)).card : ℝ) ≤ N * primePowerTail N S := by
  classical
  let T := (Finset.Icc 1 N).filter (fun q : ℕ => IsPrimePow q ∧ S < (q : ℝ))
  have hcover : A.filter (fun n => ¬ PrimePowerSmooth S n) ⊆
      T.biUnion (fun q => (Finset.Icc 1 N).filter (fun n => q ∣ n)) := by
    intro n hn
    obtain ⟨hnA, hbad⟩ := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Icc.mp (hA hnA)
    have hex : ∃ q : ℕ, IsPrimePow q ∧ q ∣ n ∧ S < (q : ℝ) := by
      simpa only [PrimePowerSmooth, not_forall, not_imp, not_le, exists_prop] using hbad
    obtain ⟨q, hqpp, hqn, hqS⟩ := hex
    apply Finset.mem_biUnion.mpr
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hqpp.pos, (Nat.le_of_dvd hnI.1 hqn).trans hnI.2⟩, hqpp, hqS⟩,
      Finset.mem_filter.mpr ⟨hA hnA, hqn⟩⟩
  have hcard : (A.filter (fun n => ¬ PrimePowerSmooth S n)).card ≤
      ∑ q ∈ T, ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ q ∈ T, (((Finset.Icc 1 N).filter (fun n => q ∣ n)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ q ∈ T, (N : ℝ) / q := by
      apply Finset.sum_le_sum
      intro q hq
      rw [card_divisible_interval N q (Finset.mem_filter.mp hq).2.1.pos]
      exact Nat.cast_div_le
    _ = _ := by
      rw [primePowerTail, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

noncomputable def smoothCutoff (a : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * Real.exp (-a * (Real.log N) ^ (4 / 5 : ℝ))

theorem smoothCutoff_pos (a : ℝ) {N : ℕ} (hN : 0 < N) : 0 < smoothCutoff a N := by
  unfold smoothCutoff
  exact mul_pos (by exact_mod_cast hN) (Real.exp_pos _)

theorem smoothCutoff_le (a : ℝ) (ha : 0 ≤ a) (N : ℕ) : smoothCutoff a N ≤ N := by
  have hpower : 0 ≤ (Real.log N) ^ (4 / 5 : ℝ) := Real.rpow_nonneg (log_nat_nonneg N) _
  have he : Real.exp (-a * (Real.log N) ^ (4 / 5 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha hpower])
  simpa only [smoothCutoff, mul_one] using mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)

theorem log_smoothCutoff (a : ℝ) {N : ℕ} (hN : 0 < N) :
    Real.log (smoothCutoff a N) = Real.log N - a * (Real.log N) ^ (4 / 5 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [smoothCutoff, Real.log_mul hNR.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem tendsto_log_smoothCutoff_ratio (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log (smoothCutoff a N) / Real.log N) atTop (𝓝 1) := by
  have hpower : Tendsto (fun N : ℕ => (Real.log N) ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_log_coe_at_top
  have hlim : Tendsto (fun N : ℕ => 1 - a * (Real.log N) ^ (-(1 / 5 : ℝ))) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hpower.const_mul a)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_pos hNR
  have hp : (Real.log N) ^ (4 / 5 : ℝ) / Real.log N =
      (Real.log N) ^ (-(1 / 5 : ℝ)) := by
    rw [show (-(1 / 5 : ℝ)) = (4 / 5 : ℝ) - 1 by norm_num,
      Real.rpow_sub hlog, Real.rpow_one]
  rw [log_smoothCutoff a (Nat.zero_lt_of_lt hN), sub_div, div_self hlog.ne', mul_div_assoc, hp]

theorem tendsto_log_smoothCutoff (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log (smoothCutoff a N)) atTop atTop := by
  have hratio := (tendsto_log_smoothCutoff_ratio a).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hLower : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) * Real.log N ≤ Real.log (smoothCutoff a N) := by
    filter_upwards [hratio, eventually_gt_atTop (1 : ℕ)] with N hNratio hN
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    exact ((lt_div_iff₀ hlog).mp hNratio).le
  exact tendsto_atTop_mono' atTop hLower
    ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr tendsto_log_coe_at_top)

theorem tendsto_smoothCutoff (a : ℝ) : Tendsto (smoothCutoff a) atTop atTop := by
  have hlim := Real.tendsto_exp_atTop.comp (tendsto_log_smoothCutoff a)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact Real.exp_log (smoothCutoff_pos a hN)

theorem tendsto_smoothCutoff_loglog_difference (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log (Real.log N) - Real.log (Real.log (smoothCutoff a N)))
      atTop (𝓝 0) := by
  have hlim := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (tendsto_log_smoothCutoff_ratio a)).neg
  simp only [Real.log_one, neg_zero] at hlim
  apply hlim.congr'
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    (tendsto_log_smoothCutoff a).eventually (eventually_gt_atTop (0 : ℝ))] with N hN hS
  dsimp only [Function.comp_def]
  rw [Real.log_div hS.ne' hN.ne']
  ring

theorem tendsto_primePowerTail_smoothCutoff (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun N => primePowerTail N (smoothCutoff a N)) atTop (𝓝 0) := by
  exact tendsto_primePowerTail (smoothCutoff a) (tendsto_smoothCutoff a)
    (Filter.Eventually.of_forall (smoothCutoff_le a ha)) (tendsto_smoothCutoff_loglog_difference a)

theorem reciprocalSum_le_card_div_min (A : Finset ℕ) (M : ℝ) (hM : 0 < M)
    (hmin : ∀ n ∈ A, M ≤ (n : ℝ)) : (reciprocalSum A : ℝ) ≤ A.card / M := by
  rw [reciprocalSum_real]
  calc
    _ ≤ ∑ _n ∈ A, (1 : ℝ) / M := Finset.sum_le_sum
      (fun n hn => one_div_le_one_div_of_le hM (hmin n hn))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]

theorem tendsto_nonsmooth_density (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun N => ((A N).filter (fun n => ¬ PrimePowerSmooth (smoothCutoff a N) n)).card / (N : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_primePowerTail_smoothCutoff a ha)
  · exact Filter.Eventually.of_forall (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hh := nonsmooth_card_bound (A N) (hA N) (smoothCutoff a N)
    exact (div_le_iff₀ hNR).mpr (by simpa only [mul_comm] using hh)

theorem tendsto_nonsmooth_reciprocal (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, m * N ≤ (n : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun N => (reciprocalSum ((A N).filter (fun n =>
      ¬ PrimePowerSmooth (smoothCutoff a N) n)) : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N =>
      (((A N).filter (fun n => ¬ PrimePowerSmooth (smoothCutoff a N) n)).card / (N : ℝ)) / m)
      atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_nonsmooth_density A hA a ha).div_const m
  apply squeeze_zero' ?_ ?_ hlim
  · apply Filter.Eventually.of_forall
    intro N
    exact_mod_cast reciprocalSum_nonneg
      ((A N).filter (fun n => ¬ PrimePowerSmooth (smoothCutoff a N) n))
  · filter_upwards [hmin, eventually_gt_atTop (0 : ℕ)] with N hNmin hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hh := reciprocalSum_le_card_div_min
      ((A N).filter (fun n => ¬ PrimePowerSmooth (smoothCutoff a N) n)) (m * N) (mul_pos hm hNR)
      (fun n hn => hNmin n (Finset.mem_filter.mp hn).1)
    rw [mul_comm m (N : ℝ), div_mul_eq_div_div] at hh
    exact hh

theorem exists_smooth_cleaning_sequence (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, m * N ≤ (n : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    ∃ F : ℕ → Finset ℕ, (∀ N, F N ⊆ A N) ∧
      (∀ N n, n ∈ F N → PrimePowerSmooth (smoothCutoff a N) n) ∧
      Tendsto (fun N => (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0) := by
  classical
  let F := fun N => (A N).filter (PrimePowerSmooth (smoothCutoff a N))
  refine ⟨F, fun N => Finset.filter_subset _ _, fun N n hn => (Finset.mem_filter.mp hn).2, ?_⟩
  have hlim := tendsto_nonsmooth_reciprocal A hA m hm hmin a ha
  have heq (N : ℕ) : (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ) =
      (reciprocalSum ((A N).filter (fun n => ¬ PrimePowerSmooth (smoothCutoff a N) n)) : ℝ) := by
    have hh := Finset.sum_filter_add_sum_filter_not (A N) (PrimePowerSmooth (smoothCutoff a N))
      (fun n => (1 : ℝ) / n)
    simp only [reciprocalSum_real]
    dsimp [F]
    linarith only [hh]
  simpa only [heq] using hlim

noncomputable def primePowerMultiplicity (N n : ℕ) : ℕ :=
  (((Finset.Icc 1 N).filter IsPrimePow).filter (fun q => q ∣ n)).card

theorem primePowerMultiplicity_sum (N : ℕ) (A : Finset ℕ) :
    (∑ n ∈ A, (primePowerMultiplicity N n : ℝ)) =
      ∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, ((A.filter (fun n => q ∣ n)).card : ℝ) := by
  simp only [primePowerMultiplicity, Finset.natCast_card_filter]
  exact Finset.sum_comm

theorem primePowerMultiplicity_first_moment {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    (∑ n ∈ A, (primePowerMultiplicity N n : ℝ)) ≤ N * primePowerRecipSum (N : ℝ) := by
  rw [primePowerMultiplicity_sum]
  calc
    _ ≤ ∑ q ∈ (Finset.Icc 1 N).filter IsPrimePow, (N : ℝ) / q := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      have hsub : A.filter (fun n => q ∣ n) ⊆ (Finset.Icc 1 N).filter (fun n => q ∣ n) :=
        Finset.filter_subset_filter _ hA
      have hh : ((A.filter (fun n => q ∣ n)).card : ℝ) ≤
          (((Finset.Icc 1 N).filter (fun n => q ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      rw [card_divisible_interval N q hqpos] at hh
      exact hh.trans Nat.cast_div_le
    _ = _ := by
      rw [primePowerRecipSum, Nat.floor_natCast, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem many_primePowers_card_bound {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (T : ℝ) (hT : 0 < T) :
    ((A.filter (fun n => T < (primePowerMultiplicity N n : ℝ))).card : ℝ) ≤
      N * primePowerRecipSum (N : ℝ) / T := by
  have hsum : T * ((A.filter (fun n => T < (primePowerMultiplicity N n : ℝ))).card : ℝ) ≤
      ∑ n ∈ A, (primePowerMultiplicity N n : ℝ) := by
    calc
      _ = ∑ _n ∈ A.filter (fun n => T < (primePowerMultiplicity N n : ℝ)), T := by simp [mul_comm]
      _ ≤ ∑ n ∈ A.filter (fun n => T < (primePowerMultiplicity N n : ℝ)),
          (primePowerMultiplicity N n : ℝ) :=
        Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n hn hnnot => Nat.cast_nonneg _)
  apply (le_div_iff₀ hT).mpr
  calc
    _ = T * ((A.filter (fun n => T < (primePowerMultiplicity N n : ℝ))).card : ℝ) := mul_comm _ _
    _ ≤ _ := hsum
    _ ≤ _ := primePowerMultiplicity_first_moment A hA

theorem tendsto_many_primePowers_density (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) :
    Tendsto (fun N => ((A N).filter (fun n =>
      (Real.log (Real.log N)) ^ 2 < (primePowerMultiplicity N n : ℝ))).card / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_primePower_cleanup_budget
  · exact Filter.Eventually.of_forall (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hL
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hh := many_primePowers_card_bound (A N) (hA N)
      ((Real.log (Real.log N)) ^ 2) (sq_pos_of_pos hL)
    apply (div_le_iff₀ hNR).mpr
    rw [primePowerRecipSum, Nat.floor_natCast] at hh
    convert hh using 1
    ring

theorem reciprocal_limit_zero_of_card_density (B : ℕ → Finset ℕ) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ B N, m * N ≤ (n : ℝ))
    (hCard : Tendsto (fun N => (B N).card / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (reciprocalSum (B N) : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => ((B N).card / (N : ℝ)) / m) atTop (𝓝 0) := by
    simpa only [zero_div] using hCard.div_const m
  apply squeeze_zero' ?_ ?_ hlim
  · exact Filter.Eventually.of_forall (fun N => by exact_mod_cast reciprocalSum_nonneg (B N))
  · filter_upwards [hmin, eventually_gt_atTop (0 : ℕ)] with N hNmin hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hh := reciprocalSum_le_card_div_min (B N) (m * N) (mul_pos hm hNR) hNmin
    rw [mul_comm m (N : ℝ), div_mul_eq_div_div] at hh
    exact hh

theorem exists_multiplicity_cleaning_sequence (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, m * N ≤ (n : ℝ)) :
    ∃ F : ℕ → Finset ℕ, (∀ N, F N ⊆ A N) ∧
      (∀ N n, n ∈ F N → (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
      Tendsto (fun N => (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0) := by
  classical
  let F := fun N => (A N).filter (fun n =>
    (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
  let B := fun N => (A N).filter (fun n =>
    (Real.log (Real.log N)) ^ 2 < (primePowerMultiplicity N n : ℝ))
  have hBmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ B N, m * N ≤ (n : ℝ) := by
    filter_upwards [hmin] with N hN n hn
    exact hN n (Finset.mem_filter.mp hn).1
  have hlim := reciprocal_limit_zero_of_card_density B m hm hBmin (tendsto_many_primePowers_density A hA)
  refine ⟨F, fun N => Finset.filter_subset _ _, fun N n hn => (Finset.mem_filter.mp hn).2, ?_⟩
  have heq (N : ℕ) : (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ) =
      (reciprocalSum (B N) : ℝ) := by
    have hh := Finset.sum_filter_add_sum_filter_not (A N)
      (fun n => (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) (fun n => (1 : ℝ) / n)
    simp only [not_le] at hh
    simp only [reciprocalSum_real]
    dsimp [F, B]
    linarith only [hh]
  simpa only [heq] using hlim

theorem exists_regular_cleaning_sequence (A : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Finset.Icc 1 N) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, m * N ≤ (n : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    ∃ F : ℕ → Finset ℕ, (∀ N, F N ⊆ A N) ∧
      (∀ N n, n ∈ F N → PrimePowerSmooth (smoothCutoff a N) n) ∧
      (∀ N n, n ∈ F N → (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
      (∀ N q, IsPrimePow q → (∃ n ∈ F N, q ∣ n) →
        ((Real.log (Real.log N)) ^ 2)⁻¹ ≤
          (q : ℝ) * (reciprocalSum ((F N).filter (fun n => q ∣ n)) : ℝ)) ∧
      Tendsto (fun N => (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨S, hSA, hSmooth, hLossAS⟩ := exists_smooth_cleaning_sequence A hA m hm hmin a ha
  have hS : ∀ N, S N ⊆ Finset.Icc 1 N := fun N => (hSA N).trans (hA N)
  have hSmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ S N, m * N ≤ (n : ℝ) := by
    filter_upwards [hmin] with N hN n hn
    exact hN n (hSA N hn)
  obtain ⟨B, hBS, hMultiplicity, hLossSB⟩ := exists_multiplicity_cleaning_sequence S hS m hm hSmin
  have hB : ∀ N, B N ⊆ Finset.Icc 1 N := fun N => (hBS N).trans (hS N)
  obtain ⟨F, hFB, hRich, hLossBF⟩ := exists_prime_power_cleaning_sequence B hB
  refine ⟨F, fun N => (hFB N).trans ((hBS N).trans (hSA N)),
    fun N n hn => hSmooth N n (hBS N (hFB N hn)),
    fun N n hn => hMultiplicity N n (hFB N hn), hRich, ?_⟩
  have hlim := (hLossAS.add hLossSB).add hLossBF
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards with N using by ring

set_option maxHeartbeats 800000 in
theorem smooth_lcm_le_exp (A : Finset ℕ) (S : ℝ) (hS : 1 ≤ S)
    (hSmooth : ∀ n ∈ A, PrimePowerSmooth S n) :
    ((A.lcm id : ℕ) : ℝ) ≤ Real.exp (S * Real.log S) := by
  classical
  let P := (Finset.Icc 1 ⌊S⌋₊).filter IsPrimePow
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hmem (n : ℕ) (hn : n ∈ A) (q : ℕ) (hq : IsPrimePow q) (hqn : q ∣ n) : q ∈ P := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hq.pos, (Nat.le_floor_iff hS0.le).mpr (hSmooth n hn q hq hqn)⟩, hq⟩
  have hdvd : A.lcm id ∣ ∏ q ∈ P, q := by
    apply Finset.lcm_dvd
    intro n hn
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    by_cases hk : k = 0
    · simp [hk]
    · exact Finset.dvd_prod_of_mem id (hmem n hn (p ^ k) (IsPrimePow.pow hp.isPrimePow hk) hpk)
  have hprodpos : 0 < ∏ q ∈ P, q := Finset.prod_pos
    (fun q hq => (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1)
  have hQle : ((A.lcm id : ℕ) : ℝ) ≤ ((∏ q ∈ P, q : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hprodpos hdvd
  have hPcard : (P.card : ℝ) ≤ S := by
    have hh : P.card ≤ ⌊S⌋₊ := by
      simpa using Finset.card_le_card (Finset.filter_subset IsPrimePow (Finset.Icc 1 ⌊S⌋₊))
    exact (by exact_mod_cast hh : (P.card : ℝ) ≤ ⌊S⌋₊).trans (Nat.floor_le hS0.le)
  apply hQle.trans
  calc
    _ = ∏ q ∈ P, (q : ℝ) := by simp only [Nat.cast_prod]
    _ ≤ ∏ _q ∈ P, Real.exp (Real.log S) := by
      apply Finset.prod_le_prod₀ (fun q hq => Nat.cast_nonneg q)
      intro q hq
      rw [Real.exp_log hS0]
      exact ((Nat.le_floor_iff hS0.le).mp (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2)
    _ = Real.exp ((P.card : ℝ) * Real.log S) := by rw [← Real.exp_sum]; simp
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hPcard (Real.log_nonneg hS))

theorem tendsto_log_times_smooth_factor (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log N * Real.exp (-a * (Real.log N) ^ (4 / 5 : ℝ))) atTop (𝓝 0) := by
  have hroot : Tendsto (fun N : ℕ => (Real.log N) ^ (4 / 5 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp tendsto_log_coe_at_top
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 4) a ha).comp hroot
  apply hlim.congr'
  filter_upwards with N
  have hp : ((Real.log N) ^ (4 / 5 : ℝ)) ^ (5 / 4 : ℝ) = Real.log N := by
    rw [← Real.rpow_mul (log_nat_nonneg N)]
    norm_num
  simp only [Function.comp_def, hp]

theorem tendsto_smooth_lcm_log_ratio (A : ℕ → Finset ℕ)
    (hPos : ∀ N n, n ∈ A N → 0 < n) (a : ℝ) (ha : 0 < a)
    (hSmooth : ∀ N n, n ∈ A N → PrimePowerSmooth (smoothCutoff a N) n) :
    Tendsto (fun N => Real.log ((A N).lcm id : ℕ) / N) atTop (𝓝 0) := by
  have hQpos (N : ℕ) : (0 : ℝ) < (A N).lcm id := by
    exact_mod_cast Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos N n hn).ne'))
  apply squeeze_zero' ?_ ?_ (tendsto_log_times_smooth_factor a ha)
  · exact Filter.Eventually.of_forall (fun N => div_nonneg (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ (A N).lcm id by exact_mod_cast hQpos N))) (Nat.cast_nonneg N))
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      (tendsto_smoothCutoff a).eventually (eventually_ge_atTop (1 : ℝ))] with N hN hS
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hS0 := smoothCutoff_pos a hN
    have hBound := smooth_lcm_le_exp (A N) (smoothCutoff a N) hS (hSmooth N)
    have hlogQ := Real.log_le_log (hQpos N) hBound
    rw [Real.log_exp] at hlogQ
    have hlogS : Real.log (smoothCutoff a N) ≤ Real.log N :=
      Real.log_le_log hS0 (smoothCutoff_le a ha.le N)
    calc
      _ ≤ (smoothCutoff a N * Real.log (smoothCutoff a N)) / N :=
        div_le_div_of_nonneg_right hlogQ hNR.le
      _ ≤ (smoothCutoff a N * Real.log N) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogS hS0.le) hNR.le
      _ = _ := by unfold smoothCutoff; field_simp [hNR.ne']

theorem eventually_smoothCutoff_ge_rpow (a ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) ≤ smoothCutoff a N := by
  have hratio := (tendsto_log_smoothCutoff_ratio a).eventually
    (Ioi_mem_nhds (by linarith : 1 - ε < 1))
  filter_upwards [hratio, eventually_gt_atTop (1 : ℕ)] with N hR hN
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos hNR
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNR
  have hS0 := smoothCutoff_pos a (Nat.zero_lt_of_lt hN)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hN0 _) hS0).mp
  rw [Real.log_rpow hN0]
  exact ((lt_div_iff₀ hlog).mp hR).le

theorem eventually_smooth_lcm_fourier_growth (A : ℕ → Finset ℕ)
    (hPos : ∀ N n, n ∈ A N → 0 < n) (a : ℝ) (ha : 0 < a)
    (hSmooth : ∀ N n, n ∈ A N → PrimePowerSmooth (smoothCutoff a N) n)
    (m : ℝ) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      (((A N).lcm id : ℕ) : ℝ) ≤ Real.exp (((m * N) ^ 2 / N) / 4) ∧
        Real.log 4 < ((m * N) ^ 2 / N) / 4 := by
  have hC : 0 < m ^ 2 / 4 := by positivity
  have hlog := (tendsto_smooth_lcm_log_ratio A hPos a ha hSmooth).eventually (Iio_mem_nhds hC)
  have hsize : ∀ᶠ N : ℕ in atTop, Real.log 4 < (m ^ 2 / 4) * N :=
    ((tendsto_const_mul_atTop_of_pos hC).mpr tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (Real.log 4))
  filter_upwards [hlog, hsize, eventually_gt_atTop (0 : ℕ)] with N hLog hSize hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hQpos : (0 : ℝ) < (A N).lcm id := by
    exact_mod_cast Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos N n hn).ne'))
  have heq : ((m * N) ^ 2 / (N : ℝ)) / 4 = (m ^ 2 / 4) * N := by
    field_simp [hNR.ne']
  rw [heq]
  exact ⟨(Real.log_le_iff_le_exp hQpos).mp ((div_lt_iff₀ hNR).mp hLog).le, hSize⟩

noncomputable def coprimePrefix (D N : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (1 + N)).filter (fun n => D.Coprime n)

theorem coprime_complete_blocks (D k : ℕ) :
    ((Finset.Ico 1 (1 + k * D)).filter (fun n => D.Coprime n)).card = k * D.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : 1 + (k + 1) * D = (1 + k * D) + D := by ring
    have hu : Finset.Ico 1 ((1 + k * D) + D) =
        Finset.Ico 1 (1 + k * D) ∪ Finset.Ico (1 + k * D) ((1 + k * D) + D) := by
      exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
    have hd : Disjoint
        ((Finset.Ico 1 (1 + k * D)).filter (fun n => D.Coprime n))
        ((Finset.Ico (1 + k * D) ((1 + k * D) + D)).filter (fun n => D.Coprime n)) := by
      apply Finset.disjoint_left.mpr
      intro n hleft hright
      have hl := (Finset.mem_Ico.mp (Finset.mem_filter.mp hleft).1).2
      have hr := (Finset.mem_Ico.mp (Finset.mem_filter.mp hright).1).1
      exact (not_lt_of_ge hr) hl
    rw [heq, hu, Finset.filter_union, Finset.card_union_of_disjoint hd, ih,
      Nat.filter_coprime_Ico_eq_totient]
    ring

theorem coprimePrefix_card_bounds (D N : ℕ) (hD : 0 < D) :
    D.totient * (N / D) ≤ (coprimePrefix D N).card ∧
      (coprimePrefix D N).card ≤ D.totient * (N / D + 1) := by
  constructor
  · have hsub : (Finset.Ico 1 (1 + (N / D) * D)).filter (fun n => D.Coprime n) ⊆
        coprimePrefix D N := by
      apply Finset.filter_subset_filter
      apply Finset.Ico_subset_Ico le_rfl
      exact Nat.add_le_add_left (Nat.div_mul_le_self N D) 1
    have hh := Finset.card_le_card hsub
    rw [coprime_complete_blocks] at hh
    simpa only [mul_comm] using hh
  · exact Nat.Ico_filter_coprime_le 1 N hD.ne'

theorem coprimePrefix_card_error (D N : ℕ) (hD : 0 < D) :
    |((coprimePrefix D N).card : ℝ) - coprimeDensity D * N| ≤ D.totient := by
  have hb := coprimePrefix_card_bounds D N hD
  have hlo : (D.totient : ℝ) * (N / D : ℕ) ≤ (coprimePrefix D N).card := by exact_mod_cast hb.1
  have hhi : ((coprimePrefix D N).card : ℝ) ≤ (D.totient : ℝ) * ((N / D : ℕ) + 1) := by
    exact_mod_cast hb.2
  have hfloor : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / D := Nat.cast_div_le
  have hfloorUpper : (N : ℝ) / D < ((N / D : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using Nat.lt_floor_add_one ((N : ℝ) / D)
  have hφ : (0 : ℝ) ≤ D.totient := Nat.cast_nonneg _
  have hmlo := mul_le_mul_of_nonneg_left hfloor hφ
  have hmhi := mul_le_mul_of_nonneg_left hfloorUpper.le hφ
  have heq : coprimeDensity D * N = (D.totient : ℝ) * ((N : ℝ) / D) := by
    unfold coprimeDensity
    ring
  rw [heq, abs_le]
  constructor <;> nlinarith

theorem tendsto_coprimePrefix_density (D : ℕ) (hD : 0 < D) :
    Tendsto (fun N : ℕ => (coprimePrefix D N).card / (N : ℝ)) atTop (𝓝 (coprimeDensity D)) := by
  have hlim : Tendsto (fun N : ℕ => (D.totient : ℝ) / N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.const_mul (D.totient : ℝ))
  have herror : Tendsto (fun N : ℕ => (coprimePrefix D N).card / (N : ℝ) - coprimeDensity D)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have heq : (coprimePrefix D N).card / (N : ℝ) - coprimeDensity D =
        ((coprimePrefix D N).card - coprimeDensity D * N) / N := by
      field_simp [hNR.ne']
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hNR]
    exact div_le_div_of_nonneg_right (coprimePrefix_card_error D N hD) hNR.le
  simpa only [zero_add, sub_add_cancel] using herror.add_const (coprimeDensity D)

theorem coprimePrefix_eq_filter_Icc (D N : ℕ) :
    coprimePrefix D N = (Finset.Icc 1 N).filter (fun n => D.Coprime n) := by
  unfold coprimePrefix
  congr 1
  ext n
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ Finset.range N, f (i + 1)) = ∑ n ∈ Finset.Icc 1 N, f n := by
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    have hh := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj heq
    omega
  · intro n hn
    have hh := Finset.mem_Icc.mp hn
    exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

noncomputable def coprimeCenteredWeight (D n : ℕ) : ℝ :=
  (if D.Coprime n then 1 else 0) - coprimeDensity D

theorem coprimeCenteredWeight_prefix (D N : ℕ) :
    (∑ i ∈ Finset.range N, coprimeCenteredWeight D (i + 1)) =
      (coprimePrefix D N).card - coprimeDensity D * (N : ℝ) := by
  rw [sum_range_succ_eq_sum_Icc]
  simp only [coprimeCenteredWeight, Finset.sum_sub_distrib]
  rw [Finset.sum_boole, ← coprimePrefix_eq_filter_Icc]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  rw [Nat.add_sub_cancel]
  ring

theorem coprime_weighted_correction (D N : ℕ) :
    (reciprocalSum (coprimePrefix D N) : ℝ) -
        coprimeDensity D * (reciprocalSum (Finset.Icc 1 N) : ℝ) =
      ∑ i ∈ Finset.range N, ((1 : ℝ) / (i + 1 : ℕ)) * coprimeCenteredWeight D (i + 1) := by
  symm
  rw [sum_range_succ_eq_sum_Icc (fun n : ℕ => ((1 : ℝ) / n) * coprimeCenteredWeight D n) N]
  rw [reciprocalSum_real, reciprocalSum_real, coprimePrefix_eq_filter_Icc, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  unfold coprimeCenteredWeight
  split_ifs <;> ring

theorem exists_coprime_harmonic_correction_limit (D : ℕ) (hD : 0 < D) :
    ∃ L : ℝ, Tendsto (fun N : ℕ =>
      (reciprocalSum (coprimePrefix D N) : ℝ) -
        coprimeDensity D * (reciprocalSum (Finset.Icc 1 N) : ℝ)) atTop (𝓝 L) := by
  let f := fun i : ℕ => (1 : ℝ) / (i + 1 : ℕ)
  let z := fun i : ℕ => coprimeCenteredWeight D (i + 1)
  have hAnti : Antitone f := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hij
  have hf0 : Tendsto f atTop (𝓝 0) := by
    simpa only [f, one_div, Function.comp_def, Pi.inv_def] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
  have hBound : ∀ N, ‖∑ i ∈ Finset.range N, z i‖ ≤ (D.totient : ℝ) := by
    intro N
    rw [show z = (fun i => coprimeCenteredWeight D (i + 1)) from rfl,
      coprimeCenteredWeight_prefix, Real.norm_eq_abs]
    exact coprimePrefix_card_error D N hD
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (hAnti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hBound)
  refine ⟨L, ?_⟩
  simpa only [coprime_weighted_correction, f, z, smul_eq_mul] using hL

theorem exists_coprime_reciprocal_log_limit (D : ℕ) (hD : 0 < D) :
    ∃ L : ℝ, Tendsto (fun N : ℕ =>
      (reciprocalSum (coprimePrefix D N) : ℝ) - coprimeDensity D * Real.log N) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_coprime_harmonic_correction_limit D hD
  have hH : Tendsto (fun N : ℕ =>
      (reciprocalSum (Finset.Icc 1 N) : ℝ) - Real.log N) atTop (𝓝 euler_mascheroni) := by
    simpa only [reciprocalSum_real, one_div] using harmonic_series_limit
  have hlim := hL.add (hH.const_mul (coprimeDensity D))
  refine ⟨L + coprimeDensity D * euler_mascheroni, ?_⟩
  apply hlim.congr'
  filter_upwards with N using by ring

noncomputable def coprimeWindow (D : ℕ) (c : ℝ) (N : ℕ) : Finset ℕ :=
  coprimePrefix D N \ coprimePrefix D ⌊c * N⌋₊

theorem coprimePrefix_mono (D : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    coprimePrefix D M ⊆ coprimePrefix D N := by
  rw [coprimePrefix_eq_filter_Icc, coprimePrefix_eq_filter_Icc]
  exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hMN)

theorem floor_scaled_le (c : ℝ) (hc : c ≤ 1) (N : ℕ) : ⌊c * N⌋₊ ≤ N := by
  apply Nat.floor_le_of_le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)

theorem coprimeWindow_card (D : ℕ) (c : ℝ) (hc : c ≤ 1) (N : ℕ) :
    ((coprimeWindow D c N).card : ℝ) =
      (coprimePrefix D N).card - (coprimePrefix D ⌊c * N⌋₊).card := by
  have hSub := coprimePrefix_mono D (floor_scaled_le c hc N)
  have hh : (coprimeWindow D c N).card + (coprimePrefix D ⌊c * N⌋₊).card =
      (coprimePrefix D N).card := by
    simpa [coprimeWindow] using
      (Finset.sum_sdiff hSub (f := fun _ : ℕ => (1 : ℕ)))
  have hhR : ((coprimeWindow D c N).card : ℝ) + (coprimePrefix D ⌊c * N⌋₊).card =
      (coprimePrefix D N).card := by exact_mod_cast hh
  linarith only [hhR]

theorem coprimeWindow_reciprocal (D : ℕ) (c : ℝ) (hc : c ≤ 1) (N : ℕ) :
    reciprocalSum (coprimeWindow D c N) =
      reciprocalSum (coprimePrefix D N) - reciprocalSum (coprimePrefix D ⌊c * N⌋₊) := by
  have hSub := coprimePrefix_mono D (floor_scaled_le c hc N)
  have hh := Finset.sum_sdiff hSub (f := fun n : ℕ => (n : ℚ)⁻¹)
  change reciprocalSum (coprimeWindow D c N) + reciprocalSum (coprimePrefix D ⌊c * N⌋₊) =
    reciprocalSum (coprimePrefix D N) at hh
  linarith only [hh]

theorem tendsto_floor_scaled (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => ⌊c * N⌋₊) atTop atTop := by
  simpa only [Function.comp_def] using tendsto_nat_floor_atTop.comp
    ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_natCast_atTop_atTop)

theorem tendsto_floor_scaled_ratio (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => (⌊c * N⌋₊ : ℝ) / N) atTop (𝓝 c) := by
  simpa only [Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop hc).comp tendsto_natCast_atTop_atTop

theorem tendsto_coprimeWindow_density (D : ℕ) (hD : 0 < D) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℕ => (coprimeWindow D c N).card / (N : ℝ))
      atTop (𝓝 (coprimeDensity D * (1 - c))) := by
  have hFloor := tendsto_floor_scaled c hc
  have hFloorRatio := tendsto_floor_scaled_ratio c hc.le
  have hProduct := ((tendsto_coprimePrefix_density D hD).comp hFloor).mul hFloorRatio
  have hLower : Tendsto (fun N : ℕ => (coprimePrefix D ⌊c * N⌋₊).card / (N : ℝ))
      atTop (𝓝 (coprimeDensity D * c)) := by
    apply hProduct.congr'
    filter_upwards [hFloor.eventually (eventually_gt_atTop (0 : ℕ)),
      eventually_gt_atTop (0 : ℕ)] with N hF hN
    have hFR : (⌊c * N⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hF.ne'
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp only [Function.comp_def]
    field_simp [hFR, hNR]
  have hlim := (tendsto_coprimePrefix_density D hD).sub hLower
  rw [show coprimeDensity D - coprimeDensity D * c = coprimeDensity D * (1 - c) by ring] at hlim
  apply hlim.congr'
  filter_upwards with N using by rw [coprimeWindow_card D c hc1 N]; ring

theorem tendsto_scaled_log_difference (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log N - Real.log (⌊c * N⌋₊ : ℝ)) atTop (𝓝 (-Real.log c)) := by
  have hFloor := tendsto_floor_scaled c hc
  have hlim := ((Real.continuousAt_log hc.ne').tendsto.comp (tendsto_floor_scaled_ratio c hc.le)).neg
  apply hlim.congr'
  filter_upwards [hFloor.eventually (eventually_gt_atTop (0 : ℕ)),
      eventually_gt_atTop (0 : ℕ)] with N hF hN
  have hFR : (⌊c * N⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hF.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [Function.comp_def]
  rw [Real.log_div hFR hNR]
  ring

theorem tendsto_coprimeWindow_reciprocal (D : ℕ) (hD : 0 < D) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℕ => (reciprocalSum (coprimeWindow D c N) : ℝ))
      atTop (𝓝 (coprimeDensity D * Real.log (1 / c))) := by
  obtain ⟨L, hL⟩ := exists_coprime_reciprocal_log_limit D hD
  have hDifference := hL.sub (hL.comp (tendsto_floor_scaled c hc))
  simp only [sub_self] at hDifference
  have hError : Tendsto (fun N : ℕ => (reciprocalSum (coprimeWindow D c N) : ℝ) -
      coprimeDensity D * (Real.log N - Real.log (⌊c * N⌋₊ : ℝ))) atTop (𝓝 0) := by
    apply hDifference.congr'
    filter_upwards with N
    rw [coprimeWindow_reciprocal D c hc1 N, Rat.cast_sub]
    dsimp only [Function.comp_def]
    ring
  have hlim := hError.add ((tendsto_scaled_log_difference c hc).const_mul (coprimeDensity D))
  simp only [zero_add] at hlim
  rw [one_div, Real.log_inv]
  apply hlim.congr'
  filter_upwards with N using by ring

theorem mem_coprimeWindow_iff (D : ℕ) (c : ℝ) (hc : 0 ≤ c) (N n : ℕ) :
    n ∈ coprimeWindow D c N ↔ 1 ≤ n ∧ n ≤ N ∧ D.Coprime n ∧ c * N < (n : ℝ) := by
  rw [coprimeWindow, Finset.mem_sdiff, coprimePrefix_eq_filter_Icc, coprimePrefix_eq_filter_Icc]
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hcN : 0 ≤ c * (N : ℝ) := mul_nonneg hc (Nat.cast_nonneg N)
  constructor
  · rintro ⟨⟨⟨hn1, hnN⟩, hcop⟩, hnot⟩
    refine ⟨hn1, hnN, hcop, lt_of_not_ge ?_⟩
    intro hnlow
    exact hnot ⟨⟨hn1, (Nat.le_floor_iff hcN).mpr hnlow⟩, hcop⟩
  · rintro ⟨hn1, hnN, hcop, hnlow⟩
    refine ⟨⟨⟨hn1, hnN⟩, hcop⟩, ?_⟩
    rintro ⟨⟨_hn1, hnfloor⟩, _hcop⟩
    exact (not_le_of_gt hnlow) ((Nat.le_floor_iff hcN).mp hnfloor)

theorem nat_cast_sub_lower (u v : ℕ) : (u : ℝ) - v ≤ ((u - v : ℕ) : ℝ) := by
  by_cases h : v ≤ u
  · rw [Nat.cast_sub h]
  · have h' : u ≤ v := (lt_of_not_ge h).le
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast h')

set_option maxHeartbeats 800000 in
theorem coprimeWindow_divisor_card_lower (D q : ℕ) (hD : 0 < D) (hq : 0 < q)
    (hcop : q.Coprime D) (c : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    ((1 - c) / ((q : ℝ) * D)) * N - 2 ≤
      (((coprimeWindow D c N).filter (fun n => q ∣ n)).card : ℝ) := by
  classical
  let T := q * D
  let M := N / T
  let L := ⌊c * N / (T : ℝ)⌋₊
  let K := Finset.Icc (L + 1) (M - 1)
  have hT : 0 < T := Nat.mul_pos hq hD
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hqT : q ≤ T := by
    dsimp [T]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hD
  have hinj : Function.Injective (fun k : ℕ => T * k + q) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hT (Nat.add_right_cancel hij)
  have hImage : K.image (fun k => T * k + q) ⊆
      (coprimeWindow D c N).filter (fun n => q ∣ n) := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hkI := Finset.mem_Icc.mp hk
    have hkplus : k + 1 ≤ M := by omega
    have hTop : T * (k + 1) ≤ N := by
      have hh := Nat.mul_le_mul_left T hkplus
      have hdiv : T * M ≤ N := by simpa only [M, mul_comm] using Nat.div_mul_le_self N T
      exact hh.trans hdiv
    have hnTop : T * k + q ≤ N := by
      calc
        _ ≤ T * k + T := Nat.add_le_add_left hqT _
        _ = T * (k + 1) := by ring
        _ ≤ _ := hTop
    have hFloor : c * (N : ℝ) / T < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkR : (L : ℝ) + 1 ≤ k := by exact_mod_cast hkI.1
    have hnLow : c * N < ((T * k + q : ℕ) : ℝ) := by
      have hh := (div_lt_iff₀ hTR).mp (hFloor.trans_le hkR)
      push_cast
      nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
    have hform : T * k + q = q * (D * k + 1) := by dsimp [T]; ring
    have hDc : D.Coprime (D * k + 1) := by simp [Nat.coprime_mul_left_add_right]
    have hnCop : D.Coprime (T * k + q) := by
      rw [hform]
      exact Nat.Coprime.mul_right hcop.symm hDc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_coprimeWindow_iff D c hc N _).mpr ⟨by omega, hnTop, hnCop, hnLow⟩, ?_⟩
    exact ⟨D * k + 1, hform⟩
  have hCardNat := Finset.card_le_card hImage
  rw [Finset.card_image_of_injective K hinj] at hCardNat
  have hCard : (K.card : ℝ) ≤ ((coprimeWindow D c N).filter (fun n => q ∣ n)).card := by
    exact_mod_cast hCardNat
  have hKLower : (M : ℝ) - L - 1 ≤ K.card := by
    have h1 := nat_cast_sub_lower ((M - 1) + 1) (L + 1)
    have h2 := nat_cast_sub_lower M 1
    simp only [Nat.cast_add, Nat.cast_one] at h1 h2
    dsimp [K]
    rw [Nat.card_Icc]
    linarith
  have hMLower : (N : ℝ) / T - 1 ≤ M := by
    have hh := Nat.lt_floor_add_one ((N : ℝ) / T)
    rw [Nat.floor_div_eq_div] at hh
    dsimp [M]
    linarith
  have hLUpper : (L : ℝ) ≤ c * N / T := Nat.floor_le
    (div_nonneg (mul_nonneg hc (Nat.cast_nonneg N)) hTR.le)
  have hResult : ((1 - c) / (T : ℝ)) * N - 2 ≤
      (((coprimeWindow D c N).filter (fun n => q ∣ n)).card : ℝ) := by
    calc
      _ = (N : ℝ) / T - 1 - c * N / T - 1 := by ring
      _ ≤ (M : ℝ) - L - 1 := by linarith only [hMLower, hLUpper]
      _ ≤ (K.card : ℝ) := hKLower
      _ ≤ _ := hCard
  simpa only [T, Nat.cast_mul] using hResult

theorem coprimeWindow_subset (D : ℕ) (c : ℝ) (N : ℕ) :
    coprimeWindow D c N ⊆ Finset.Icc 1 N := by
  exact Finset.sdiff_subset.trans (by rw [coprimePrefix_eq_filter_Icc]; exact Finset.filter_subset _ _)

theorem coprimeWindow_divisor_mass_positive (D q : ℕ) (hD : 0 < D) (hq : 0 < q)
    (hcop : q.Coprime D) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ ≤ (reciprocalSum ((coprimeWindow D c N).filter (fun n => q ∣ n)) : ℝ) := by
  let α := (1 - c) / ((q : ℝ) * D)
  have hα : 0 < α := by
    dsimp [α]
    exact div_pos (sub_pos.mpr hc1) (mul_pos (by exact_mod_cast hq) (by exact_mod_cast hD))
  have hlim : Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (tendsto_natCast_atTop_atTop.inv_tendsto_atTop.const_mul (2 : ℝ))
  have hSmall := hlim.eventually (Iio_mem_nhds (half_pos hα))
  refine ⟨α / 2, half_pos hα, ?_⟩
  filter_upwards [hSmall, eventually_gt_atTop (0 : ℕ)] with N hNsmall hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hSmallMul := (div_lt_iff₀ hNR).mp hNsmall
  have hLow : α * N - 2 ≤ (((coprimeWindow D c N).filter (fun n => q ∣ n)).card : ℝ) :=
    coprimeWindow_divisor_card_lower D q hD hq hcop c hc N
  have hHigh := card_le_N_mul_reciprocalSum
    ((Finset.filter_subset (fun n => q ∣ n) (coprimeWindow D c N)).trans (coprimeWindow_subset D c N))
  apply (mul_le_mul_iff_left₀ hNR).mp
  nlinarith only [hLow, hHigh, hSmallMul]

theorem eventually_denominator_dvd_cleaned_lcm_of_lower_bounds
    (A F : ℕ → Finset ℕ) (b : ℕ) (hb : 0 < b) (hSub : ∀ N, F N ⊆ A N)
    (hLocal : ∀ q : ℕ, IsPrimePow q → q ∣ b → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ ≤ (reciprocalSum ((A N).filter (fun n => q ∣ n)) : ℝ))
    (hLoss : Tendsto (fun N =>
      (reciprocalSum (A N) : ℝ) - (reciprocalSum (F N) : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, b ∣ (F N).lcm id := by
  classical
  let S := b.divisors.filter IsPrimePow
  have hClasses : ∀ q ∈ S, ∀ᶠ N : ℕ in atTop, ∃ n ∈ F N, q ∣ n := by
    intro q hq
    have hh := Finset.mem_filter.mp hq
    obtain ⟨δ, hδ, hLower⟩ := hLocal q hh.2 (Nat.mem_divisors.mp hh.1).1
    have hSmall := hLoss.eventually (Iio_mem_nhds hδ)
    filter_upwards [hLower, hSmall] with N hNlow hNsmall
    exact divisor_class_survives_small_loss (A N) (F N) q (hSub N) (hNsmall.trans_le hNlow)
  have hAll := (Filter.eventually_all_finset S).mpr hClasses
  filter_upwards [hAll] with N hN
  apply divisor_dvd_lcm_of_primePower_classes b (F N)
  intro q hqpp hqb
  exact hN q (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqb, hb.ne'⟩, hqpp⟩)

theorem exists_regular_coprimeWindow (D : ℕ) (hD : 0 < D) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (a : ℝ) (ha : 0 ≤ a) (b : ℕ) (hb : 0 < b) (hbD : b.Coprime D) :
    ∃ F : ℕ → Finset ℕ, (∀ N, F N ⊆ coprimeWindow D c N) ∧
      (∀ N n, n ∈ F N → PrimePowerSmooth (smoothCutoff a N) n) ∧
      (∀ N n, n ∈ F N → (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) ∧
      (∀ N q, IsPrimePow q → (∃ n ∈ F N, q ∣ n) →
        ((Real.log (Real.log N)) ^ 2)⁻¹ ≤
          (q : ℝ) * (reciprocalSum ((F N).filter (fun n => q ∣ n)) : ℝ)) ∧
      Tendsto (fun N => (reciprocalSum (F N) : ℝ))
        atTop (𝓝 (coprimeDensity D * Real.log (1 / c))) ∧
      Tendsto (fun N => (F N).card / (N : ℝ)) atTop (𝓝 (coprimeDensity D * (1 - c))) ∧
      (∀ᶠ N : ℕ in atTop, b ∣ (F N).lcm id) := by
  let A := fun N => coprimeWindow D c N
  have hA : ∀ N, A N ⊆ Finset.Icc 1 N := coprimeWindow_subset D c
  have hmin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, c * N ≤ (n : ℝ) := by
    apply Filter.Eventually.of_forall
    intro N n hn
    exact ((mem_coprimeWindow_iff D c hc.le N n).mp hn).2.2.2.le
  obtain ⟨F, hSub, hSmooth, hMultiplicity, hRich, hLoss⟩ :=
    exists_regular_cleaning_sequence A hA c hc hmin a ha
  refine ⟨F, hSub, hSmooth, hMultiplicity, hRich, ?_, ?_, ?_⟩
  · exact cleaning_preserves_reciprocal_limit A F _
      (tendsto_coprimeWindow_reciprocal D hD c hc hc1.le) hLoss
  · exact cleaning_preserves_card_density A F _ hA hSub
      (tendsto_coprimeWindow_density D hD c hc hc1.le) hLoss
  · apply eventually_denominator_dvd_cleaned_lcm_of_lower_bounds A F b hb hSub ?_ hLoss
    intro q hqpp hqb
    exact coprimeWindow_divisor_mass_positive D q hD hqpp.pos
      (Nat.Coprime.of_dvd_left hqb hbD) c hc.le hc1

theorem sum_powerset_truncated_apply_card {ι M : Type*} [AddCommMonoid M]
    (P : Finset ι) (K : ℕ) (f : ℕ → M) :
    (∑ B ∈ P.powerset.filter (fun B => B.card ≤ K), f B.card) =
      ∑ j ∈ Finset.range (K + 1), P.card.choose j • f j := by
  classical
  trans ∑ j ∈ Finset.range (K + 1),
    ∑ B ∈ (P.powerset.filter (fun B => B.card ≤ K)).filter (fun B => B.card = j), f B.card
  · refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro B hB
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hB).2)
  · apply Finset.sum_congr rfl
    intro j hj
    have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hsets : (P.powerset.filter (fun B => B.card ≤ K)).filter (fun B => B.card = j) =
        P.powersetCard j := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hBP, _hBK⟩, hBj⟩
        exact ⟨hBP, hBj⟩
      · rintro ⟨hBP, hBj⟩
        exact ⟨⟨hBP, hBj.symm ▸ hjK⟩, hBj⟩
    rw [hsets, ← Finset.card_powersetCard, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro B hB
    rw [(Finset.mem_powersetCard.mp hB).2]

theorem bonferroni_even_truncation_int {ι : Type*} (P : Finset ι) (k : ℕ) :
    (if P = ∅ then (1 : ℤ) else 0) ≤
      ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k), (-1 : ℤ) ^ B.card := by
  classical
  by_cases hP : P = ∅
  · subst P
    rw [Finset.sum_filter]
    simp
  · rw [ite_eq_right hP, sum_powerset_truncated_apply_card]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hP))
    rw [hn]
    simp only [nsmul_eq_mul]
    have hsum : (∑ j ∈ Finset.range (2 * k + 1), ((n + 1).choose j : ℤ) * (-1) ^ j) =
        (n.choose (2 * k) : ℤ) := by
      calc
        _ = ∑ j ∈ Finset.range (2 * k + 1), (-1 : ℤ) ^ j * (n + 1).choose j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (-1 : ℤ) ^ (2 * k) * n.choose (2 * k) := Int.alternating_sum_range_choose_eq_choose
        _ = _ := by simp only [pow_mul, neg_one_sq, one_pow, one_mul]
    rw [hsum]
    positivity

theorem bonferroni_even_upper {ι : Type*} (P : Finset ι) (E : ι → Prop) (k : ℕ) :
    (if ∀ i ∈ P, ¬ E i then (1 : ℝ) else 0) ≤
      ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
        (-1 : ℝ) ^ B.card * (if ∀ i ∈ B, E i then 1 else 0) := by
  classical
  let D := P.filter E
  have hEmpty : D = ∅ ↔ ∀ i ∈ P, ¬ E i := Finset.filter_eq_empty_iff
  have hsets : D.powerset.filter (fun B => B.card ≤ 2 * k) =
      (P.powerset.filter (fun B => B.card ≤ 2 * k)).filter (fun B => ∀ i ∈ B, E i) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hBD, hcard⟩
      refine ⟨⟨fun i hi => (Finset.mem_filter.mp (hBD hi)).1, hcard⟩, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hBD hi)).2
    · rintro ⟨⟨hBP, hcard⟩, hBE⟩
      exact ⟨fun i hi => Finset.mem_filter.mpr ⟨hBP hi, hBE i hi⟩, hcard⟩
  have hReal : (if D = ∅ then (1 : ℝ) else 0) ≤
      ∑ B ∈ D.powerset.filter (fun B => B.card ≤ 2 * k), (-1 : ℝ) ^ B.card := by
    exact_mod_cast bonferroni_even_truncation_int D k
  simp only [hEmpty, hsets, Finset.sum_filter] at hReal
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_filter] using hReal

theorem bonferroni_count_upper {ι : Type*} (A : Finset ℕ) (P : Finset ι)
    (E : ι → ℕ → Prop) (k : ℕ) :
    ((A.filter (fun n => ∀ i ∈ P, ¬ E i n)).card : ℝ) ≤
      ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
        (-1 : ℝ) ^ B.card * ((A.filter (fun n => ∀ i ∈ B, E i n)).card : ℝ) := by
  classical
  rw [Finset.natCast_card_filter]
  calc
    _ ≤ ∑ n ∈ A, ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
        (-1 : ℝ) ^ B.card * (if ∀ i ∈ B, E i n then 1 else 0) :=
      Finset.sum_le_sum (fun n hn => bonferroni_even_upper P (fun i => E i n) k)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [← Finset.mul_sum, Finset.sum_boole]

theorem powerset_weight_tail_bound {ι : Type*} (P : Finset ι) (u : ι → ℝ) (K : ℕ)
    (hu : ∀ i ∈ P, 0 ≤ u i) :
    (∑ B ∈ P.powerset.filter (fun B => K < B.card), ∏ i ∈ B, u i) ≤
      Real.exp (2 * ∑ i ∈ P, u i) / (2 : ℝ) ^ K := by
  classical
  have hpow : (0 : ℝ) < 2 ^ K := by positivity
  apply (le_div_iff₀ hpow).mpr
  calc
    _ = ∑ B ∈ P.powerset.filter (fun B => K < B.card), (∏ i ∈ B, u i) * (2 : ℝ) ^ K :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ B ∈ P.powerset.filter (fun B => K < B.card), ∏ i ∈ B, 2 * u i := by
      apply Finset.sum_le_sum
      intro B hB
      have hBP := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
      have hKB := (Finset.mem_filter.mp hB).2.le
      have hnonneg : 0 ≤ ∏ i ∈ B, u i := Finset.prod_nonneg (fun i hi => hu i (hBP hi))
      have hscale : (2 : ℝ) ^ K ≤ 2 ^ B.card := pow_le_pow_right₀ (by norm_num) hKB
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hscale hnonneg
    _ ≤ ∑ B ∈ P.powerset, ∏ i ∈ B, 2 * u i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro B hB hBnot
      have hBP := Finset.mem_powerset.mp hB
      exact Finset.prod_nonneg (fun i hi => mul_nonneg (by norm_num) (hu i (hBP hi)))
    _ = ∏ i ∈ P, (1 + 2 * u i) := (Finset.prod_one_add P).symm
    _ ≤ ∏ i ∈ P, Real.exp (2 * u i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hh := hu i hi
        positivity
      · intro i hi
        simpa only [add_comm] using Real.add_one_le_exp (2 * u i)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

noncomputable def truncatedEulerProduct {ι : Type*} (P : Finset ι) (u : ι → ℝ) (K : ℕ) : ℝ :=
  ∑ B ∈ P.powerset.filter (fun B => B.card ≤ K), (-1 : ℝ) ^ B.card * ∏ i ∈ B, u i

theorem truncatedEulerProduct_error {ι : Type*} (P : Finset ι) (u : ι → ℝ) (K : ℕ)
    (hu : ∀ i ∈ P, 0 ≤ u i) :
    |truncatedEulerProduct P u K - ∏ i ∈ P, (1 - u i)| ≤
      Real.exp (2 * ∑ i ∈ P, u i) / (2 : ℝ) ^ K := by
  classical
  have hprod : (∏ i ∈ P, (1 - u i)) =
      ∑ B ∈ P.powerset, (-1 : ℝ) ^ B.card * ∏ i ∈ B, u i := by
    simpa only [Finset.prod_const_one, mul_one] using Finset.prod_sub (fun _ => (1 : ℝ)) u P
  have hsplit := Finset.sum_filter_add_sum_filter_not P.powerset
    (fun B => B.card ≤ K) (fun B => (-1 : ℝ) ^ B.card * ∏ i ∈ B, u i)
  simp only [not_le] at hsplit
  have herror : truncatedEulerProduct P u K - ∏ i ∈ P, (1 - u i) =
      -(∑ B ∈ P.powerset.filter (fun B => K < B.card), (-1 : ℝ) ^ B.card * ∏ i ∈ B, u i) := by
    rw [hprod]
    unfold truncatedEulerProduct
    linarith only [hsplit]
  rw [herror, abs_neg]
  calc
    _ ≤ ∑ B ∈ P.powerset.filter (fun B => K < B.card),
        |(-1 : ℝ) ^ B.card * ∏ i ∈ B, u i| := abs_sum_le_sum_abs _ _
    _ = ∑ B ∈ P.powerset.filter (fun B => K < B.card), ∏ i ∈ B, u i := by
      apply Finset.sum_congr rfl
      intro B hB
      have hBP := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
      have hnonneg : 0 ≤ ∏ i ∈ B, u i := Finset.prod_nonneg (fun i hi => hu i (hBP hi))
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hnonneg]
    _ ≤ _ := powerset_weight_tail_bound P u K hu

theorem finite_brun_upper_bound {ι : Type*} (A : Finset ℕ) (P : Finset ι)
    (E : ι → ℕ → Prop) (u : ι → ℝ) (k : ℕ) (X R : ℝ)
    (hX : 0 ≤ X) (hu : ∀ i ∈ P, 0 ≤ u i)
    (hApprox : ∀ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
      |((A.filter (fun n => ∀ i ∈ B, E i n)).card : ℝ) - X * ∏ i ∈ B, u i| ≤ R) :
    ((A.filter (fun n => ∀ i ∈ P, ¬ E i n)).card : ℝ) ≤
      X * (∏ i ∈ P, (1 - u i)) + X * Real.exp (2 * ∑ i ∈ P, u i) / (2 : ℝ) ^ (2 * k) +
        R * (P.powerset.filter (fun B => B.card ≤ 2 * k)).card := by
  classical
  let F := P.powerset.filter (fun B => B.card ≤ 2 * k)
  have hterm : ∀ B ∈ F,
      (-1 : ℝ) ^ B.card * ((A.filter (fun n => ∀ i ∈ B, E i n)).card : ℝ) ≤
        X * ((-1 : ℝ) ^ B.card * ∏ i ∈ B, u i) + R := by
    intro B hB
    have hAbs : |(-1 : ℝ) ^ B.card *
        (((A.filter (fun n => ∀ i ∈ B, E i n)).card : ℝ) - X * ∏ i ∈ B, u i)| ≤ R := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hApprox B hB
    have hUpper := (le_abs_self _).trans hAbs
    nlinarith only [hUpper]
  have hsum : (∑ B ∈ F, (-1 : ℝ) ^ B.card * ((A.filter (fun n => ∀ i ∈ B, E i n)).card : ℝ)) ≤
      X * truncatedEulerProduct P u (2 * k) + R * F.card := by
    calc
      _ ≤ ∑ B ∈ F, (X * ((-1 : ℝ) ^ B.card * ∏ i ∈ B, u i) + R) := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [truncatedEulerProduct, F, mul_comm]
  have hError := (abs_le.mp (truncatedEulerProduct_error P u (2 * k) hu)).2
  have hMain : truncatedEulerProduct P u (2 * k) ≤
      (∏ i ∈ P, (1 - u i)) + Real.exp (2 * ∑ i ∈ P, u i) / (2 : ℝ) ^ (2 * k) := by linarith
  calc
    _ ≤ ∑ B ∈ F, (-1 : ℝ) ^ B.card * ((A.filter (fun n => ∀ i ∈ B, E i n)).card : ℝ) :=
      bonferroni_count_upper A P E k
    _ ≤ X * truncatedEulerProduct P u (2 * k) + R * F.card := hsum
    _ ≤ X * ((∏ i ∈ P, (1 - u i)) + Real.exp (2 * ∑ i ∈ P, u i) / (2 : ℝ) ^ (2 * k)) +
        R * F.card := add_le_add (mul_le_mul_of_nonneg_left hMain hX) le_rfl
    _ = _ := by dsimp [F]; ring

theorem eulerProduct_le_exp_neg_sum {ι : Type*} (P : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ P, u i ≤ 1) :
    (∏ i ∈ P, (1 - u i)) ≤ Real.exp (-(∑ i ∈ P, u i)) := by
  calc
    _ ≤ ∏ i ∈ P, Real.exp (-u i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact sub_nonneg.mpr (hu i hi)
      · intro i hi
        simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-u i)
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem sieve_prime_product_dvd_iff (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) (n : ℕ) :
    (∏ p ∈ B, p) ∣ n ↔ ∀ p ∈ B, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp) h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    exact (hB p hp).coprime_iff_not_dvd.mpr
      (fun hdiv => hpq ((Nat.prime_dvd_prime_iff_eq (hB p hp) (hB q hq)).mp hdiv))

theorem sieve_prime_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun B : Finset ℕ => ∏ p ∈ B, p) (P.powerset : Set (Finset ℕ)) := by
  intro B hB C hC hprod
  have hBP := Finset.mem_powerset.mp hB
  have hCP := Finset.mem_powerset.mp hC
  have hsub : ∀ U V : Finset ℕ, U ⊆ P → V ⊆ P →
      (∏ p ∈ U, p) = (∏ p ∈ V, p) → U ⊆ V := by
    intro U V hUP hVP hUV p hp
    have hdiv : p ∣ ∏ q ∈ V, q := hUV ▸ Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
    obtain ⟨q, hq, hpq⟩ := (Nat.prime_iff.mp (hP p (hUP hp))).dvd_finsetProd_iff
      (fun q : ℕ => q) |>.mp hdiv
    have heq := (Nat.prime_dvd_prime_iff_eq (hP p (hUP hp)) (hP q (hVP hq))).mp hpq
    exact heq ▸ hq
  exact Finset.Subset.antisymm (hsub B C hBP hCP hprod) (hsub C B hCP hBP hprod.symm)

theorem sieve_truncated_powerset_card_le (P : Finset ℕ) (Y K : ℕ)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y) :
    (P.powerset.filter (fun B => B.card ≤ K)).card ≤ Y ^ K := by
  classical
  let F := P.powerset.filter (fun B => B.card ≤ K)
  have hinj : Set.InjOn (fun B : Finset ℕ => ∏ p ∈ B, p) (F : Set (Finset ℕ)) :=
    (sieve_prime_product_injective P (fun p hp => (hP p hp).1)).mono (Finset.filter_subset _ _)
  have hsub : F.image (fun B => ∏ p ∈ B, p) ⊆ Finset.Icc 1 (Y ^ K) := by
    intro n hn
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hn
    have hBP := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have hBK := (Finset.mem_filter.mp hB).2
    apply Finset.mem_Icc.mpr
    constructor
    · exact Finset.one_le_prod (fun p hp => (hP p (hBP hp)).1.one_le)
    · calc
        _ ≤ ∏ _p ∈ B, Y := Finset.prod_le_prod (fun p hp => (hP p (hBP hp)).2)
        _ = Y ^ B.card := Finset.prod_const Y
        _ ≤ Y ^ K := pow_le_pow_right₀ hY hBK
  calc
    _ = (F.image (fun B => ∏ p ∈ B, p)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (Y ^ K)).card := Finset.card_le_card hsub
    _ = Y ^ K := by simp

theorem sieve_card_divisible_interval (N q : ℕ) (hq : 0 < q) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card = N / q := by
  have hcard : (Finset.Icc 1 (N / q)).card = N / q := by simp
  rw [← hcard]
  refine (Finset.card_bij (fun n _ => n * q) ?_ ?_ ?_).symm
  · intro n hn
    have hi := Finset.mem_Icc.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨one_le_mul hi.1 hq, (Nat.le_div_iff_mul_le hq).mp hi.2⟩, dvd_mul_left _ _⟩
  · intro n hn m hm heq
    exact Nat.eq_of_mul_eq_mul_right hq (by simpa only [mul_comm] using heq)
  · intro n hn
    obtain ⟨hnI, hqn⟩ := Finset.mem_filter.mp hn
    obtain ⟨m, rfl⟩ := hqn
    have hi := Finset.mem_Icc.mp hnI
    refine ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, by simp only [mul_comm]⟩
    · exact Nat.succ_le_of_lt (Nat.pos_of_mul_pos_left hi.1)
    · exact (Nat.le_div_iff_mul_le hq).mpr (by simpa only [mul_comm] using hi.2)

theorem sieve_nat_div_error (N q : ℕ) (hq : 0 < q) :
    |((N / q : ℕ) : ℝ) - (N : ℝ) / q| ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hUpper : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  have hLower : (N : ℝ) / q < ((N / q : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hqR).mpr
    have hnat : N < (N / q + 1) * q := by
      simpa only [mul_comm] using Nat.lt_mul_div_succ N hq
    exact_mod_cast hnat
  rw [abs_le]
  constructor <;> linarith

theorem sieve_prefix_intersection_error (N : ℕ) (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) :
    |(((Finset.Icc 1 N).filter (fun n => ∀ p ∈ B, p ∣ n)).card : ℝ) -
      N * ∏ p ∈ B, (p : ℝ)⁻¹| ≤ 1 := by
  have hfilter : (Finset.Icc 1 N).filter (fun n => ∀ p ∈ B, p ∣ n) =
      (Finset.Icc 1 N).filter (fun n => (∏ p ∈ B, p) ∣ n) := by
    ext n
    simp only [Finset.mem_filter, sieve_prime_product_dvd_iff B hB]
  have hprod : 0 < ∏ p ∈ B, p := Finset.prod_pos (fun p hp => (hB p hp).pos)
  have hrecip : (∏ p ∈ B, (p : ℝ)⁻¹) = ((∏ p ∈ B, p : ℕ) : ℝ)⁻¹ := by
    simp only [Nat.cast_prod, Finset.prod_inv_distrib]
  rw [hfilter, sieve_card_divisible_interval N _ hprod, hrecip, ← div_eq_mul_inv]
  exact sieve_nat_div_error N _ hprod

theorem finite_prime_sieve_upper (N Y k : ℕ) (P : Finset ℕ)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y) :
    (((Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card : ℝ) ≤
      N * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) +
        N * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) + (Y : ℝ) ^ (2 * k) := by
  classical
  have hApprox : ∀ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
      |(((Finset.Icc 1 N).filter (fun n => ∀ p ∈ B, p ∣ n)).card : ℝ) -
        N * ∏ p ∈ B, (p : ℝ)⁻¹| ≤ 1 := by
    intro B hB
    simpa only using sieve_prefix_intersection_error N B
      (fun p hp => (hP p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) hp)).1)
  have hbrun := finite_brun_upper_bound (Finset.Icc 1 N) P (fun p n => p ∣ n)
    (fun p => (p : ℝ)⁻¹) k N 1 (Nat.cast_nonneg N)
    (fun p hp => inv_nonneg.mpr (Nat.cast_nonneg p))
    (fun B hB => by
      convert hApprox B hB using 1
      congr 4
      ext n
      simp only [Finset.mem_filter])
  have hcost : ((P.powerset.filter (fun B => B.card ≤ 2 * k)).card : ℝ) ≤
      (Y : ℝ) ^ (2 * k) := by
    exact_mod_cast sieve_truncated_powerset_card_le P Y (2 * k) hY hP
  simp only [one_mul] at hbrun
  convert hbrun.trans (add_le_add le_rfl hcost) using 1
  congr 2
  ext n
  simp only [Finset.mem_filter]

theorem finite_prime_sieve_upper_exp (N Y k : ℕ) (P : Finset ℕ)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y) :
    (((Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card : ℝ) ≤
      N * Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
        N * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) + (Y : ℝ) ^ (2 * k) := by
  have hprod : (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) :=
    eulerProduct_le_exp_neg_sum P _ (fun p hp => inv_le_one_of_one_le₀
      (by exact_mod_cast (hP p hp).1.one_le))
  exact (finite_prime_sieve_upper N Y k P hY hP).trans
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg N)) le_rfl) le_rfl)

theorem missing_primes_sieve_bound (N Y k : ℕ) (A P : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y) :
    (A.card : ℝ) ≤
      N * Real.exp (-(∑ p ∈ P.filter (fun p => ∀ n ∈ A, ¬ p ∣ n), (p : ℝ)⁻¹)) +
        N * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) + (Y : ℝ) ^ (2 * k) := by
  classical
  let M := P.filter (fun p => ∀ n ∈ A, ¬ p ∣ n)
  have hAM : A ⊆ (Finset.Icc 1 N).filter (fun n => ∀ p ∈ M, ¬ p ∣ n) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨hA hn, fun p hp => (Finset.mem_filter.mp hp).2 n hn⟩
  have hcount : (A.card : ℝ) ≤
      N * Real.exp (-(∑ p ∈ M, (p : ℝ)⁻¹)) +
        N * Real.exp (2 * ∑ p ∈ M, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) + (Y : ℝ) ^ (2 * k) := by
    have hcard : (A.card : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun n => ∀ p ∈ M, ¬ p ∣ n)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hAM
    exact hcard.trans (finite_prime_sieve_upper_exp N Y k M hY
      (fun p hp => hP p (Finset.mem_filter.mp hp).1))
  have hsum : (∑ p ∈ M, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp hpnot
    positivity
  have hError : N * Real.exp (2 * ∑ p ∈ M, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) ≤
      N * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg N)
  exact hcount.trans (add_le_add (add_le_add le_rfl hError) le_rfl)

theorem missing_primes_reciprocal_bound (N Y k : ℕ) (A P : Finset ℕ) (δ : ℝ)
    (hN : 0 < N) (hδ : 0 < δ) (hA : A ⊆ Finset.Icc 1 N)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y)
    (hDense : δ * N ≤ (A.card : ℝ))
    (hError : N * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ * N / 2) :
    (∑ p ∈ P.filter (fun p => ∀ n ∈ A, ¬ p ∣ n), (p : ℝ)⁻¹) ≤ Real.log (2 / δ) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount := missing_primes_sieve_bound N Y k A P hA hY hP
  have hHalf : δ / 2 ≤ Real.exp
      (-(∑ p ∈ P.filter (fun p => ∀ n ∈ A, ¬ p ∣ n), (p : ℝ)⁻¹)) := by
    nlinarith only [hcount, hDense, hError, hNReal]
  have hlog := Real.log_le_log (half_pos hδ) hHalf
  rw [Real.log_exp, Real.log_div (ne_of_gt hδ) (by norm_num)] at hlog
  rw [Real.log_div (by norm_num) (ne_of_gt hδ)]
  linarith only [hlog]

theorem common_prime_support_mass (A B P : Finset ℕ) :
    (∑ p ∈ P, (p : ℝ)⁻¹) -
      (∑ p ∈ P.filter (fun p => ∀ n ∈ A, ¬ p ∣ n), (p : ℝ)⁻¹) -
      (∑ p ∈ P.filter (fun p => ∀ n ∈ B, ¬ p ∣ n), (p : ℝ)⁻¹) ≤
      ∑ p ∈ P.filter (fun p => (∃ n ∈ A, p ∣ n) ∧ (∃ n ∈ B, p ∣ n)), (p : ℝ)⁻¹ := by
  classical
  have hpoint : ∀ p ∈ P, (p : ℝ)⁻¹ ≤
      (if ∀ n ∈ A, ¬ p ∣ n then (p : ℝ)⁻¹ else 0) +
      (if ∀ n ∈ B, ¬ p ∣ n then (p : ℝ)⁻¹ else 0) +
      (if (∃ n ∈ A, p ∣ n) ∧ (∃ n ∈ B, p ∣ n) then (p : ℝ)⁻¹ else 0) := by
    intro p hp
    have hnonneg : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have ha : (∀ n ∈ A, ¬ p ∣ n) ↔ ¬ (∃ n ∈ A, p ∣ n) := by simp
    have hb : (∀ n ∈ B, ¬ p ∣ n) ↔ ¬ (∃ n ∈ B, p ∣ n) := by simp
    by_cases hpa : ∃ n ∈ A, p ∣ n <;> by_cases hpb : ∃ n ∈ B, p ∣ n <;>
      simp only [ha, hb, hpa, hpb, not_true_eq_false, not_false_eq_true,
        and_self, false_and, and_false, ite_true, ite_false] <;> linarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
  linarith only [hsum]

theorem dense_sets_common_prime_support (N₁ N₂ Y k : ℕ) (A B P : Finset ℕ)
    (δ₁ δ₂ : ℝ) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hA : A ⊆ Finset.Icc 1 N₁) (hB : B ⊆ Finset.Icc 1 N₂)
    (hY : 1 ≤ Y) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y)
    (hDenseA : δ₁ * N₁ ≤ (A.card : ℝ)) (hDenseB : δ₂ * N₂ ≤ (B.card : ℝ))
    (hErrorA : N₁ * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ₁ * N₁ / 2)
    (hErrorB : N₂ * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ₂ * N₂ / 2) :
    (∑ p ∈ P, (p : ℝ)⁻¹) - Real.log (2 / δ₁) - Real.log (2 / δ₂) ≤
      ∑ p ∈ P.filter (fun p => (∃ n ∈ A, p ∣ n) ∧ (∃ n ∈ B, p ∣ n)), (p : ℝ)⁻¹ := by
  have hmissA := missing_primes_reciprocal_bound N₁ Y k A P δ₁
    hN₁ hδ₁ hA hY hP hDenseA hErrorA
  have hmissB := missing_primes_reciprocal_bound N₂ Y k B P δ₂
    hN₂ hδ₂ hB hY hP hDenseB hErrorB
  linarith only [common_prime_support_mass A B P, hmissA, hmissB]

theorem prime_support_dvd (A : Finset ℕ) (P : Finset ℕ) (x : ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hA : ∀ n ∈ A, (n : ℤ) ∣ x)
    (hSupport : ∀ p ∈ P, ∃ n ∈ A, p ∣ n) :
    ((∏ p ∈ P, p : ℕ) : ℤ) ∣ x := by
  have hindividual : ∀ p ∈ P, p ∣ x.natAbs := by
    intro p hp
    obtain ⟨n, hn, hpn⟩ := hSupport p hp
    have hpx : (p : ℤ) ∣ x := dvd_trans (by exact_mod_cast hpn) (hA n hn)
    exact Int.natCast_dvd.mp hpx
  exact Int.natCast_dvd.mpr ((sieve_prime_product_dvd_iff P hP x.natAbs).mpr hindividual)

theorem eq_of_common_prime_support (A B P : Finset ℕ) (x y : ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (hA : ∀ n ∈ A, (n : ℤ) ∣ x) (hB : ∀ n ∈ B, (n : ℤ) ∣ y)
    (hSupport : ∀ p ∈ P, (∃ n ∈ A, p ∣ n) ∧ (∃ n ∈ B, p ∣ n))
    (hSmall : (x - y).natAbs < ∏ p ∈ P, p) : x = y := by
  have hpx := prime_support_dvd A P x hP hA (fun p hp => (hSupport p hp).1)
  have hpy := prime_support_dvd B P y hP hB (fun p hp => (hSupport p hp).2)
  have hdiv : (∏ p ∈ P, p) ∣ (x - y).natAbs := Int.natCast_dvd.mp (dvd_sub hpx hpy)
  have hz : (x - y).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hSmall
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hz)

theorem sieve_product_large_of_mass (P : Finset ℕ) (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : ∀ p ∈ P, Z ≤ p) (hMass : 1 ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    Z ^ Z ≤ ∏ p ∈ P, p := by
  have hZReal : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hSum : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (P.card : ℝ) / Z := by
    calc
      _ ≤ ∑ _p ∈ P, (Z : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact inv_anti₀ hZReal (by exact_mod_cast hP p hp)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hCardReal : (Z : ℝ) ≤ P.card := by
    have hh := (le_div_iff₀ hZReal).mp (hMass.trans hSum)
    simpa only [one_mul] using hh
  have hCard : Z ≤ P.card := by exact_mod_cast hCardReal
  calc
    _ ≤ Z ^ P.card := pow_le_pow_right₀ hZ hCard
    _ = ∏ _p ∈ P, Z := (Finset.prod_const Z).symm
    _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod hP

theorem eq_of_dense_prime_support (N₁ N₂ Y k Z : ℕ) (A B P : Finset ℕ)
    (δ₁ δ₂ : ℝ) (x y : ℤ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hA : A ⊆ Finset.Icc 1 N₁) (hB : B ⊆ Finset.Icc 1 N₂)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (hP : ∀ p ∈ P, p.Prime ∧ Z ≤ p ∧ p ≤ Y)
    (hDenseA : δ₁ * N₁ ≤ (A.card : ℝ)) (hDenseB : δ₂ * N₂ ≤ (B.card : ℝ))
    (hErrorA : N₁ * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ₁ * N₁ / 2)
    (hErrorB : N₂ * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ₂ * N₂ / 2)
    (hMass : 1 ≤ (∑ p ∈ P, (p : ℝ)⁻¹) - Real.log (2 / δ₁) - Real.log (2 / δ₂))
    (hAx : ∀ n ∈ A, (n : ℤ) ∣ x) (hBy : ∀ n ∈ B, (n : ℤ) ∣ y)
    (hClose : (x - y).natAbs < Z ^ Z) : x = y := by
  classical
  let C := P.filter (fun p => (∃ n ∈ A, p ∣ n) ∧ (∃ n ∈ B, p ∣ n))
  have hC : ∀ p ∈ C, p.Prime ∧ Z ≤ p := by
    intro p hp
    have hh := hP p (Finset.mem_filter.mp hp).1
    exact ⟨hh.1, hh.2.1⟩
  have hCmass : 1 ≤ ∑ p ∈ C, (p : ℝ)⁻¹ := hMass.trans
    (dense_sets_common_prime_support N₁ N₂ Y k A B P δ₁ δ₂ hN₁ hN₂ hδ₁ hδ₂
      hA hB hY (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩) hDenseA hDenseB hErrorA hErrorB)
  have hProduct := sieve_product_large_of_mass C Z hZ (fun p hp => (hC p hp).2) hCmass
  exact eq_of_common_prime_support A B C x y (fun p hp => (hC p hp).1) hAx hBy
    (fun p hp => (Finset.mem_filter.mp hp).2) (hClose.trans_le hProduct)

noncomputable def nearbyRepresentative (h : ℤ) (n : ℕ) : ℤ :=
  h - (h : ZMod n).valMinAbs

theorem nearbyRepresentative_dvd (h : ℤ) (n : ℕ) :
    (n : ℤ) ∣ nearbyRepresentative h n := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [nearbyRepresentative, Int.cast_sub, ZMod.coe_valMinAbs, sub_self]

theorem nearbyRepresentative_distance (h : ℤ) (n : ℕ) :
    |(nearbyRepresentative h n : ℝ) - h| = |((h : ZMod n).valMinAbs : ℝ)| := by
  simp only [nearbyRepresentative, Int.cast_sub, sub_sub_cancel_left, abs_neg]

theorem nearby_multiples_unique (d : ℕ) (K c : ℝ) (x y : ℤ)
    (hK : K ≤ d) (hx : (d : ℤ) ∣ x) (hy : (d : ℤ) ∣ y)
    (hcx : |(x : ℝ) - c| < K / 2) (hcy : |(y : ℝ) - c| < K / 2) : x = y := by
  have hdiff : |(x : ℝ) - y| < (d : ℝ) := by
    calc
      _ ≤ |(x : ℝ) - c| + |(y : ℝ) - c| := by
        simpa only [abs_sub_comm c (y : ℝ)] using abs_sub_le (x : ℝ) c (y : ℝ)
      _ < K / 2 + K / 2 := add_lt_add hcx hcy
      _ = K := by ring
      _ ≤ d := hK
  have hsmall : (x - y).natAbs < d := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
    exact_mod_cast hdiff
  have hdiv : d ∣ (x - y).natAbs := Int.natCast_dvd.mp (dvd_sub hx hy)
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdiv hsmall))

theorem packet_nearby_multiple (A : Finset ℕ) (d : ℕ) (h : ℤ) (K : ℝ)
    (hne : A.Nonempty) (hK : K ≤ d) (hdiv : ∀ n ∈ A, d ∣ n)
    (hGood : ∀ n ∈ A, |((h : ZMod n).valMinAbs : ℝ)| < K / 2) :
    ∃ x : ℤ, |(x : ℝ) - h| < K / 2 ∧ (d : ℤ) ∣ x ∧ ∀ n ∈ A, (n : ℤ) ∣ x := by
  obtain ⟨n₀, hn₀⟩ := hne
  let x := nearbyRepresentative h n₀
  have hx : |(x : ℝ) - h| < K / 2 := by
    rw [nearbyRepresentative_distance]
    exact hGood n₀ hn₀
  have hdx : (d : ℤ) ∣ x := dvd_trans (by exact_mod_cast hdiv n₀ hn₀)
    (nearbyRepresentative_dvd h n₀)
  refine ⟨x, hx, hdx, ?_⟩
  intro n hn
  have hyn : |(nearbyRepresentative h n : ℝ) - h| < K / 2 := by
    rw [nearbyRepresentative_distance]
    exact hGood n hn
  have hdy : (d : ℤ) ∣ nearbyRepresentative h n := dvd_trans (by exact_mod_cast hdiv n hn)
    (nearbyRepresentative_dvd h n)
  have heq := nearby_multiples_unique d K h x (nearbyRepresentative h n) hK hdx hdy hx hyn
  rw [heq]
  exact nearbyRepresentative_dvd h n

theorem factored_reciprocal_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => ((n : ℕ) : ℝ)⁻¹)
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have hGeom : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖((p ^ j : ℕ) : ℝ)⁻¹‖) := by
    intro p hp
    have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpInv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpOne
    simpa only [Nat.cast_pow, inv_pow, Real.norm_eq_abs, abs_inv, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)] using
      summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) hpInv
  have hSeries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n : ℝ)⁻¹) (by norm_num)
    (fun {m n} _hCoprime => by simp only [Nat.cast_mul, mul_inv]) hGeom P
  have hProduct : (∏ p ∈ P.filter Nat.Prime, ∑' j : ℕ, ((p ^ j : ℕ) : ℝ)⁻¹) =
      ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [Finset.filter_eq_self.mpr hP]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [Nat.cast_pow]
    simpa only [inv_pow] using tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hP p hp).one_lt))
  rw [hProduct] at hSeries
  exact hSeries.2

theorem factored_reciprocal_sum_le (A P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ A, (n : ℝ)⁻¹) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let f : A → Nat.factoredNumbers P := fun n => ⟨n, hA n n.property⟩
  let T := A.attach.image f
  have hinj : ∀ a ∈ A.attach, ∀ b ∈ A.attach, f a = f b → a = b := by
    intro a ha b hb hab
    apply Subtype.ext
    exact congrArg (fun n : Nat.factoredNumbers P => (n : ℕ)) hab
  have hEq : (∑ n ∈ T, ((n : ℕ) : ℝ)⁻¹) = ∑ n ∈ A, (n : ℝ)⁻¹ := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_attach A (fun n => (n : ℝ)⁻¹)
  rw [← hEq]
  exact sum_le_hasSum T (fun n hn => inv_nonneg.mpr (Nat.cast_nonneg (n : ℕ)))
    (factored_reciprocal_hasSum P hP)

theorem factored_reciprocal_sum_le_euler_ratio (A P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQP : Q ⊆ P)
    (hA : ∀ n ∈ A, n ∈ Nat.factoredNumbers (P \ Q)) :
    (∑ n ∈ A, (n : ℝ)⁻¹) ≤
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) / (∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have hQnonzero : (∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpOne : (1 : ℝ) < p := by exact_mod_cast (hP p (hQP hp)).one_lt
    exact ne_of_gt (inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpOne)))
  have hRatio : (∏ p ∈ P \ Q, (1 - (p : ℝ)⁻¹)⁻¹) =
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) / (∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹) := by
    apply (eq_div_iff hQnonzero).mpr
    exact Finset.prod_sdiff hQP
  exact (factored_reciprocal_sum_le A (P \ Q)
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1) hA).trans_eq hRatio

theorem exists_scaled_fiber_mass (A : Finset ℕ) (f : ℕ → ℕ) (w : ℕ → ℝ)
    (η C : ℝ) (hη : 0 < η) (hC : 0 < C)
    (hf : ∀ n ∈ A, 0 < f n) (hw : ∀ n ∈ A, 0 ≤ w n)
    (hMass : η ≤ ∑ n ∈ A, w n)
    (hRecip : (∑ d ∈ A.image f, (d : ℝ)⁻¹) ≤ C) :
    ∃ d ∈ A.image f, η / C ≤ (d : ℝ) * ∑ n ∈ A.filter (fun n => f n = d), w n := by
  classical
  have hANe : A.Nonempty := by
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty.mp hEmpty, Finset.sum_empty] at hMass
    linarith
  let D := A.image f
  let g := fun d : ℕ => (d : ℝ) * ∑ n ∈ A.filter (fun n => f n = d), w n
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image D g (hANe.image f)
  have hpos : ∀ e ∈ D, 0 < e := by
    intro e he
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
    exact hf n hn
  have hNonneg : 0 ≤ g d := mul_nonneg (Nat.cast_nonneg d)
    (Finset.sum_nonneg (fun n hn => hw n (Finset.mem_filter.mp hn).1))
  have hsum : (∑ n ∈ A, w n) = ∑ e ∈ D, (e : ℝ)⁻¹ * g e := by
    trans ∑ e ∈ D, ∑ n ∈ A.filter (fun n => f n = e), w n
    · exact (Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image.mpr ⟨n, hn, rfl⟩) _).symm
    · apply Finset.sum_congr rfl
      intro e he
      have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos e he))
      dsimp [g]
      rw [← mul_assoc, inv_mul_cancel₀ he0, one_mul]
  have hbound : (∑ n ∈ A, w n) ≤ C * g d := by
    rw [hsum]
    calc
      _ ≤ ∑ e ∈ D, (e : ℝ)⁻¹ * g d := Finset.sum_le_sum
        (fun e he => mul_le_mul_of_nonneg_left (hmax e he) (by positivity))
      _ = (∑ e ∈ D, (e : ℝ)⁻¹) * g d := (Finset.sum_mul _ _ _).symm
      _ ≤ C * g d := mul_le_mul_of_nonneg_right hRecip hNonneg
  refine ⟨d, hd, ?_⟩
  apply (div_le_iff₀ hC).mpr
  simpa only [mul_comm] using hMass.trans hbound

theorem sieve_remainder_budget (N Y k : ℕ) (P : Finset ℕ) (δ : ℝ)
    (hN : 0 < N) (hY : 0 < Y) (hδ : 0 < δ)
    (hLevel : 2 * (∑ p ∈ P, (p : ℝ)⁻¹) + Real.log (4 / δ) ≤
      (2 * k : ℕ) * Real.log 2)
    (hSize : (2 * k : ℕ) * Real.log Y ≤ Real.log (δ * N / 4)) :
    N * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ * N / 2 := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hYReal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hlog : Real.log (4 / δ) = -Real.log (δ / 4) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hδ),
      Real.log_div (ne_of_gt hδ) (by norm_num)]
    ring
  have htail : Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) ≤ δ / 4 := by
    have hExponent : 2 * (∑ p ∈ P, (p : ℝ)⁻¹) -
        (2 * k : ℕ) * Real.log 2 ≤ Real.log (δ / 4) := by
      rw [hlog] at hLevel
      linarith only [hLevel]
    have he := Real.exp_le_exp.mpr hExponent
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by positivity : (0 : ℝ) < δ / 4)] at he
    exact he
  have hpower : (Y : ℝ) ^ (2 * k) ≤ δ * N / 4 := by
    have he := Real.exp_le_exp.mpr hSize
    rw [Real.exp_nat_mul, Real.exp_log hYReal,
      Real.exp_log (by positivity : (0 : ℝ) < δ * N / 4)] at he
    exact he
  have htailN := mul_le_mul_of_nonneg_left htail hNReal.le
  rw [← mul_div_assoc] at htailN
  nlinarith only [htailN, hpower]

theorem exists_factored_fiber_mass (A P : Finset ℕ) (f : ℕ → ℕ) (w : ℕ → ℝ)
    (η : ℝ) (hη : 0 < η) (hP : ∀ p ∈ P, p.Prime)
    (hf : ∀ n ∈ A, f n ∈ Nat.factoredNumbers P)
    (hw : ∀ n ∈ A, 0 ≤ w n) (hMass : η ≤ ∑ n ∈ A, w n) :
    ∃ d ∈ A.image f, η / (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      (d : ℝ) * ∑ n ∈ A.filter (fun n => f n = d), w n := by
  have hC : (0 : ℝ) < ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀
      (by exact_mod_cast (hP p hp).one_lt)))
  have hRecip : (∑ d ∈ A.image f, (d : ℝ)⁻¹) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply factored_reciprocal_sum_le _ P hP
    intro d hd
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    exact hf n hn
  exact exists_scaled_fiber_mass A f w η _ hη hC
    (fun n hn => Nat.pos_of_ne_zero (hf n hn).1) hw hMass hRecip

def roughCofactor (Y m : ℕ) : ℕ :=
  (m.primeFactorsList.filter (fun p => Y < p)).prod

def smoothCofactor (Y m : ℕ) : ℕ :=
  (m.primeFactorsList.filter (fun p => p ≤ Y)).prod

theorem roughCofactor_mul_smoothCofactor (Y m : ℕ) (hm : m ≠ 0) :
    roughCofactor Y m * smoothCofactor Y m = m := by
  have hp := (List.filter_append_perm (fun p : ℕ => decide (p ≤ Y)) m.primeFactorsList).prod_eq
  simp only [List.prod_append, ← decide_not, not_le, Nat.prod_primeFactorsList hm] at hp
  simpa only [roughCofactor, smoothCofactor, mul_comm] using hp

theorem roughCofactor_dvd (Y m : ℕ) : roughCofactor Y m ∣ m := by
  by_cases hm : m = 0
  · simp [hm]
  · exact ⟨smoothCofactor Y m, (roughCofactor_mul_smoothCofactor Y m hm).symm⟩

theorem roughCofactor_pos (Y m : ℕ) : 0 < roughCofactor Y m := by
  apply List.prod_pos
  intro p hp
  exact Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp)

theorem smoothCofactor_le_pow_length (Y m : ℕ) (hY : 1 ≤ Y) :
    smoothCofactor Y m ≤ Y ^ m.primeFactorsList.length := by
  unfold smoothCofactor
  calc
    _ ≤ Y ^ (m.primeFactorsList.filter (fun p => p ≤ Y)).length :=
      List.prod_le_pow_length _ Y (fun p hp => of_decide_eq_true (List.mem_filter.mp hp).2)
    _ ≤ Y ^ m.primeFactorsList.length := pow_le_pow_right₀ hY (List.length_filter_le _ _)

theorem roughCofactor_large (Y m k : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y)
    (hLength : m.primeFactorsList.length ≤ k) :
    m ≤ roughCofactor Y m * Y ^ k := by
  conv_lhs => rw [← roughCofactor_mul_smoothCofactor Y m hm]
  exact Nat.mul_le_mul_left _ ((smoothCofactor_le_pow_length Y m hY).trans
    (pow_le_pow_right₀ hY hLength))

theorem roughCofactor_mem_factored (Y m : ℕ) (hm : m ≠ 0) :
    roughCofactor Y m ∈ Nat.factoredNumbers ((Finset.Icc (Y + 1) m).filter Nat.Prime) := by
  classical
  have hfilter : m.primeFactorsList.filter (fun p => Y < p) =
      m.primeFactorsList.filter (fun p => p ∈ (Finset.Icc (Y + 1) m).filter Nat.Prime) := by
    apply List.filter_congr
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactorsList hp
    have hpLe := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.dvd_of_mem_primeFactorsList hp)
    simp only [Finset.mem_filter, Finset.mem_Icc, hpPrime, and_true, decide_eq_decide]
    omega
  rw [roughCofactor, hfilter]
  exact Nat.prod_mem_factoredNumbers _ m

theorem smoothCofactor_pos (Y m : ℕ) : 0 < smoothCofactor Y m := by
  apply List.prod_pos
  intro p hp
  exact Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp)

theorem smoothCofactor_dvd_of_medium_prime (Y m p : ℕ) (hm : m ≠ 0)
    (hp : p.Prime) (hpm : p ∣ m) (hpY : p ≤ Y) : p ∣ smoothCofactor Y m := by
  apply List.dvd_prod
  apply List.mem_filter.mpr
  exact ⟨(Nat.mem_primeFactorsList_iff_dvd hm hp).mpr hpm, by simpa only [decide_eq_true_eq] using hpY⟩

theorem roughCofactor_small_of_medium_prime (Y H m p : ℕ) (hm : m ≠ 0)
    (hp : p.Prime) (hpm : p ∣ m) (hHp : H ≤ p) (hpY : p ≤ Y) :
    H * roughCofactor Y m ≤ m := by
  have hH : H ≤ smoothCofactor Y m := hHp.trans
    (Nat.le_of_dvd (smoothCofactor_pos Y m) (smoothCofactor_dvd_of_medium_prime Y m p hm hp hpm hpY))
  calc
    _ ≤ smoothCofactor Y m * roughCofactor Y m := Nat.mul_le_mul_right _ hH
    _ = m := by simpa only [mul_comm] using roughCofactor_mul_smoothCofactor Y m hm

theorem roughCofactor_scaled_bounds (Y H q n k p : ℕ) (hq : 0 < q) (hn : 0 < n)
    (hqn : q ∣ n) (hY : 1 ≤ Y) (hLength : (n / q).primeFactorsList.length ≤ k)
    (hp : p.Prime) (hpn : p ∣ n / q) (hHp : H ≤ p) (hpY : p ≤ Y) :
    q * roughCofactor Y (n / q) ∣ n ∧
      n ≤ (q * roughCofactor Y (n / q)) * Y ^ k ∧
      H * (q * roughCofactor Y (n / q)) ≤ n := by
  have hqLe : q ≤ n := Nat.le_of_dvd hn hqn
  have hm : n / q ≠ 0 := Nat.ne_of_gt (Nat.div_pos hqLe hq)
  have hcancel : q * (n / q) = n := Nat.mul_div_cancel' hqn
  constructor
  · conv_rhs => rw [← hcancel]
    exact Nat.mul_dvd_mul_left q (roughCofactor_dvd Y (n / q))
  constructor
  · have hh := Nat.mul_le_mul_left q (roughCofactor_large Y (n / q) k hm hY hLength)
    simpa only [hcancel, mul_assoc] using hh
  · have hh := Nat.mul_le_mul_left q
      (roughCofactor_small_of_medium_prime Y H (n / q) p hm hp hpn hHp hpY)
    simpa only [hcancel, mul_left_comm q H] using hh

theorem primeFactor_length_le_primePowerDivisors_card (n : ℕ) (hn : n ≠ 0) :
    n.primeFactorsList.length ≤ (n.divisors.filter IsPrimePow).card := by
  classical
  let T := fun p : ℕ => (Finset.Icc 1 (n.factorization p)).image (fun a => p ^ a)
  have hDisjoint : (n.primeFactors : Set ℕ).PairwiseDisjoint T := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro r hrp hrq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hrp
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hrq
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hqPrime := Nat.prime_of_mem_primeFactors hq
    have hdiv : p ∣ q ^ b := by
      rw [heq]
      simpa only [pow_one] using pow_dvd_pow p (Finset.mem_Icc.mp ha).1
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp (hpPrime.dvd_of_dvd_pow hdiv))
  have hCard : (n.primeFactors.biUnion T).card = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [Finset.card_biUnion hDisjoint]
    apply Finset.sum_congr rfl
    intro p hp
    have hInjective : Function.Injective (fun a : ℕ => p ^ a) :=
      Nat.pow_right_injective (Nat.prime_of_mem_primeFactors hp).one_lt
    dsimp [T]
    rw [Finset.card_image_of_injective _ hInjective]
    simp
  have hSub : n.primeFactors.biUnion T ⊆ n.divisors.filter IsPrimePow := by
    intro r hr
    obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hai := Finset.mem_Icc.mp ha
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(hpPrime.pow_dvd_iff_le_factorization hn).mpr hai.2, hn⟩,
      ⟨p, a, hpPrime.prime, hai.1, rfl⟩⟩
  have hLength : n.primeFactorsList.length = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_eq_sum_factorization]
    simp only [Finsupp.sum, Nat.support_factorization]
  rw [hLength, ← hCard]
  exact Finset.card_le_card hSub

theorem primeFactor_length_le_primePower_count (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    n.primeFactorsList.length ≤
      (((Finset.Icc 1 N).filter IsPrimePow).filter (fun q => q ∣ n)).card := by
  have hSub : n.divisors.filter IsPrimePow ⊆
      ((Finset.Icc 1 N).filter IsPrimePow).filter (fun q => q ∣ n) := by
    intro q hq
    obtain ⟨hqDiv, hqPP⟩ := Finset.mem_filter.mp hq
    have hdiv := (Nat.mem_divisors.mp hqDiv).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hqPP.pos, (Nat.le_of_dvd hn hdiv).trans hnN⟩, hqPP⟩, hdiv⟩
  exact (primeFactor_length_le_primePowerDivisors_card n hn.ne').trans (Finset.card_le_card hSub)


theorem primeFactor_length_le_primePowerMultiplicity (N n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    n.primeFactorsList.length ≤ primePowerMultiplicity N n := by
  exact primeFactor_length_le_primePower_count N n hn hnN

theorem quotient_primeFactor_length_le_multiplicity (N n q : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) (hqn : q ∣ n) :
    (n / q).primeFactorsList.length ≤ primePowerMultiplicity N n := by
  exact (Nat.primeFactorsList_sublist_of_dvd (Nat.div_dvd_of_dvd hqn) hn.ne').length_le.trans
    (primeFactor_length_le_primePowerMultiplicity N n hn hnN)

theorem roughCofactor_scaled_bounds_of_multiplicity (N Y H q n k p : ℕ)
    (hq : 0 < q) (hn : 0 < n) (hnN : n ≤ N) (hqn : q ∣ n) (hY : 1 ≤ Y)
    (hMultiplicity : primePowerMultiplicity N n ≤ k)
    (hp : p.Prime) (hpn : p ∣ n / q) (hHp : H ≤ p) (hpY : p ≤ Y) :
    q * roughCofactor Y (n / q) ∣ n ∧
      n ≤ (q * roughCofactor Y (n / q)) * Y ^ k ∧
      H * (q * roughCofactor Y (n / q)) ≤ n := by
  exact roughCofactor_scaled_bounds Y H q n k p hq hn hqn hY
    ((quotient_primeFactor_length_le_multiplicity N n q hn hnN hqn).trans hMultiplicity)
    hp hpn hHp hpY

theorem quotient_injective_on_divisibles (A : Finset ℕ) (d : ℕ)
    (hdiv : ∀ n ∈ A, d ∣ n) :
    Set.InjOn (fun n : ℕ => n / d) (A : Set ℕ) := by
  intro a ha b hb hab
  calc
    a = d * (a / d) := (Nat.mul_div_cancel' (hdiv a ha)).symm
    _ = d * (b / d) := congrArg (fun t : ℕ => d * t) hab
    _ = b := Nat.mul_div_cancel' (hdiv b hb)

theorem reciprocalSum_image_div (A : Finset ℕ) (d : ℕ)
    (hdiv : ∀ n ∈ A, d ∣ n) :
    reciprocalSum (A.image (fun n => n / d)) = (d : ℚ) * reciprocalSum A := by
  classical
  unfold reciprocalSum
  rw [Finset.sum_image (quotient_injective_on_divisibles A d hdiv), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.cast_div_charZero (hdiv n hn), inv_div, div_eq_mul_inv]

theorem quotient_packet_subset_prefix (A : Finset ℕ) (N d : ℕ) (hd : 0 < d)
    (hA : A ⊆ Finset.Icc 1 N) (hdiv : ∀ n ∈ A, d ∣ n) :
    A.image (fun n => n / d) ⊆ Finset.Icc 1 (N / d) := by
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  have hni := Finset.mem_Icc.mp (hA hn)
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.div_pos (Nat.le_of_dvd hni.1 (hdiv n hn)) hd,
    Nat.div_le_div_right hni.2⟩

theorem cofactor_packet_density (A : Finset ℕ) (N d : ℕ) (c r : ℝ)
    (hN : 0 < N) (hc : 0 < c) (_hA : A ⊆ Finset.Icc 1 N)
    (hmin : ∀ n ∈ A, c * N ≤ (n : ℝ)) (hdiv : ∀ n ∈ A, d ∣ n)
    (hMass : r ≤ (d : ℝ) * (reciprocalSum A : ℝ)) :
    (c * r) * (N / d : ℕ) ≤ ((A.image (fun n => n / d)).card : ℝ) := by
  classical
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hRNonneg : (0 : ℝ) ≤ (reciprocalSum A : ℝ) := by
    exact_mod_cast reciprocalSum_nonneg A
  have hMassCount : (reciprocalSum A : ℝ) * (c * N) ≤ A.card :=
    (le_div_iff₀ (mul_pos hc hNReal)).mp (reciprocalSum_le_card_div_min A (c * N)
      (mul_pos hc hNReal) hmin)
  have hFloor : (d : ℝ) * (N / d : ℕ) ≤ N := by
    exact_mod_cast Nat.mul_div_le N d
  rw [Finset.card_image_of_injOn (quotient_injective_on_divisibles A d hdiv)]
  calc
    _ ≤ c * ((d : ℝ) * (reciprocalSum A : ℝ)) * (N / d : ℕ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMass hc.le) (Nat.cast_nonneg _)
    _ = (reciprocalSum A : ℝ) * (c * ((d : ℝ) * (N / d : ℕ))) := by ring
    _ ≤ (reciprocalSum A : ℝ) * (c * N) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hFloor hc.le) hRNonneg
    _ ≤ A.card := hMassCount

theorem sifted_quotient_card_bound (A P : Finset ℕ) (N q : ℕ) (hq : 0 < q)
    (hA : A ⊆ Finset.Icc 1 N) (hdiv : ∀ n ∈ A, q ∣ n) :
    (A.filter (fun n => ∀ p ∈ P, ¬ p ∣ n / q)).card ≤
      ((Finset.Icc 1 (N / q)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card := by
  let B := A.filter (fun n => ∀ p ∈ P, ¬ p ∣ n / q)
  have hBdiv : ∀ n ∈ B, q ∣ n := fun n hn => hdiv n (Finset.mem_filter.mp hn).1
  apply Finset.card_le_card_of_injOn (fun n => n / q) _
    (quotient_injective_on_divisibles B q hBdiv)
  intro n hn
  have hnB := Finset.mem_filter.mp hn
  have hPrefix := quotient_packet_subset_prefix B N q hq
    (fun m hm => hA (Finset.mem_filter.mp hm).1) hBdiv
  exact Finset.mem_filter.mpr ⟨hPrefix (Finset.mem_image.mpr ⟨n, hn, rfl⟩), hnB.2⟩

theorem sifted_quotient_reciprocal_bound (A P : Finset ℕ) (N q Y k : ℕ) (M : ℝ)
    (hq : 0 < q) (hM : 0 < M) (hY : 1 ≤ Y)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, q ∣ n) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Y) :
    (q : ℝ) * (reciprocalSum (A.filter (fun n => ∀ p ∈ P, ¬ p ∣ n / q)) : ℝ) ≤
      (N : ℝ) / M * (Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
        Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k)) +
        (q : ℝ) / M * (Y : ℝ) ^ (2 * k) := by
  let B := A.filter (fun n => ∀ p ∈ P, ¬ p ∣ n / q)
  let W := Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
    Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hBcount : (B.card : ℝ) ≤ (N / q : ℕ) * W + (Y : ℝ) ^ (2 * k) := by
    have hcard : (B.card : ℝ) ≤
        (((Finset.Icc 1 (N / q)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) := by
      exact_mod_cast sifted_quotient_card_bound A P N q hq hA hdiv
    have hh := hcard.trans (finite_prime_sieve_upper_exp (N / q) Y k P hY hP)
    dsimp [W]
    convert hh using 1
    ring
  have hRecip := reciprocalSum_le_card_div_min B M hM
    (fun n hn => hmin n (Finset.mem_filter.mp hn).1)
  have hqNonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hFloor : (q : ℝ) * (N / q : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N q
  have hFloorWeight := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hFloor hM.le) hW
  calc
    _ ≤ (q : ℝ) * (B.card / M) := mul_le_mul_of_nonneg_left hRecip hqNonneg
    _ = ((q : ℝ) / M) * B.card := by ring
    _ ≤ ((q : ℝ) / M) * ((N / q : ℕ) * W + (Y : ℝ) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hBcount (div_nonneg hqNonneg hM.le)
    _ = (((q : ℝ) * (N / q : ℕ)) / M) * W + (q : ℝ) / M * (Y : ℝ) ^ (2 * k) := by ring
    _ ≤ (N : ℝ) / M * W + (q : ℝ) / M * (Y : ℝ) ^ (2 * k) :=
      add_le_add hFloorWeight le_rfl

theorem roughCofactor_image_reciprocal_bound (A : Finset ℕ) (N Y q : ℕ)
    (hq : 0 < q) (hY : Y ≤ N) (hA : A ⊆ Finset.Icc 1 N)
    (hdiv : ∀ n ∈ A, q ∣ n) :
    (∑ d ∈ A.image (fun n => roughCofactor Y (n / q)), (d : ℝ)⁻¹) ≤
      partial_euler_product N / partial_euler_product Y := by
  let P := (Finset.Icc 1 N).filter Nat.Prime
  let Q := (Finset.Icc 1 Y).filter Nat.Prime
  apply factored_reciprocal_sum_le_euler_ratio _ P Q
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hY))
  intro d hd
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
  have hni := Finset.mem_Icc.mp (hA hn)
  have hmPos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hni.1 (hdiv n hn)) hq
  have hmN : n / q ≤ N := (Nat.div_le_self n q).trans hni.2
  apply Nat.factoredNumbers_mono _ (roughCofactor_mem_factored Y (n / q) hmPos.ne')
  intro p hp
  obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
  have hpi := Finset.mem_Icc.mp hpI
  apply Finset.mem_sdiff.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hpi.2.trans hmN⟩, hpPrime⟩
  · intro hpQ
    have hpLe := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpQ).1).2
    omega

theorem exists_euler_ratio_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N Y : ℕ, 2 ≤ Y → Y ≤ N →
      partial_euler_product N / partial_euler_product Y ≤ C * Real.log N / Real.log Y := by
  obtain ⟨U, hU, hUpper⟩ := weak_mertens_third_upper_all
  obtain ⟨L, hL, hLower⟩ := weak_mertens_third_lower_all
  refine ⟨U / L, div_pos hU hL, ?_⟩
  intro N Y hY hYN
  have hN : 2 ≤ N := hY.trans hYN
  have hNReal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hYReal : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hLogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hLogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hEN : partial_euler_product N ≤ U * Real.log N := by
    simpa only [Nat.floor_natCast, Real.norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
      Real.norm_of_nonneg hLogN] using hUpper N hNReal
  have hEY : L * Real.log Y ≤ partial_euler_product Y := by
    simpa only [Nat.floor_natCast, Real.norm_of_nonneg (zero_le_one.trans partial_euler_trivial_lower_bound),
      Real.norm_of_nonneg hLogY.le] using hLower Y (by linarith)
  have hEYPos : 0 < partial_euler_product Y := lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
  calc
    _ ≤ (U * Real.log N) / partial_euler_product Y := div_le_div_of_nonneg_right hEN hEYPos.le
    _ ≤ (U * Real.log N) / (L * Real.log Y) :=
      div_le_div_of_nonneg_left (mul_nonneg hU.le hLogN) (mul_pos hL hLogY) hEY
    _ = (U / L) * Real.log N / Real.log Y := by ring

theorem extract_rough_divisor_packet (A P : Finset ℕ) (N Y H q s t : ℕ) (M η : ℝ)
    (hq : 0 < q) (hM : 0 < M) (hη : 0 < η) (hY : 1 ≤ Y) (hYN : Y ≤ N)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, q ∣ n) (hMultiplicity : ∀ n ∈ A, primePowerMultiplicity N n ≤ t)
    (hP : ∀ p ∈ P, p.Prime ∧ H ≤ p ∧ p ≤ Y)
    (hMass : η ≤ (q : ℝ) * (reciprocalSum A : ℝ))
    (hBudget : (N : ℝ) / M * (Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
      Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * s)) +
      (q : ℝ) / M * (Y : ℝ) ^ (2 * s) ≤ η / 2) :
    ∃ d : ℕ, 0 < d ∧ ∃ F : Finset ℕ, F ⊆ A ∧ F.Nonempty ∧
      (∀ n ∈ F, q * d ∣ n ∧ n ≤ (q * d) * Y ^ t ∧ H * (q * d) ≤ n) ∧
      η / (2 * (partial_euler_product N / partial_euler_product Y)) ≤
        ((q * d : ℕ) : ℝ) * (reciprocalSum F : ℝ) := by
  classical
  let G := A.filter (fun n => ∃ p ∈ P, p ∣ n / q)
  let B := A.filter (fun n => ∀ p ∈ P, ¬ p ∣ n / q)
  let C := partial_euler_product N / partial_euler_product Y
  have hC : 0 < C := div_pos
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
  have hComplement : A.filter (fun n => ¬ ∃ p ∈ P, p ∣ n / q) = B := by
    ext n
    simp [B]
  have hPartition : (reciprocalSum G : ℝ) + (reciprocalSum B : ℝ) = (reciprocalSum A : ℝ) := by
    simp only [reciprocalSum_real]
    have hh := Finset.sum_filter_add_sum_filter_not A (fun n => ∃ p ∈ P, p ∣ n / q)
      (fun n => (1 : ℝ) / n)
    rw [hComplement] at hh
    exact hh
  have hBad : (q : ℝ) * (reciprocalSum B : ℝ) ≤ η / 2 :=
    (sifted_quotient_reciprocal_bound A P N q Y s M hq hM hY hA hmin hdiv
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩)).trans hBudget
  have hGood : η / 2 ≤ (q : ℝ) * (reciprocalSum G : ℝ) := by
    nlinarith only [hPartition, hBad, hMass]
  let f := fun n => roughCofactor Y (n / q)
  let w := fun n : ℕ => (q : ℝ) * (n : ℝ)⁻¹
  have hGoodSum : η / 2 ≤ ∑ n ∈ G, w n := by
    simpa only [reciprocalSum_real, Finset.mul_sum, one_div, w] using hGood
  have hGsub : G ⊆ A := Finset.filter_subset _ _
  have hRecip : (∑ d ∈ G.image f, (d : ℝ)⁻¹) ≤ C :=
    roughCofactor_image_reciprocal_bound G N Y q hq hYN (hGsub.trans hA)
      (fun n hn => hdiv n (hGsub hn))
  obtain ⟨d, hd, hFiber⟩ := exists_scaled_fiber_mass G f w (η / 2) C (half_pos hη) hC
    (fun n hn => roughCofactor_pos Y (n / q)) (fun n hn => by dsimp [w]; positivity)
    hGoodSum hRecip
  let F := G.filter (fun n => f n = d)
  have hFsub : F ⊆ A := (Finset.filter_subset _ _).trans hGsub
  have hSum : (∑ n ∈ F, w n) = (q : ℝ) * (reciprocalSum F : ℝ) := by
    simp only [reciprocalSum_real, Finset.mul_sum, one_div, w]
  change (η / 2) / C ≤ (d : ℝ) * ∑ n ∈ F, w n at hFiber
  rw [hSum] at hFiber
  have hFmass : η / (2 * C) ≤ ((q * d : ℕ) : ℝ) * (reciprocalSum F : ℝ) := by
    calc
      _ = (η / 2) / C := by ring
      _ ≤ (d : ℝ) * ((q : ℝ) * (reciprocalSum F : ℝ)) := hFiber
      _ = _ := by rw [Nat.cast_mul]; ring
  have hFne : F.Nonempty := by
    by_contra hEmpty
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    rw [hEmpty, reciprocalSum_empty, Rat.cast_zero, mul_zero] at hFmass
    exact (not_le_of_gt (div_pos hη (mul_pos (by norm_num) hC))) hFmass
  have hdPos : 0 < d := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    exact roughCofactor_pos Y (n / q)
  refine ⟨d, hdPos, F, hFsub, hFne, ?_, hFmass⟩
  intro n hn
  obtain ⟨hnG, hfn⟩ := Finset.mem_filter.mp hn
  have hnA := hGsub hnG
  obtain ⟨p, hp, hpn⟩ := (Finset.mem_filter.mp hnG).2
  have hnPos := (Finset.mem_Icc.mp (hA hnA)).1
  have hnN := (Finset.mem_Icc.mp (hA hnA)).2
  have hh := roughCofactor_scaled_bounds_of_multiplicity N Y H q n t p hq hnPos hnN
    (hdiv n hnA) hY (hMultiplicity n hnA) (hP p hp).1 hpn (hP p hp).2.1 (hP p hp).2.2
  change roughCofactor Y (n / q) = d at hfn
  rw [hfn] at hh
  exact hh

theorem extract_nearby_dense_cofactor_packet (A P : Finset ℕ) (N Y H q s t : ℕ)
    (c η K : ℝ) (h : ℤ) (hN : 0 < N) (hq : 0 < q) (hc : 0 < c) (hη : 0 < η)
    (hY : 1 ≤ Y) (hYN : Y ≤ N)
    (hA : A ⊆ Finset.Icc 1 N) (hmin : ∀ n ∈ A, c * N ≤ (n : ℝ))
    (hdiv : ∀ n ∈ A, q ∣ n) (hMultiplicity : ∀ n ∈ A, primePowerMultiplicity N n ≤ t)
    (hP : ∀ p ∈ P, p.Prime ∧ H ≤ p ∧ p ≤ Y)
    (hMass : η ≤ (q : ℝ) * (reciprocalSum A : ℝ))
    (hGood : ∀ n ∈ A, |((h : ZMod n).valMinAbs : ℝ)| < K / 2)
    (hKSize : K * (Y : ℝ) ^ t ≤ c * N)
    (hBudget : (N : ℝ) / (c * N) * (Real.exp (-(∑ p ∈ P, (p : ℝ)⁻¹)) +
      Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * s)) +
      (q : ℝ) / (c * N) * (Y : ℝ) ^ (2 * s) ≤ η / 2) :
    ∃ J : ℕ, ∃ T : Finset ℕ, ∃ x : ℤ,
      H ≤ J ∧ T ⊆ Finset.Icc 1 J ∧
      (c * (η / (2 * (partial_euler_product N / partial_euler_product Y)))) * J ≤ (T.card : ℝ) ∧
      |(x : ℝ) - h| < K / 2 ∧ (q : ℤ) ∣ x ∧ ∀ n ∈ T, (n : ℤ) ∣ x := by
  classical
  have hM : 0 < c * (N : ℝ) := mul_pos hc (by exact_mod_cast hN)
  obtain ⟨d, hd, F, hFA, hFne, hBounds, hFmass⟩ := extract_rough_divisor_packet
    A P N Y H q s t (c * N) η hq hM hη hY hYN hA hmin hdiv hMultiplicity hP hMass hBudget
  have hqd : 0 < q * d := Nat.mul_pos hq hd
  have hFdiv : ∀ n ∈ F, q * d ∣ n := fun n hn => (hBounds n hn).1
  obtain ⟨n₀, hn₀⟩ := hFne
  have hFne : F.Nonempty := ⟨n₀, hn₀⟩
  have hpow : (0 : ℝ) < (Y : ℝ) ^ t := pow_pos (by exact_mod_cast hY) t
  have hUpper : (n₀ : ℝ) ≤ ((q * d : ℕ) : ℝ) * (Y : ℝ) ^ t := by
    exact_mod_cast (hBounds n₀ hn₀).2.1
  have hKdiv : K ≤ ((q * d : ℕ) : ℝ) :=
    (mul_le_mul_iff_of_pos_right hpow).mp (hKSize.trans ((hmin n₀ (hFA hn₀)).trans hUpper))
  obtain ⟨x, hx, hxd, hxF⟩ := packet_nearby_multiple F (q * d) h K hFne hKdiv hFdiv
    (fun n hn => hGood n (hFA hn))
  let T := F.image (fun n => n / (q * d))
  let J := N / (q * d)
  have hTsub : T ⊆ Finset.Icc 1 J := quotient_packet_subset_prefix F N (q * d) hqd
    (hFA.trans hA) hFdiv
  have hHJ : H ≤ J := by
    have hHquot : H ≤ n₀ / (q * d) := (Nat.le_div_iff_mul_le hqd).mpr (hBounds n₀ hn₀).2.2
    exact hHquot.trans (Finset.mem_Icc.mp (hTsub (Finset.mem_image.mpr ⟨n₀, hn₀, rfl⟩))).2
  refine ⟨J, T, x, hHJ, hTsub, ?_, hx, ?_, ?_⟩
  · exact cofactor_packet_density F N (q * d) c _ hN hc (hFA.trans hA)
      (fun n hn => hmin n (hFA hn)) hFdiv hFmass
  · exact dvd_trans (by exact_mod_cast (dvd_mul_right q d)) hxd
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact dvd_trans (by exact_mod_cast (Nat.div_dvd_of_dvd (hFdiv n hn))) (hxF n hn)

theorem uniform_sieve_remainder (H J Y k : ℕ) (P : Finset ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hHJ : H ≤ J)
    (hTail : Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) ≤ δ / 4)
    (hCount : (Y : ℝ) ^ (2 * k) ≤ δ * H / 4) :
    J * Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) +
      (Y : ℝ) ^ (2 * k) ≤ δ * J / 2 := by
  have hTailJ := mul_le_mul_of_nonneg_left hTail (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  rw [← mul_div_assoc] at hTailJ
  have hHJReal : (H : ℝ) ≤ J := by exact_mod_cast hHJ
  have hScale := mul_le_mul_of_nonneg_left hHJReal hδ
  nlinarith only [hTailJ, hCount, hScale]

theorem short_interval_difference_lt (K c : ℝ) (x y : ℤ) (R : ℕ)
    (hK : K ≤ R) (hx : |(x : ℝ) - c| < K / 2) (hy : |(y : ℝ) - c| < K / 2) :
    (x - y).natAbs < R := by
  have hh : |(x : ℝ) - y| < (R : ℝ) := by
    calc
      _ ≤ |(x : ℝ) - c| + |(y : ℝ) - c| := by
        simpa only [abs_sub_comm c (y : ℝ)] using abs_sub_le (x : ℝ) c (y : ℝ)
      _ < K / 2 + K / 2 := add_lt_add hx hy
      _ = K := by ring
      _ ≤ R := hK
  rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
  exact_mod_cast hh

theorem common_nearby_multiple_of_dense_packets (D P : Finset ℕ) (H Y k Z : ℕ)
    (δ K : ℝ) (h : ℤ) (hH : 1 ≤ H) (hY : 1 ≤ Y) (hZ : 1 ≤ Z)
    (hδ : 0 < δ) (hK : 0 < K) (hKR : K ≤ (Z ^ Z : ℕ))
    (hP : ∀ p ∈ P, p.Prime ∧ Z ≤ p ∧ p ≤ Y)
    (hTail : Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * k) ≤ δ / 4)
    (hCount : (Y : ℝ) ^ (2 * k) ≤ δ * H / 4)
    (hPrimeMass : 1 ≤ (∑ p ∈ P, (p : ℝ)⁻¹) - 2 * Real.log (2 / δ))
    (hPackets : ∀ q ∈ D, ∃ J : ℕ, ∃ T : Finset ℕ, ∃ x : ℤ,
      H ≤ J ∧ T ⊆ Finset.Icc 1 J ∧ δ * J ≤ (T.card : ℝ) ∧
      |(x : ℝ) - h| < K / 2 ∧ (q : ℤ) ∣ x ∧ ∀ n ∈ T, (n : ℤ) ∣ x) :
    ∃ x : ℤ, |(x : ℝ) - h| < K / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x := by
  classical
  by_cases hD : D.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hD
    obtain ⟨J₀, T₀, x₀, hHJ₀, hT₀, hDense₀, hx₀, _hqx₀, hDiv₀⟩ := hPackets q₀ hq₀
    refine ⟨x₀, hx₀, ?_⟩
    intro q hq
    obtain ⟨J, T, x, hHJ, hT, hDense, hx, hqx, hDiv⟩ := hPackets q hq
    have heq : x₀ = x := eq_of_dense_prime_support J₀ J Y k Z T₀ T P δ δ x₀ x
      (hH.trans hHJ₀) (hH.trans hHJ) hδ hδ hT₀ hT hY hZ hP hDense₀ hDense
      (uniform_sieve_remainder H J₀ Y k P δ hδ.le hHJ₀ hTail hCount)
      (uniform_sieve_remainder H J Y k P δ hδ.le hHJ hTail hCount)
      (by linarith only [hPrimeMass]) hDiv₀ hDiv
      (short_interval_difference_lt K h x₀ x (Z ^ Z) hKR hx₀ hx)
    rw [heq]
    exact hqx
  · refine ⟨h, ?_, ?_⟩
    · simpa only [sub_self, abs_zero] using half_pos hK
    · intro q hq
      exact False.elim (hD ⟨q, hq⟩)

def primeBand (a b : ℕ) : Finset ℕ := (Finset.Icc (a + 1) b).filter Nat.Prime

theorem primeBand_reciprocal_eq (a b : ℕ) (hab : a ≤ b) :
    (∑ p ∈ primeBand a b, (p : ℝ)⁻¹) =
      (∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (p : ℝ)⁻¹) -
      (∑ p ∈ (Finset.Icc 1 a).filter Nat.Prime, (p : ℝ)⁻¹) := by
  have hSub : (Finset.Icc 1 a).filter Nat.Prime ⊆ (Finset.Icc 1 b).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hab)
  have hDiff : ((Finset.Icc 1 b).filter Nat.Prime) \ ((Finset.Icc 1 a).filter Nat.Prime) =
      primeBand a b := by
    ext p
    simp only [primeBand, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    by_cases hp : p.Prime
    · simp only [hp, and_true]
      omega
    · simp only [hp, and_false, and_true, not_false_eq_true]
  rw [← hDiff]
  exact Finset.sum_sdiff_eq_sub hSub

theorem tendsto_prime_mertens_error_nat :
    Tendsto (fun N : ℕ => (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) -
      (Real.log (Real.log N) + meissel_mertens)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  simpa only [Function.comp_def, prime_summatory, Nat.floor_natCast] using
    (prime_reciprocal.trans_tendsto hlim).comp tendsto_natCast_atTop_atTop

theorem exists_uniform_primeBand_error :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ a b : ℕ, B ≤ a → a ≤ b →
      |(∑ p ∈ primeBand a b, (p : ℝ)⁻¹) -
        (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 2 := by
  have hBound : ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) -
        (Real.log (Real.log N) + meissel_mertens)| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      tendsto_prime_mertens_error_nat.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
  obtain ⟨B, hB⟩ := eventually_atTop.mp hBound
  refine ⟨max B 2, le_max_right _ _, ?_⟩
  intro a b ha hab
  have hA := (abs_lt.mp (hB a ((le_max_left _ _).trans ha)))
  have hBB := (abs_lt.mp (hB b (((le_max_left _ _).trans ha).trans hab)))
  rw [primeBand_reciprocal_eq a b hab, abs_le]
  constructor <;> linarith only [hA.1, hA.2, hBB.1, hBB.2]

theorem primeBand_sift_factor_bound (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hMass : Real.log (Real.log b) - Real.log (Real.log a) - 2 ≤
      ∑ p ∈ primeBand a b, (p : ℝ)⁻¹) :
    Real.exp (-(∑ p ∈ primeBand a b, (p : ℝ)⁻¹)) ≤
      Real.exp 2 * Real.log a / Real.log b := by
  have hLogA : 0 < Real.log a := Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) ha))
  have hLogB : 0 < Real.log b := Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) (ha.trans hab)))
  have he := Real.exp_le_exp.mpr (neg_le_neg hMass)
  have hExponent : -(Real.log (Real.log b) - Real.log (Real.log a) - 2) =
      (2 + Real.log (Real.log a)) - Real.log (Real.log b) := by ring
  rw [hExponent, Real.exp_sub, Real.exp_add, Real.exp_log hLogA, Real.exp_log hLogB] at he
  exact he

noncomputable def sieveLevel (N : ℕ) : ℕ :=
  ⌈10 * Real.log (Real.log N) / Real.log 2⌉₊

theorem sieveLevel_lower (N : ℕ) :
    10 * Real.log (Real.log N) ≤ (sieveLevel N : ℝ) * Real.log 2 := by
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp (Nat.le_ceil _)

theorem sieveLevel_upper (N : ℕ) (hLog : 0 ≤ Real.log (Real.log N)) :
    (sieveLevel N : ℝ) ≤ 10 * Real.log (Real.log N) / Real.log 2 + 1 := by
  exact (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hLog)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)).le

theorem sieveLevel_tail_bound (N : ℕ) (P : Finset ℕ)
    (hSum : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 2 * Real.log (Real.log N)) :
    Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * sieveLevel N) ≤
      Real.exp (-16 * Real.log (Real.log N)) := by
  have hPower : (2 : ℝ) ^ (2 * sieveLevel N) =
      Real.exp (((2 * sieveLevel N : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hPower, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hSum, sieveLevel_lower N]

theorem eventually_sieveLevel_tail_bound :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≤ N) →
      Real.exp (2 * ∑ p ∈ P, (p : ℝ)⁻¹) / (2 : ℝ) ^ (2 * sieveLevel N) ≤
        Real.exp (-16 * Real.log (Real.log N)) := by
  filter_upwards [eventually_primePower_reciprocal_bound] with N hN P hP
  apply sieveLevel_tail_bound
  have hSub : P ⊆ (Finset.Icc 1 N).filter IsPrimePow := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hP p hp).1.one_le, (hP p hp).2⟩,
      (hP p hp).1.isPrimePow⟩
  have hSum : (∑ p ∈ P, (p : ℝ)⁻¹) ≤
      ∑ p ∈ (Finset.Icc 1 N).filter IsPrimePow, (p : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSub
    intro p hp hpnot
    positivity
  exact hSum.trans (by simpa only [one_div] using hN)

theorem log_floor_exp_bounds (x : ℝ) (hx : 0 ≤ x) :
    x - Real.log 2 ≤ Real.log (⌊Real.exp x⌋₊ : ℕ) ∧
      Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hFloor : 1 ≤ ⌊Real.exp x⌋₊ := (Nat.one_le_floor_iff (Real.exp x)).mpr hexp
  have hFloorReal : (1 : ℝ) ≤ (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast hFloor
  have hFloorLower : Real.exp x / 2 ≤ (⌊Real.exp x⌋₊ : ℕ) := by
    have hh := Nat.lt_floor_add_one (Real.exp x)
    linarith only [hh, hFloorReal]
  constructor
  · have hh := Real.log_le_log (div_pos (Real.exp_pos x) (by norm_num)) hFloorLower
    rw [Real.log_div (Real.exp_ne_zero x) (by norm_num), Real.log_exp] at hh
    exact hh
  · have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one hFloorReal)
      (Nat.floor_le (Real.exp_nonneg x))
    rw [Real.log_exp] at hh
    exact hh

noncomputable def localizationPower (N : ℕ) : ℝ := (Real.log N) ^ (4 / 5 : ℝ)

noncomputable def localizationRoughBound (N : ℕ) : ℕ :=
  ⌊Real.exp (localizationPower N / (2 * (Real.log (Real.log N)) ^ 2))⌋₊

noncomputable def localizationMediumBound (N : ℕ) : ℕ :=
  ⌊Real.exp (localizationPower N / (Real.log (Real.log N)) ^ 8)⌋₊

noncomputable def localizationCommonBound (N : ℕ) : ℕ :=
  ⌊Real.exp (localizationPower N / (8 * (Real.log (Real.log N)) ^ 10))⌋₊

noncomputable def localizationPrimeLower (N : ℕ) : ℕ := ⌈Real.log N⌉₊

theorem tendsto_loglog_pow_div_localizationPower (k : ℕ) :
    Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ k / localizationPower N) atTop (𝓝 0) := by
  simpa only [Function.comp_def, localizationPower, Real.rpow_natCast] using
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 4 / 5)).tendsto_div_nhds_zero).comp
      tendsto_log_coe_at_top

theorem tendsto_localizationPower_div_loglog_pow (k : ℕ) :
    Tendsto (fun N : ℕ => localizationPower N / (Real.log (Real.log N)) ^ k) atTop atTop := by
  have hPos : ∀ᶠ N : ℕ in atTop,
      0 < (Real.log (Real.log N)) ^ k / localizationPower N := by
    filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLL hL
    exact div_pos (pow_pos hLL k) (Real.rpow_pos_of_pos hL _)
  have hSmall : Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ k / localizationPower N)
      atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_loglog_pow_div_localizationPower k, hPos⟩
  convert hSmall.inv_tendsto_nhdsGT_zero using 1
  funext N
  change localizationPower N / (Real.log (Real.log N)) ^ k =
    ((Real.log (Real.log N)) ^ k / localizationPower N)⁻¹
  rw [inv_div]

theorem tendsto_localizationRoughBound : Tendsto localizationRoughBound atTop atTop := by
  have hh := (tendsto_localizationPower_div_loglog_pow 2).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  apply tendsto_nat_floor_atTop.comp
  apply Real.tendsto_exp_atTop.comp
  simpa only [div_div, mul_comm] using hh

theorem tendsto_localizationMediumBound : Tendsto localizationMediumBound atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
    (tendsto_localizationPower_div_loglog_pow 8))

theorem tendsto_localizationCommonBound : Tendsto localizationCommonBound atTop atTop := by
  have hh := (tendsto_localizationPower_div_loglog_pow 10).atTop_div_const (by norm_num : (0 : ℝ) < 8)
  apply tendsto_nat_floor_atTop.comp
  apply Real.tendsto_exp_atTop.comp
  simpa only [div_div, mul_comm] using hh

theorem eventually_sieveLevel_le_loglog_sq :
    ∀ᶠ N : ℕ in atTop, (sieveLevel N : ℝ) ≤ (Real.log (Real.log N)) ^ 2 := by
  filter_upwards [tendsto_log_log_coe_at_top.eventually
    (eventually_ge_atTop (max (1 : ℝ) (10 / Real.log 2 + 1)))] with N hLL
  have hOne : 1 ≤ Real.log (Real.log N) := (le_max_left _ _).trans hLL
  have hConst : 10 / Real.log 2 + 1 ≤ Real.log (Real.log N) := (le_max_right _ _).trans hLL
  have hUpper := sieveLevel_upper N (zero_le_one.trans hOne)
  have hMul := mul_le_mul_of_nonneg_right hConst (zero_le_one.trans hOne)
  have hRewrite : 10 * Real.log (Real.log N) / Real.log 2 =
      (10 / Real.log 2) * Real.log (Real.log N) := by ring
  rw [hRewrite] at hUpper
  nlinarith only [hUpper, hMul, hOne]

theorem localizationPrimeLower_power_gt (N : ℕ)
    (hLog : 1 ≤ Real.log N) (hLL : 1 < Real.log (Real.log N)) :
    (N : ℝ) < ((localizationPrimeLower N ^ localizationPrimeLower N : ℕ) : ℝ) := by
  have hZ : Real.log N ≤ (localizationPrimeLower N : ℝ) := Nat.le_ceil _
  have hZOne : (1 : ℝ) ≤ localizationPrimeLower N := hLog.trans hZ
  have hZLog : Real.log (Real.log N) ≤ Real.log (localizationPrimeLower N) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hLog) hZ
  have hExponent : Real.log N < (localizationPrimeLower N : ℝ) * Real.log (localizationPrimeLower N) := by
    have hLogPos : (0 : ℝ) < Real.log N := lt_of_lt_of_le zero_lt_one hLog
    have hProd := mul_le_mul_of_nonneg_left hZLog (le_trans (by norm_num) hZOne)
    nlinarith only [hProd, hZ, hLL, hLogPos]
  have hNatPos : 0 < N := by
    by_contra hN
    have hN : N = 0 := Nat.eq_zero_of_not_pos hN
    norm_num [hN] at hLog
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hNatPos
  have hh := Real.exp_lt_exp.mpr hExponent
  simpa only [Real.exp_log hNReal, Real.exp_nat_mul,
    Real.exp_log (lt_of_lt_of_le zero_lt_one hZOne), Nat.cast_pow] using hh

theorem floor_exp_pow_le (x b : ℝ) (a : ℕ) (hx : 0 ≤ x) (haxb : (a : ℝ) * x ≤ b) :
    ((⌊Real.exp x⌋₊ : ℕ) : ℝ) ^ a ≤ Real.exp b := by
  have hFloorPos : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by
    have hFloor : 1 ≤ ⌊Real.exp x⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp hx)
    exact_mod_cast hFloor
  have hExponent := (mul_le_mul_of_nonneg_left (log_floor_exp_bounds x hx).2
    (Nat.cast_nonneg a : (0 : ℝ) ≤ a)).trans haxb
  have he := Real.exp_le_exp.mpr hExponent
  rw [Real.exp_nat_mul, Real.exp_log hFloorPos] at he
  exact he

theorem floor_exp_le_nat (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : x ≤ Real.log N) :
    ⌊Real.exp x⌋₊ ≤ N := by
  have hh : ((⌊Real.exp x⌋₊ : ℕ) : ℝ) ≤ N := by
    calc
      _ ≤ Real.exp x := Nat.floor_le (Real.exp_nonneg x)
      _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hx
      _ = N := Real.exp_log (by exact_mod_cast hN)
  exact_mod_cast hh

theorem localizationRough_log_bounds (N : ℕ) (hLL : 1 ≤ Real.log (Real.log N))
    (hGrowth : 4 * Real.log 2 * (Real.log (Real.log N)) ^ 2 ≤ localizationPower N) :
    localizationPower N / (4 * (Real.log (Real.log N)) ^ 2) ≤ Real.log (localizationRoughBound N) ∧
      Real.log (localizationRoughBound N) ≤ localizationPower N / (2 * (Real.log (Real.log N)) ^ 2) := by
  have hEllPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one hLL
  have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
  have hx : 0 ≤ localizationPower N / (2 * (Real.log (Real.log N)) ^ 2) := by positivity
  have hBounds := log_floor_exp_bounds _ hx
  change localizationPower N / (2 * (Real.log (Real.log N)) ^ 2) - Real.log 2 ≤
      Real.log (localizationRoughBound N) ∧ Real.log (localizationRoughBound N) ≤
      localizationPower N / (2 * (Real.log (Real.log N)) ^ 2) at hBounds
  have hLog : 2 * Real.log 2 ≤ localizationPower N / (2 * (Real.log (Real.log N)) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (Real.log N)) ^ 2)).mpr
    nlinarith only [hGrowth]
  refine ⟨?_, hBounds.2⟩
  have hHalf : localizationPower N / (4 * (Real.log (Real.log N)) ^ 2) =
      (localizationPower N / (2 * (Real.log (Real.log N)) ^ 2)) / 2 := by ring
  rw [hHalf]
  linarith only [hBounds.1, hLog]

theorem localizationRough_power_bound (N a : ℕ) (B : ℝ)
    (hLL : 0 < Real.log (Real.log N))
    (ha : (a : ℝ) ≤ B * (Real.log (Real.log N)) ^ 2) :
    (localizationRoughBound N : ℝ) ^ a ≤ Real.exp (B * localizationPower N / 2) := by
  have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
  have hx : 0 ≤ localizationPower N / (2 * (Real.log (Real.log N)) ^ 2) := by positivity
  apply floor_exp_pow_le _ _ a hx
  calc
    _ ≤ (B * (Real.log (Real.log N)) ^ 2) *
        (localizationPower N / (2 * (Real.log (Real.log N)) ^ 2)) :=
      mul_le_mul_of_nonneg_right ha hx
    _ = B * localizationPower N / 2 := by field_simp [hLL.ne']

theorem localizationCommon_sieve_cost (N : ℕ) (hLL : 0 < Real.log (Real.log N))
    (hLevel : (sieveLevel N : ℝ) ≤ (Real.log (Real.log N)) ^ 2) :
    (localizationCommonBound N : ℝ) ^ (2 * sieveLevel N) ≤
      Real.exp (localizationPower N / (4 * (Real.log (Real.log N)) ^ 8)) := by
  have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
  have hx : 0 ≤ localizationPower N / (8 * (Real.log (Real.log N)) ^ 10) := by positivity
  apply floor_exp_pow_le _ _ _ hx
  have hScale : ((2 * sieveLevel N : ℕ) : ℝ) ≤ 2 * (Real.log (Real.log N)) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hLevel (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ (2 * (Real.log (Real.log N)) ^ 2) *
        (localizationPower N / (8 * (Real.log (Real.log N)) ^ 10)) :=
      mul_le_mul_of_nonneg_right hScale hx
    _ = localizationPower N / (4 * (Real.log (Real.log N)) ^ 8) := by field_simp [hLL.ne']; ring

theorem eventually_localizationRoughBound_le :
    ∀ᶠ N : ℕ in atTop, localizationRoughBound N ≤ N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))] with N hN hL hLL
  apply floor_exp_le_nat N _ hN
  have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
  have hUL : localizationPower N ≤ Real.log N := by
    simpa only [localizationPower, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (4 / 5 : ℝ) ≤ 1)
  have hDen : 1 ≤ 2 * (Real.log (Real.log N)) ^ 2 := by nlinarith [sq_nonneg (Real.log (Real.log N) - 1)]
  exact (div_le_self hU hDen).trans hUL

theorem localizationMedium_Rough_ratio_bound (N : ℕ)
    (hL : 0 < Real.log N) (hLL : 2 ≤ Real.log (Real.log N))
    (hGrowth : 4 * Real.log 2 * (Real.log (Real.log N)) ^ 2 ≤ localizationPower N) :
    localizationMediumBound N ≤ localizationRoughBound N ∧
      Real.log (localizationMediumBound N) / Real.log (localizationRoughBound N) ≤
        4 / (Real.log (Real.log N)) ^ 6 := by
  have hEllPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le (by norm_num) hLL
  have hU : 0 < localizationPower N := Real.rpow_pos_of_pos hL _
  have hPow : (2 : ℝ) ≤ (Real.log (Real.log N)) ^ 6 := by
    calc
      _ ≤ (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (Real.log (Real.log N)) ^ 6 := by gcongr
  have hDen : 2 * (Real.log (Real.log N)) ^ 2 ≤ (Real.log (Real.log N)) ^ 8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hPow (sq_nonneg (Real.log (Real.log N)))]
  have hx8 : 0 ≤ localizationPower N / (Real.log (Real.log N)) ^ 8 := by positivity
  have hLogH : Real.log (localizationMediumBound N) ≤
      localizationPower N / (Real.log (Real.log N)) ^ 8 := (log_floor_exp_bounds _ hx8).2
  have hBounds := localizationRough_log_bounds N (by linarith) hGrowth
  have hLogY : 0 < Real.log (localizationRoughBound N) :=
    lt_of_lt_of_le (by positivity) hBounds.1
  constructor
  · apply Nat.floor_mono
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hU.le (by positivity) hDen
  · apply (div_le_iff₀ hLogY).mpr
    calc
      _ ≤ localizationPower N / (Real.log (Real.log N)) ^ 8 := hLogH
      _ = (4 / (Real.log (Real.log N)) ^ 6) *
          (localizationPower N / (4 * (Real.log (Real.log N)) ^ 2)) := by field_simp [hEllPos.ne']
      _ ≤ (4 / (Real.log (Real.log N)) ^ 6) * Real.log (localizationRoughBound N) :=
        mul_le_mul_of_nonneg_left hBounds.1 (by positivity)

theorem eventually_localization_medium_sift_bound :
    ∀ᶠ N : ℕ in atTop,
      localizationMediumBound N ≤ localizationRoughBound N ∧
      Real.exp (-(∑ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹)) ≤
        4 * Real.exp 2 / (Real.log (Real.log N)) ^ 6 := by
  obtain ⟨B, hB2, hB⟩ := exists_uniform_primeBand_error
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ)),
    (tendsto_localizationPower_div_loglog_pow 2).eventually (eventually_ge_atTop (4 * Real.log 2)),
    tendsto_localizationMediumBound.eventually (eventually_ge_atTop B)] with N hL hLL hRatio hHB
  have hEllPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le (by norm_num) hLL
  have hGrowth : 4 * Real.log 2 * (Real.log (Real.log N)) ^ 2 ≤ localizationPower N :=
    (le_div_iff₀ (sq_pos_of_pos hEllPos)).mp hRatio
  have hBounds := localizationMedium_Rough_ratio_bound N hL hLL hGrowth
  have hError := (abs_le.mp (hB _ _ hHB hBounds.1)).1
  have hMass : Real.log (Real.log (localizationRoughBound N)) -
      Real.log (Real.log (localizationMediumBound N)) - 2 ≤
      ∑ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹ := by
    linarith only [hError]
  refine ⟨hBounds.1, ?_⟩
  calc
    _ ≤ Real.exp 2 * Real.log (localizationMediumBound N) / Real.log (localizationRoughBound N) :=
      primeBand_sift_factor_bound _ _ (hB2.trans hHB) hBounds.1 hMass
    _ = Real.exp 2 * (Real.log (localizationMediumBound N) / Real.log (localizationRoughBound N)) := by ring
    _ ≤ Real.exp 2 * (4 / (Real.log (Real.log N)) ^ 6) :=
      mul_le_mul_of_nonneg_left hBounds.2 (Real.exp_nonneg _)
    _ = _ := by ring

theorem localizationRough_q_sieve_cost (N q : ℕ) (c : ℝ) (hc : 0 < c)
    (hN : 0 < N) (hLL : 0 < Real.log (Real.log N))
    (hLevel : (sieveLevel N : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
    (hq : (q : ℝ) ≤ smoothCutoff 6 N) :
    (q : ℝ) / (c * N) * (localizationRoughBound N : ℝ) ^ (2 * sieveLevel N) ≤
      Real.exp (-5 * localizationPower N) / c := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hLevel2 : ((2 * sieveLevel N : ℕ) : ℝ) ≤ 2 * (Real.log (Real.log N)) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hLevel (by norm_num : (0 : ℝ) ≤ 2)
  have hPow := localizationRough_power_bound N (2 * sieveLevel N) 2 hLL hLevel2
  have hTwo : 2 * localizationPower N / 2 = localizationPower N := by ring
  rw [hTwo] at hPow
  have hQ : (q : ℝ) ≤ (N : ℝ) * Real.exp (-6 * localizationPower N) := hq
  have hDiv := div_le_div_of_nonneg_right hQ (mul_pos hc hNReal).le
  have hCancel : ((N : ℝ) * Real.exp (-6 * localizationPower N)) / (c * N) =
      Real.exp (-6 * localizationPower N) / c := by field_simp [hc.ne', hNReal.ne']
  rw [hCancel] at hDiv
  calc
    _ ≤ (Real.exp (-6 * localizationPower N) / c) * Real.exp (localizationPower N) :=
      mul_le_mul hDiv hPow (by positivity) (by positivity)
    _ = (Real.exp (-6 * localizationPower N) * Real.exp (localizationPower N)) / c := by ring
    _ = Real.exp (-5 * localizationPower N) / c := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem tendsto_loglog_pow_mul_exp_neg (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ k * Real.exp (-a * Real.log (Real.log N)))
      atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast, Function.comp_def, neg_mul] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha).comp tendsto_log_log_coe_at_top

theorem tendsto_loglog_pow_mul_exp_neg_localizationPower (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ k * Real.exp (-a * localizationPower N))
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_loglog_pow_mul_exp_neg k a ha)
  · filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLL
    exact mul_nonneg (pow_pos hLL k).le (Real.exp_nonneg _)
  · filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      (tendsto_localizationPower_div_loglog_pow 1).eventually (eventually_ge_atTop (1 : ℝ))] with N hLL hRatio
    have hUL : Real.log (Real.log N) ≤ localizationPower N := by
      have hh := (le_div_iff₀ hLL).mp (by simpa only [pow_one] using hRatio)
      simpa only [one_mul] using hh
    apply mul_le_mul_of_nonneg_left _ (pow_pos hLL k).le
    apply Real.exp_le_exp.mpr
    nlinarith only [hUL, ha]

noncomputable def localizationSieveLossMajorant (c : ℝ) (N : ℕ) : ℝ :=
  (1 / c) * (4 * Real.exp 2 / (Real.log (Real.log N)) ^ 6 +
    Real.exp (-16 * Real.log (Real.log N))) + Real.exp (-5 * localizationPower N) / c

theorem tendsto_localizationSieveLoss_scaled (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (Real.log (Real.log N)) ^ 2 * localizationSieveLossMajorant c N)
      atTop (𝓝 0) := by
  have hInv : Tendsto (fun N : ℕ => (1 : ℝ) / (Real.log (Real.log N)) ^ 4) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, Pi.inv_apply, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] using
      tendsto_log_log_coe_at_top.inv_tendsto_atTop.pow 4
  have hFirst : Tendsto (fun N : ℕ => 4 * Real.exp 2 / (Real.log (Real.log N)) ^ 4) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using hInv.const_mul (4 * Real.exp 2)
  have hTail := tendsto_loglog_pow_mul_exp_neg 2 16 (by norm_num)
  have hCount := tendsto_loglog_pow_mul_exp_neg_localizationPower 2 5 (by norm_num)
  have hlim : Tendsto (fun N : ℕ => (1 / c) *
      (4 * Real.exp 2 / (Real.log (Real.log N)) ^ 4 +
        (Real.log (Real.log N)) ^ 2 * Real.exp (-16 * Real.log (Real.log N))) +
        ((Real.log (Real.log N)) ^ 2 * Real.exp (-5 * localizationPower N)) / c) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, zero_div, add_zero] using
      ((hFirst.add hTail).const_mul (1 / c)).add (hCount.div_const c)
  apply hlim.congr'
  filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLL
  dsimp [localizationSieveLossMajorant]
  field_simp [hLL.ne', hc.ne']

theorem eventually_localization_sieve_loss (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, (q : ℝ) ≤ smoothCutoff 6 N →
      (N : ℝ) / (c * N) *
        (Real.exp (-(∑ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹)) +
          Real.exp (2 * ∑ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹) /
            (2 : ℝ) ^ (2 * sieveLevel N)) +
        (q : ℝ) / (c * N) * (localizationRoughBound N : ℝ) ^ (2 * sieveLevel N) ≤
          1 / (4 * (Real.log (Real.log N)) ^ 2) := by
  have hSmall := (tendsto_localizationSieveLoss_scaled c hc).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hSmall, eventually_localization_medium_sift_bound, eventually_sieveLevel_tail_bound,
    eventually_localizationRoughBound_le, eventually_sieveLevel_le_loglog_sq,
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hScaled hMedium hTail hRough hLevel hLL hN q hq
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : ∀ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), p.Prime ∧ p ≤ N := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact ⟨hh.2, (Finset.mem_Icc.mp hh.1).2.trans hRough⟩
  have hTailN := hTail _ hP
  have hCount := localizationRough_q_sieve_cost N q c hc hN hLL hLevel hq
  have hCancel : (N : ℝ) / (c * N) = 1 / c := by field_simp [hc.ne', hNReal.ne']
  rw [hCancel]
  have hRaw : (1 / c) *
      (Real.exp (-(∑ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹)) +
        Real.exp (2 * ∑ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N), (p : ℝ)⁻¹) /
          (2 : ℝ) ^ (2 * sieveLevel N)) +
      (q : ℝ) / (c * N) * (localizationRoughBound N : ℝ) ^ (2 * sieveLevel N) ≤
        localizationSieveLossMajorant c N :=
    add_le_add (mul_le_mul_of_nonneg_left (add_le_add hMedium.2 hTailN) (by positivity)) hCount
  have hBudget : localizationSieveLossMajorant c N ≤ 1 / (4 * (Real.log (Real.log N)) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Real.log (Real.log N)) ^ 2)).mpr
    nlinarith only [hScaled]
  exact hRaw.trans hBudget

noncomputable def localizationWidth (c : ℝ) (N : ℕ) : ℝ :=
  c * N * Real.exp (-localizationPower N)

noncomputable def localizationPacketDensity (c : ℝ) (N : ℕ) : ℝ :=
  c * ((1 / (2 * (Real.log (Real.log N)) ^ 2)) /
    (2 * (partial_euler_product N / partial_euler_product (localizationRoughBound N))))

theorem localizationWidth_size (c : ℝ) (N : ℕ) (hc : 0 < c)
    (hLL : 0 < Real.log (Real.log N)) :
    localizationWidth c N * (localizationRoughBound N : ℝ) ^ ⌊(Real.log (Real.log N)) ^ 2⌋₊ ≤ c * N := by
  have hFloor : ((⌊(Real.log (Real.log N)) ^ 2⌋₊ : ℕ) : ℝ) ≤ (Real.log (Real.log N)) ^ 2 :=
    Nat.floor_le (sq_nonneg _)
  have hPow := localizationRough_power_bound N ⌊(Real.log (Real.log N)) ^ 2⌋₊ 1 hLL
    (by simpa only [one_mul] using hFloor)
  have hExp : Real.exp (localizationPower N / 2) ≤ Real.exp (localizationPower N) := by
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
    linarith
  simp only [one_mul] at hPow
  have hUpper := mul_le_mul_of_nonneg_left (hPow.trans hExp)
    (by unfold localizationWidth; positivity : (0 : ℝ) ≤ localizationWidth c N)
  calc
    _ ≤ localizationWidth c N * Real.exp (localizationPower N) := hUpper
    _ = c * N := by rw [localizationWidth, mul_assoc, ← Real.exp_add]; simp

theorem eventually_extract_nearby_dense_cofactor_packet (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ A : Finset ℕ, ∀ h : ℤ,
      0 < q → (q : ℝ) ≤ smoothCutoff 6 N →
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, q ∣ n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      1 / (2 * (Real.log (Real.log N)) ^ 2) ≤ (q : ℝ) * (reciprocalSum A : ℝ) →
      (∀ n ∈ A, |((h : ZMod n).valMinAbs : ℝ)| < localizationWidth c N / 2) →
      ∃ J : ℕ, ∃ T : Finset ℕ, ∃ x : ℤ,
        localizationMediumBound N ≤ J ∧ T ⊆ Finset.Icc 1 J ∧
        localizationPacketDensity c N * J ≤ (T.card : ℝ) ∧
        |(x : ℝ) - h| < localizationWidth c N / 2 ∧ (q : ℤ) ∣ x ∧ ∀ n ∈ T, (n : ℤ) ∣ x := by
  filter_upwards [eventually_localization_sieve_loss c hc, eventually_localizationRoughBound_le,
    tendsto_localizationRoughBound.eventually (eventually_ge_atTop 1),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hBudget hYN hY hLL hN q A h hq hqS hA hmin hdiv hMult hMass hGood
  have hP : ∀ p ∈ primeBand (localizationMediumBound N) (localizationRoughBound N),
      p.Prime ∧ localizationMediumBound N ≤ p ∧ p ≤ localizationRoughBound N := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hpi := Finset.mem_Icc.mp hh.1
    exact ⟨hh.2, Nat.le_of_succ_le hpi.1, hpi.2⟩
  have hMultNat : ∀ n ∈ A, primePowerMultiplicity N n ≤ ⌊(Real.log (Real.log N)) ^ 2⌋₊ := by
    intro n hn
    exact (Nat.le_floor_iff (sq_nonneg _)).mpr (hMult n hn)
  have hNumerical := hBudget q hqS
  have hEta : 0 < (1 : ℝ) / (2 * (Real.log (Real.log N)) ^ 2) := by positivity
  have hEtaHalf : (1 : ℝ) / (4 * (Real.log (Real.log N)) ^ 2) =
      (1 / (2 * (Real.log (Real.log N)) ^ 2)) / 2 := by ring
  rw [hEtaHalf] at hNumerical
  exact extract_nearby_dense_cofactor_packet A _ N (localizationRoughBound N) (localizationMediumBound N)
    q (sieveLevel N) ⌊(Real.log (Real.log N)) ^ 2⌋₊ c
    (1 / (2 * (Real.log (Real.log N)) ^ 2)) (localizationWidth c N) h hN hq hc hEta hY hYN
    hA hmin hdiv hMultNat hP hMass hGood (localizationWidth_size c N hc hLL) hNumerical

theorem good_residue_mass (A : Finset ℕ) (q : ℕ) (h : ℤ) (M K η : ℝ)
    (hM : 0 < M) (hmin : ∀ n ∈ A, M ≤ (n : ℝ))
    (hMass : η ≤ (q : ℝ) * (reciprocalSum A : ℝ))
    (hBad : (q : ℝ) * ((A.filter (fun n => K / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) / M ≤ η / 2) :
    η / 2 ≤ (q : ℝ) *
      (reciprocalSum (A.filter (fun n => |((h : ZMod n).valMinAbs : ℝ)| < K / 2)) : ℝ) := by
  let G := A.filter (fun n => |((h : ZMod n).valMinAbs : ℝ)| < K / 2)
  let B := A.filter (fun n => K / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)
  have hPartition : (reciprocalSum G : ℝ) + (reciprocalSum B : ℝ) = (reciprocalSum A : ℝ) := by
    simpa only [G, B, reciprocalSum_real, not_lt] using
      Finset.sum_filter_add_sum_filter_not A (fun n => |((h : ZMod n).valMinAbs : ℝ)| < K / 2)
        (fun n => (1 : ℝ) / n)
  have hRB := reciprocalSum_le_card_div_min B M hM (fun n hn => hmin n (Finset.mem_filter.mp hn).1)
  have hQB : (q : ℝ) * (reciprocalSum B : ℝ) ≤ η / 2 := by
    have hh := mul_le_mul_of_nonneg_left hRB (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    rw [← mul_div_assoc] at hh
    exact hh.trans hBad
  nlinarith only [hPartition, hQB, hMass]

theorem localizationPacketDensity_log (c : ℝ) (N : ℕ) (hc : 0 < c)
    (hLL : 0 < Real.log (Real.log N)) :
    0 < localizationPacketDensity c N ∧
      Real.log (2 / localizationPacketDensity c N) = Real.log (8 / c) +
        2 * Real.log (Real.log (Real.log N)) +
          Real.log (partial_euler_product N / partial_euler_product (localizationRoughBound N)) := by
  have hR : 0 < partial_euler_product N / partial_euler_product (localizationRoughBound N) := div_pos
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
  have hδ : 0 < localizationPacketDensity c N := by unfold localizationPacketDensity; positivity
  have hIdentity : (2 : ℝ) / localizationPacketDensity c N = (8 / c) *
      (Real.log (Real.log N)) ^ 2 *
        (partial_euler_product N / partial_euler_product (localizationRoughBound N)) := by
    unfold localizationPacketDensity
    field_simp [hc.ne', hLL.ne', hR.ne']
    ring
  refine ⟨hδ, ?_⟩
  rw [hIdentity, Real.log_mul (by positivity) hR.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hLL.ne'), Real.log_pow]
  norm_num

theorem eventually_localizationPacketDensity_log_bound (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, ∀ᶠ N : ℕ in atTop, 0 < localizationPacketDensity c N ∧
      Real.log (2 / localizationPacketDensity c N) ≤
        (1 / 5 : ℝ) * Real.log (Real.log N) + 4 * Real.log (Real.log (Real.log N)) + B := by
  obtain ⟨C, hC, hRatio⟩ := exists_euler_ratio_log_bound
  refine ⟨Real.log (8 / c) + Real.log (4 * C), ?_⟩
  filter_upwards [eventually_localizationRoughBound_le,
    tendsto_localizationRoughBound.eventually (eventually_ge_atTop 2),
    tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    (tendsto_localizationPower_div_loglog_pow 2).eventually (eventually_ge_atTop (4 * Real.log 2))]
      with N hYN hY hL hLL hGrowthRatio
  have hEllPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one hLL
  have hU : 0 < localizationPower N := Real.rpow_pos_of_pos hL _
  have hGrowth : 4 * Real.log 2 * (Real.log (Real.log N)) ^ 2 ≤ localizationPower N :=
    (le_div_iff₀ (sq_pos_of_pos hEllPos)).mp hGrowthRatio
  have hYLower := (localizationRough_log_bounds N hLL hGrowth).1
  have hLogY : 0 < Real.log (localizationRoughBound N) := lt_of_lt_of_le (by positivity) hYLower
  have hLowerLog := Real.log_le_log (by positivity : (0 : ℝ) < localizationPower N /
    (4 * (Real.log (Real.log N)) ^ 2)) hYLower
  have hLogU : Real.log (localizationPower N) = (4 / 5 : ℝ) * Real.log (Real.log N) := by
    rw [localizationPower, Real.log_rpow hL]
  rw [Real.log_div hU.ne' (by positivity), Real.log_mul (by norm_num) (pow_ne_zero _ hEllPos.ne'),
    Real.log_pow, hLogU] at hLowerLog
  have hR : 0 < partial_euler_product N / partial_euler_product (localizationRoughBound N) := div_pos
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
    (lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound)
  have hLogR := Real.log_le_log hR (hRatio N _ hY hYN)
  rw [Real.log_div (mul_ne_zero hC.ne' hL.ne') hLogY.ne', Real.log_mul hC.ne' hL.ne'] at hLogR
  have hδ := localizationPacketDensity_log c N hc hEllPos
  refine ⟨hδ.1, ?_⟩
  rw [hδ.2, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hC.ne']
  linarith only [hLogR, hLowerLog]

theorem tendsto_loglog_linear_sub_log (a b d : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => a * Real.log (Real.log N) -
      b * Real.log (Real.log (Real.log N)) - d) atTop atTop := by
  have hSmall : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N)) / Real.log (Real.log N))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_log_coe_at_top
  have hInv : Tendsto (fun N : ℕ => (1 : ℝ) / Real.log (Real.log N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp tendsto_log_log_coe_at_top
  have hRatio : Tendsto (fun N : ℕ => a - b *
      (Real.log (Real.log (Real.log N)) / Real.log (Real.log N)) -
      d * (1 / Real.log (Real.log N))) atTop (𝓝 a) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (hSmall.const_mul b)).sub (hInv.const_mul d)
  have hLower : ∀ᶠ N : ℕ in atTop, (a / 2) * Real.log (Real.log N) ≤
      a * Real.log (Real.log N) - b * Real.log (Real.log (Real.log N)) - d := by
    filter_upwards [hRatio.eventually (Ioi_mem_nhds (by linarith : a / 2 < a)),
      tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hR hLL
    have hIdentity : a - b * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N)) -
        d * (1 / Real.log (Real.log N)) =
        (a * Real.log (Real.log N) - b * Real.log (Real.log (Real.log N)) - d) /
          Real.log (Real.log N) := by field_simp [hLL.ne']
    rw [hIdentity] at hR
    exact ((le_div_iff₀ hLL).mp hR.le)
  exact tendsto_atTop_mono' atTop hLower
    ((tendsto_const_mul_atTop_of_pos (half_pos ha)).mpr tendsto_log_log_coe_at_top)

theorem tendsto_localizationPrimeLower : Tendsto localizationPrimeLower atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (b : ℝ))] with N hL
  have hh : (b : ℝ) ≤ (localizationPrimeLower N : ℝ) := hL.trans (Nat.le_ceil _)
  exact_mod_cast hh

theorem localizationPrimeLower_loglog_upper (N : ℕ)
    (hL : 1 ≤ Real.log N) (hLL : 1 ≤ Real.log (Real.log N)) :
    Real.log (localizationPrimeLower N) ≤ 2 * Real.log (Real.log N) ∧
      Real.log (Real.log (localizationPrimeLower N)) ≤ Real.log (Real.log (Real.log N)) + Real.log 2 := by
  have hLPos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hL
  have hZ : Real.log N ≤ (localizationPrimeLower N : ℝ) := Nat.le_ceil _
  have hZPos : (0 : ℝ) < localizationPrimeLower N := hLPos.trans_le hZ
  have hZUpper : (localizationPrimeLower N : ℝ) ≤ 2 * Real.log N := by
    have hh := (Nat.ceil_lt_add_one (log_nat_nonneg N)).le
    change (localizationPrimeLower N : ℝ) ≤ Real.log N + 1 at hh
    linarith only [hh, hL]
  have hLogZ := Real.log_le_log hZPos hZUpper
  rw [Real.log_mul (by norm_num) hLPos.ne'] at hLogZ
  have hLogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh]
  have hLogZUpper : Real.log (localizationPrimeLower N) ≤ 2 * Real.log (Real.log N) := by
    linarith only [hLogZ, hLogTwo, hLL]
  have hLogZPos : 0 < Real.log (localizationPrimeLower N) :=
    lt_of_lt_of_le zero_lt_one (hLL.trans (Real.log_le_log hLPos hZ))
  have hLogLog := Real.log_le_log hLogZPos hLogZUpper
  rw [Real.log_mul (by norm_num) (ne_of_gt (lt_of_lt_of_le zero_lt_one hLL))] at hLogLog
  exact ⟨hLogZUpper, by linarith only [hLogLog]⟩

theorem localizationCommon_loglog_lower (N : ℕ) (hL : 0 < Real.log N)
    (hLL : 0 < Real.log (Real.log N))
    (hGrowth : 16 * Real.log 2 * (Real.log (Real.log N)) ^ 10 ≤ localizationPower N) :
    localizationPower N / (16 * (Real.log (Real.log N)) ^ 10) ≤ Real.log (localizationCommonBound N) ∧
      (4 / 5 : ℝ) * Real.log (Real.log N) - 10 * Real.log (Real.log (Real.log N)) - Real.log 16 ≤
        Real.log (Real.log (localizationCommonBound N)) := by
  have hU : 0 < localizationPower N := Real.rpow_pos_of_pos hL _
  have hx : 0 ≤ localizationPower N / (8 * (Real.log (Real.log N)) ^ 10) := by positivity
  have hBounds := (log_floor_exp_bounds _ hx).1
  change localizationPower N / (8 * (Real.log (Real.log N)) ^ 10) - Real.log 2 ≤
    Real.log (localizationCommonBound N) at hBounds
  have hLogTwo : 2 * Real.log 2 ≤ localizationPower N / (8 * (Real.log (Real.log N)) ^ 10) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (Real.log (Real.log N)) ^ 10)).mpr
    nlinarith only [hGrowth]
  have hWLower : localizationPower N / (16 * (Real.log (Real.log N)) ^ 10) ≤
      Real.log (localizationCommonBound N) := by
    have hIdentity : localizationPower N / (16 * (Real.log (Real.log N)) ^ 10) =
        (localizationPower N / (8 * (Real.log (Real.log N)) ^ 10)) / 2 := by ring
    rw [hIdentity]
    linarith only [hBounds, hLogTwo]
  have hLogLog := Real.log_le_log (by positivity : (0 : ℝ) < localizationPower N /
    (16 * (Real.log (Real.log N)) ^ 10)) hWLower
  have hLogU : Real.log (localizationPower N) = (4 / 5 : ℝ) * Real.log (Real.log N) := by
    rw [localizationPower, Real.log_rpow hL]
  rw [Real.log_div hU.ne' (by positivity), Real.log_mul (by norm_num) (pow_ne_zero _ hLL.ne'),
    Real.log_pow, hLogU] at hLogLog
  refine ⟨hWLower, ?_⟩
  linarith only [hLogLog]

theorem eventually_localizationCommonBand_endpoints :
    ∀ᶠ N : ℕ in atTop, localizationPrimeLower N ≤ localizationCommonBound N ∧
      localizationCommonBound N ≤ N := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    (tendsto_localizationPower_div_loglog_pow 10).eventually (eventually_ge_atTop (16 * Real.log 2)),
    (tendsto_localizationPower_div_loglog_pow 11).eventually (eventually_ge_atTop (32 : ℝ)),
    tendsto_localizationCommonBound.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (0 : ℕ)] with N hL hLL hGrowth hLarge hW hN
  have hLPos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hL
  have hLLPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one hLL
  have hU : 0 ≤ localizationPower N := (Real.rpow_pos_of_pos hLPos _).le
  have hGrowth' := (le_div_iff₀ (pow_pos hLLPos 10)).mp hGrowth
  have hLarge' := (le_div_iff₀ (pow_pos hLLPos 11)).mp hLarge
  have hLower := (localizationCommon_loglog_lower N hLPos hLLPos hGrowth').1
  have hTwo : 2 * Real.log (Real.log N) ≤ localizationPower N / (16 * (Real.log (Real.log N)) ^ 10) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (Real.log (Real.log N)) ^ 10)).mpr
    nlinarith only [hLarge']
  have hZWLog : Real.log (localizationPrimeLower N) ≤ Real.log (localizationCommonBound N) :=
    (localizationPrimeLower_loglog_upper N hL hLL).1.trans (hTwo.trans hLower)
  have hZPos : (0 : ℝ) < localizationPrimeLower N := hLPos.trans_le (Nat.le_ceil _)
  have hWPos : (0 : ℝ) < localizationCommonBound N := by exact_mod_cast hW
  constructor
  · exact_mod_cast (Real.log_le_log_iff hZPos hWPos).mp hZWLog
  · apply floor_exp_le_nat N _ hN
    have hUL : localizationPower N ≤ Real.log N := by
      simpa only [localizationPower, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (4 / 5 : ℝ) ≤ 1)
    have hPow : (1 : ℝ) ≤ (Real.log (Real.log N)) ^ 10 := by
      calc
        _ = (1 : ℝ) ^ 10 := by norm_num
        _ ≤ (Real.log (Real.log N)) ^ 10 := by gcongr
    have hDen : 1 ≤ 8 * (Real.log (Real.log N)) ^ 10 := by linarith only [hPow]
    exact (div_le_self hU hDen).trans hUL

theorem eventually_localizationCommonBand_mass :
    ∀ᶠ N : ℕ in atTop, (4 / 5 : ℝ) * Real.log (Real.log N) -
      11 * Real.log (Real.log (Real.log N)) - (Real.log 16 + Real.log 2 + 2) ≤
      ∑ p ∈ primeBand (localizationPrimeLower N) (localizationCommonBound N), (p : ℝ)⁻¹ := by
  obtain ⟨B, _hB2, hError⟩ := exists_uniform_primeBand_error
  filter_upwards [eventually_localizationCommonBand_endpoints,
    tendsto_localizationPrimeLower.eventually (eventually_ge_atTop B),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    (tendsto_localizationPower_div_loglog_pow 10).eventually (eventually_ge_atTop (16 * Real.log 2))]
      with N hZW hZB hL hLL hGrowth
  have hLPos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hL
  have hLLPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one hLL
  have hGrowth' := (le_div_iff₀ (pow_pos hLLPos 10)).mp hGrowth
  have hLogW := (localizationCommon_loglog_lower N hLPos hLLPos hGrowth').2
  have hLogZ := (localizationPrimeLower_loglog_upper N hL hLL).2
  have hBand := (abs_le.mp (hError _ _ hZB hZW.1)).1
  linarith only [hLogW, hLogZ, hBand]

theorem eventually_localizationCommonBand_support_mass (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, 1 ≤
      (∑ p ∈ primeBand (localizationPrimeLower N) (localizationCommonBound N), (p : ℝ)⁻¹) -
        2 * Real.log (2 / localizationPacketDensity c N) := by
  obtain ⟨B, hB⟩ := eventually_localizationPacketDensity_log_bound c hc
  have hGrowth := (tendsto_loglog_linear_sub_log (2 / 5) 19
    (Real.log 16 + Real.log 2 + 2 + 2 * B) (by norm_num)).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hB, eventually_localizationCommonBand_mass, hGrowth] with N hδ hMass hLower
  linarith only [hδ.2, hMass, hLower]

theorem exp_neg_le_density_quarter (δ a : ℝ) (hδ : 0 < δ)
    (hLog : Real.log (2 / δ) + Real.log 2 ≤ a) : Real.exp (-a) ≤ δ / 4 := by
  calc
    _ ≤ Real.exp (-Real.log (2 / δ) - Real.log 2) := Real.exp_le_exp.mpr (by linarith only [hLog])
    _ = δ / 4 := by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log (div_pos (by norm_num) hδ),
        Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_div]
      ring

theorem eventually_localizationCommonBand_tail (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (2 * ∑ p ∈ primeBand (localizationPrimeLower N) (localizationCommonBound N), (p : ℝ)⁻¹) /
        (2 : ℝ) ^ (2 * sieveLevel N) ≤ localizationPacketDensity c N / 4 := by
  obtain ⟨B, hB⟩ := eventually_localizationPacketDensity_log_bound c hc
  have hGrowth := (tendsto_loglog_linear_sub_log (79 / 5) 4 (B + Real.log 2)
    (by norm_num)).eventually (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hB, hGrowth, eventually_sieveLevel_tail_bound,
    eventually_localizationCommonBand_endpoints] with N hδ hLower hTail hEndpoints
  have hP : ∀ p ∈ primeBand (localizationPrimeLower N) (localizationCommonBound N), p.Prime ∧ p ≤ N := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact ⟨hh.2, (Finset.mem_Icc.mp hh.1).2.trans hEndpoints.2⟩
  have hLog : Real.log (2 / localizationPacketDensity c N) + Real.log 2 ≤
      16 * Real.log (Real.log N) := by linarith only [hδ.2, hLower]
  have hSmall : Real.exp (-16 * Real.log (Real.log N)) ≤ localizationPacketDensity c N / 4 := by
    simpa only [neg_mul] using exp_neg_le_density_quarter (localizationPacketDensity c N)
      (16 * Real.log (Real.log N)) hδ.1 hLog
  exact (hTail _ hP).trans hSmall

theorem exp_quarter_le_density_floor_exp (δ v : ℝ) (hδ : 0 < δ) (hv : 0 ≤ v)
    (hLog : Real.log (2 / δ) + Real.log 4 ≤ 3 * v / 4) :
    Real.exp (v / 4) ≤ δ * ((⌊Real.exp v⌋₊ : ℕ) : ℝ) / 4 := by
  have hH : (0 : ℝ) < (⌊Real.exp v⌋₊ : ℕ) := by
    exact_mod_cast (Nat.one_le_floor_iff _).mpr (Real.one_le_exp hv)
  have hLogδ : Real.log δ = Real.log 2 - Real.log (2 / δ) := by
    rw [Real.log_div (by norm_num) hδ.ne']
    ring
  have hFloor := (log_floor_exp_bounds v hv).1
  have hExponent : v / 4 ≤ Real.log (δ * ((⌊Real.exp v⌋₊ : ℕ) : ℝ) / 4) := by
    rw [Real.log_div (mul_ne_zero hδ.ne' hH.ne') (by norm_num), Real.log_mul hδ.ne' hH.ne', hLogδ]
    linarith only [hFloor, hLog]
  have he := Real.exp_le_exp.mpr hExponent
  rw [Real.exp_log (by positivity : (0 : ℝ) < δ * ((⌊Real.exp v⌋₊ : ℕ) : ℝ) / 4)] at he
  exact he

theorem eventually_localizationCommonBand_count_error (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      (localizationCommonBound N : ℝ) ^ (2 * sieveLevel N) ≤
        localizationPacketDensity c N * localizationMediumBound N / 4 := by
  obtain ⟨B, hB⟩ := eventually_localizationPacketDensity_log_bound c hc
  filter_upwards [hB, eventually_sieveLevel_le_loglog_sq,
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (max (1 : ℝ) (|B| + |Real.log 4|))),
    (tendsto_localizationPower_div_loglog_pow 9).eventually (eventually_ge_atTop (8 : ℝ))]
      with N hδ hLevel hLL hRatio
  have hEllOne : 1 ≤ Real.log (Real.log N) := (le_max_left _ _).trans hLL
  have hEllPos : 0 < Real.log (Real.log N) := lt_of_lt_of_le zero_lt_one hEllOne
  have hConst : B + Real.log 4 ≤ Real.log (Real.log N) := by
    have hh := (le_max_right _ _).trans hLL
    linarith only [hh, le_abs_self B, le_abs_self (Real.log 4)]
  have hLogEll : Real.log (Real.log (Real.log N)) ≤ Real.log (Real.log N) := by
    have hh := Real.log_le_sub_one_of_pos hEllPos
    linarith only [hh]
  have hLarge := (le_div_iff₀ (pow_pos hEllPos 9)).mp hRatio
  have hV : 8 * Real.log (Real.log N) ≤ localizationPower N / (Real.log (Real.log N)) ^ 8 := by
    apply (le_div_iff₀ (pow_pos hEllPos 8)).mpr
    nlinarith only [hLarge]
  have hBudget : Real.log (2 / localizationPacketDensity c N) + Real.log 4 ≤
      3 * (localizationPower N / (Real.log (Real.log N)) ^ 8) / 4 := by
    linarith only [hδ.2, hConst, hLogEll, hV, hEllOne]
  have hFloor := exp_quarter_le_density_floor_exp _ _ hδ.1
    (by unfold localizationPower; positivity : (0 : ℝ) ≤ localizationPower N / (Real.log (Real.log N)) ^ 8) hBudget
  have hCost := localizationCommon_sieve_cost N hEllPos hLevel
  have hIdentity : localizationPower N / (4 * (Real.log (Real.log N)) ^ 8) =
      (localizationPower N / (Real.log (Real.log N)) ^ 8) / 4 := by ring
  rw [hIdentity] at hCost
  exact hCost.trans hFloor

theorem localizationWidth_le (c : ℝ) (N : ℕ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    localizationWidth c N ≤ N := by
  have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
  have hExp : Real.exp (-localizationPower N) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hU)
  have hWidth : localizationWidth c N ≤ c * N := by
    exact mul_le_of_le_one_right (mul_nonneg hc (Nat.cast_nonneg N)) hExp
  exact hWidth.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N))

theorem eventually_common_nearby_multiple_of_packets (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ D : Finset ℕ, ∀ h : ℤ,
      (∀ q ∈ D, ∃ J : ℕ, ∃ T : Finset ℕ, ∃ x : ℤ,
        localizationMediumBound N ≤ J ∧ T ⊆ Finset.Icc 1 J ∧ localizationPacketDensity c N * J ≤ (T.card : ℝ) ∧
        |(x : ℝ) - h| < localizationWidth c N / 2 ∧ (q : ℤ) ∣ x ∧ ∀ n ∈ T, (n : ℤ) ∣ x) →
      ∃ x : ℤ, |(x : ℝ) - h| < localizationWidth c N / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x := by
  obtain ⟨B, hB⟩ := eventually_localizationPacketDensity_log_bound c hc
  filter_upwards [hB, eventually_localizationCommonBand_tail c hc, eventually_localizationCommonBand_count_error c hc,
    eventually_localizationCommonBand_support_mass c hc,
    tendsto_localizationMediumBound.eventually (eventually_ge_atTop 1),
    tendsto_localizationCommonBound.eventually (eventually_ge_atTop 1),
    tendsto_localizationPrimeLower.eventually (eventually_ge_atTop 1),
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hδ hTail hCount hMass hH hW hZ hL hLL hN D h hPackets
  have hK : 0 < localizationWidth c N := by unfold localizationWidth; positivity
  have hKR : localizationWidth c N ≤ ((localizationPrimeLower N ^ localizationPrimeLower N : ℕ) : ℝ) :=
    (localizationWidth_le c N hc.le hc1).trans (localizationPrimeLower_power_gt N hL hLL).le
  have hP : ∀ p ∈ primeBand (localizationPrimeLower N) (localizationCommonBound N),
      p.Prime ∧ localizationPrimeLower N ≤ p ∧ p ≤ localizationCommonBound N := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hpi := Finset.mem_Icc.mp hh.1
    exact ⟨hh.2, Nat.le_of_succ_le hpi.1, hpi.2⟩
  exact common_nearby_multiple_of_dense_packets D _ (localizationMediumBound N) (localizationCommonBound N)
    (sieveLevel N) (localizationPrimeLower N) (localizationPacketDensity c N) (localizationWidth c N)
    h hH hW hZ hδ.1 hK hKR hP hTail hCount hMass hPackets

theorem eventually_divisor_localization (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ A D : Finset ℕ, ∀ h : ℤ,
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ D, 0 < q ∧ (q : ℝ) ≤ smoothCutoff 6 N ∧
        1 / (Real.log (Real.log N)) ^ 2 ≤
          (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ) ∧
        (q : ℝ) * (((A.filter (fun n => q ∣ n)).filter
          (fun n => localizationWidth c N / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) / (c * N) ≤
          1 / (2 * (Real.log (Real.log N)) ^ 2)) →
      ∃ x : ℤ, |(x : ℝ) - h| < localizationWidth c N / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x := by
  filter_upwards [eventually_extract_nearby_dense_cofactor_packet c hc,
    eventually_common_nearby_multiple_of_packets c hc hc1,
    eventually_gt_atTop (0 : ℕ)] with N hExtract hCommon hN A D h hA hmin hMult hD
  apply hCommon D h
  intro q hq
  obtain ⟨hqPos, hqS, hMass, hBad⟩ := hD q hq
  let Aq := A.filter (fun n => q ∣ n)
  let G := Aq.filter (fun n => |((h : ZMod n).valMinAbs : ℝ)| < localizationWidth c N / 2)
  have hGsub : G ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hM : 0 < c * (N : ℝ) := mul_pos hc (by exact_mod_cast hN)
  have hEtaHalf : ((1 : ℝ) / (Real.log (Real.log N)) ^ 2) / 2 =
      1 / (2 * (Real.log (Real.log N)) ^ 2) := by ring
  have hGoodMass := good_residue_mass Aq q h (c * N) (localizationWidth c N)
    (1 / (Real.log (Real.log N)) ^ 2) hM
    (fun n hn => hmin n (Finset.mem_filter.mp hn).1) hMass (by simpa only [hEtaHalf] using hBad)
  rw [hEtaHalf] at hGoodMass
  exact hExtract q G h hqPos hqS (hGsub.trans hA)
    (fun n hn => hmin n (hGsub hn))
    (fun n hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2)
    (fun n hn => hMult n (hGsub hn)) hGoodMass (fun n hn => (Finset.mem_filter.mp hn).2)

theorem tendsto_log_pow_mul_exp_neg_localizationPower (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (Real.log N) ^ k * Real.exp (-a * localizationPower N)) atTop (𝓝 0) := by
  have hU : Tendsto localizationPower atTop atTop := by
    simpa only [pow_zero, div_one] using tendsto_localizationPower_div_loglog_pow 0
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((5 / 4 : ℝ) * k) a ha).comp hU
  apply hlim.congr'
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hL
  have hPower : (localizationPower N) ^ ((5 / 4 : ℝ) * k) = (Real.log N) ^ k := by
    rw [localizationPower, ← Real.rpow_mul hL.le]
    have hExponent : (4 / 5 : ℝ) * ((5 / 4 : ℝ) * k) = (k : ℝ) := by ring
    rw [hExponent, Real.rpow_natCast]
  change (localizationPower N) ^ ((5 / 4 : ℝ) * k) * Real.exp (-a * localizationPower N) = _
  rw [hPower]

theorem tendsto_log_pow_loglog_pow_exp_neg_localizationPower (k m : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (Real.log N) ^ k * (Real.log (Real.log N)) ^ m *
      Real.exp (-a * localizationPower N)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_log_pow_mul_exp_neg_localizationPower (k + m) a ha)
  · filter_upwards [tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hLL
    exact mul_nonneg (mul_nonneg (pow_nonneg (log_nat_nonneg N) k) (pow_pos hLL m).le) (Real.exp_nonneg _)
  · filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))] with N hL hLL
    have hLog : Real.log (Real.log N) ≤ Real.log N := by
      have hh := Real.log_le_sub_one_of_pos hL
      linarith only [hh]
    calc
      _ ≤ (Real.log N) ^ k * (Real.log N) ^ m * Real.exp (-a * localizationPower N) := by gcongr
      _ = _ := by rw [pow_add]

noncomputable def localizationRarity (c τ : ℝ) (N : ℕ) : ℝ :=
  50 * (N : ℝ) ^ 2 * Real.log N * (Real.log (Real.log N)) ^ 2 /
    (τ * (localizationWidth c N) ^ 2)

theorem localizationRarity_scaled_cost (c τ : ℝ) (N q : ℕ) (hc : 0 < c) (hτ : 0 < τ)
    (hN : 0 < N) (hq : (q : ℝ) ≤ smoothCutoff 6 N) :
    (Real.log (Real.log N)) ^ 2 * ((q : ℝ) * localizationRarity c τ N / (c * N)) ≤
      (50 / (τ * c ^ 3)) * Real.log N * (Real.log (Real.log N)) ^ 4 * Real.exp (-4 * localizationPower N) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hRarity : 0 ≤ localizationRarity c τ N := by
    unfold localizationRarity
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (log_nat_nonneg N)) (sq_nonneg _)) (mul_nonneg hτ.le (sq_nonneg _))
  have hScaled := mul_le_mul_of_nonneg_right hq (div_nonneg hRarity (mul_pos hc hNReal).le)
  rw [← mul_div_assoc, ← mul_div_assoc] at hScaled
  have hScaled2 := mul_le_mul_of_nonneg_left hScaled (sq_nonneg (Real.log (Real.log N)))
  have hExp : Real.exp (-6 * localizationPower N) / (Real.exp (-localizationPower N)) ^ 2 =
      Real.exp (-4 * localizationPower N) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    ring
  have hIdentity : (Real.log (Real.log N)) ^ 2 * (smoothCutoff 6 N * localizationRarity c τ N / (c * N)) =
      (50 / (τ * c ^ 3)) * Real.log N * (Real.log (Real.log N)) ^ 4 *
        (Real.exp (-6 * localizationPower N) / (Real.exp (-localizationPower N)) ^ 2) := by
    unfold smoothCutoff localizationRarity localizationWidth
    change (Real.log (Real.log N)) ^ 2 * ((N * Real.exp (-6 * localizationPower N)) *
        (50 * (N : ℝ) ^ 2 * Real.log N * (Real.log (Real.log N)) ^ 2 /
          (τ * (c * N * Real.exp (-localizationPower N)) ^ 2)) / (c * N)) = _
    field_simp [hc.ne', hτ.ne', hNReal.ne', Real.exp_ne_zero]
  rw [hIdentity, hExp] at hScaled2
  exact hScaled2

theorem eventually_localizationRarity_cost (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, (q : ℝ) ≤ smoothCutoff 6 N →
      (q : ℝ) * localizationRarity c τ N / (c * N) ≤ 1 / (2 * (Real.log (Real.log N)) ^ 2) := by
  have hlim : Tendsto (fun N : ℕ => (50 / (τ * c ^ 3)) * Real.log N *
      (Real.log (Real.log N)) ^ 4 * Real.exp (-4 * localizationPower N)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_assoc, mul_zero] using
      (tendsto_log_pow_loglog_pow_exp_neg_localizationPower 1 4 4 (by norm_num)).const_mul (50 / (τ * c ^ 3))
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hSmall hLL hN q hq
  have hCost := localizationRarity_scaled_cost c τ N q hc hτ hN hq
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (Real.log N)) ^ 2)).mpr
  nlinarith only [hCost, hSmall]

theorem eventually_rare_divisor_localization (c τ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ A D : Finset ℕ, ∀ h : ℤ,
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ D, 0 < q ∧ (q : ℝ) ≤ smoothCutoff 6 N ∧
        1 / (Real.log (Real.log N)) ^ 2 ≤
          (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ) ∧
        ((((A.filter (fun n => q ∣ n)).filter
          (fun n => localizationWidth c N / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) < localizationRarity c τ N)) →
      ∃ x : ℤ, |(x : ℝ) - h| < localizationWidth c N / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x := by
  filter_upwards [eventually_divisor_localization c hc hc1,
    eventually_localizationRarity_cost c τ hc hτ,
    eventually_gt_atTop (0 : ℕ)] with N hLocal hCost hN A D h hA hmin hMult hD
  apply hLocal A D h hA hmin hMult
  intro q hq
  obtain ⟨hqPos, hqS, hMass, hRare⟩ := hD q hq
  refine ⟨hqPos, hqS, hMass, ?_⟩
  have hCoeff : 0 ≤ (q : ℝ) / (c * N) := div_nonneg (Nat.cast_nonneg q) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hRare.le hCoeff
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at hh
  exact hh.trans (hCost q hqS)

theorem card_frequencies_of_residue_cover {Q R : ℕ} [NeZero Q]
    (F : Finset (ZMod Q)) (T : Finset ℤ) (hR : 0 < R) (hRQ : R ∣ Q)
    (hCover : ∀ h ∈ F, ∃ a ∈ T, (R : ℤ) ∣ (h.val : ℤ) - a) :
    F.card ≤ T.card * (Q / R) := by
  classical
  let : NeZero R := ⟨Nat.ne_of_gt hR⟩
  let g := fun h : ZMod Q => ((h.val : ZMod R), h.val / R)
  let U : Finset (ZMod R × ℕ) := (T.image (fun a : ℤ => (a : ZMod R))) ×ˢ Finset.range (Q / R)
  have hMaps : Set.MapsTo g (F : Set (ZMod Q)) (U : Set (ZMod R × ℕ)) := by
    intro h hh
    obtain ⟨a, ha, hDiv⟩ := hCover h hh
    have hEq : (a : ZMod R) = (h.val : ZMod R) := by
      simpa only [Int.cast_natCast] using
        (ZMod.intCast_eq_intCast_iff_dvd_sub a (h.val : ℤ) R).mpr hDiv
    have hQ : (Q / R) * R = Q := Nat.div_mul_cancel hRQ
    have hQuot : h.val / R < Q / R := (Nat.div_lt_iff_lt_mul hR).mpr (by simpa only [hQ] using h.val_lt)
    change ((h.val : ZMod R), h.val / R) ∈ (T.image (fun a : ℤ => (a : ZMod R))) ×ˢ Finset.range (Q / R)
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, ha, hEq⟩, Finset.mem_range.mpr hQuot⟩
  have hInjective : Set.InjOn g (F : Set (ZMod Q)) := by
    intro a ha b hb hab
    apply ZMod.val_injective Q
    exact (Nat.residueClassesEquiv R).injective hab
  have hCount := Finset.card_le_card_of_injOn g hMaps hInjective
  change F.card ≤ (T.image (fun a : ℤ => (a : ZMod R)) ×ˢ Finset.range (Q / R)).card at hCount
  rw [Finset.card_product, Finset.card_range] at hCount
  exact hCount.trans (Nat.mul_le_mul_right (Q / R) (Finset.card_image_le))

theorem residue_cover_of_near_multiple {Q R : ℕ} [NeZero Q] (N : ℕ) (K : ℝ)
    (h : ZMod Q) (x : ℤ) (hK : K ≤ N) (hRQ : R ∣ Q)
    (hNear : |(x : ℝ) - (h.valMinAbs : ℝ)| < K / 2) (hDiv : (R : ℤ) ∣ x) :
    ∃ a ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (R : ℤ) ∣ (h.val : ℤ) - a := by
  let a := h.valMinAbs - x
  have haReal : |(a : ℝ)| ≤ (N : ℝ) := by
    have hNear' : |(a : ℝ)| < K / 2 := by
      simpa only [a, Int.cast_sub, abs_sub_comm] using hNear
    have hNNonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith only [hNear', hK, hNNonneg]
  have haInt : |a| ≤ (N : ℤ) := by exact_mod_cast haReal
  have hBalanced : (Q : ℤ) ∣ h.valMinAbs - (h.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.coe_valMinAbs, ZMod.natCast_zmod_val, sub_self]
  have hRBalanced : (R : ℤ) ∣ h.valMinAbs - (h.val : ℤ) :=
    dvd_trans (by exact_mod_cast hRQ) hBalanced
  refine ⟨a, Finset.mem_Icc.mpr (abs_le.mp haInt), ?_⟩
  have hIdentity : (h.val : ℤ) - a = x - (h.valMinAbs - (h.val : ℤ)) := by dsimp [a]; ring
  rw [hIdentity]
  exact dvd_sub hDiv hRBalanced

theorem card_frequencies_near_multiples {Q R : ℕ} [NeZero Q]
    (F : Finset (ZMod Q)) (N : ℕ) (K : ℝ) (hR : 0 < R) (hRQ : R ∣ Q) (hK : K ≤ N)
    (hNear : ∀ h ∈ F, ∃ x : ℤ, |(x : ℝ) - (h.valMinAbs : ℝ)| < K / 2 ∧ (R : ℤ) ∣ x) :
    F.card ≤ (2 * N + 1) * (Q / R) := by
  have hCount := card_frequencies_of_residue_cover F (Finset.Icc (-(N : ℤ)) (N : ℤ)) hR hRQ
    (fun h hh => by
      obtain ⟨x, hx, hDiv⟩ := hNear h hh
      exact residue_cover_of_near_multiple N K h x hK hRQ hx hDiv)
  have hCard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by rw [Int.card_Icc]; omega
  rwa [hCard] at hCount

theorem nat_lcm_dvd_int (D : Finset ℕ) (x : ℤ) (hDiv : ∀ q ∈ D, (q : ℤ) ∣ x) :
    ((D.lcm id : ℕ) : ℤ) ∣ x := by
  apply Int.natCast_dvd.mpr
  apply Finset.lcm_dvd
  intro q hq
  exact Int.natCast_dvd.mp (hDiv q hq)

noncomputable def divisorPrimePowers (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc 1 N).filter IsPrimePow).filter (fun q => ∃ n ∈ A, q ∣ n)

theorem divisorPrimePowers_lcm (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    (divisorPrimePowers N A).lcm id = A.lcm id := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro q hq
    obtain ⟨n, hn, hqn⟩ := (Finset.mem_filter.mp hq).2
    exact hqn.trans (Finset.dvd_lcm hn)
  · apply Finset.lcm_dvd
    intro n hn
    apply divisor_dvd_lcm_of_primePower_classes
    intro q hqPP hqn
    have hni := Finset.mem_Icc.mp (hA hn)
    have hqN : q ≤ N := (Nat.le_of_dvd hni.1 hqn).trans hni.2
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqPP.pos, hqN⟩, hqPP⟩, ⟨n, hn, hqn⟩⟩, dvd_rfl⟩

theorem lcm_complement_quotient_bound (T D : Finset ℕ) (hDT : D ⊆ T)
    (hPos : ∀ q ∈ T, 0 < q) :
    T.lcm id / D.lcm id ≤ ∏ q ∈ T \ D, q := by
  have hR : 0 < D.lcm id := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun q hq => Nat.ne_of_gt (hPos q (hDT hq))))
  have hProd : 0 < ∏ q ∈ T \ D, q := Finset.prod_pos (fun q hq => hPos q (Finset.mem_sdiff.mp hq).1)
  have hDiv : T.lcm id ∣ D.lcm id * ∏ q ∈ T \ D, q := by
    apply Finset.lcm_dvd
    intro q hq
    by_cases hqD : q ∈ D
    · exact dvd_mul_of_dvd_left (Finset.dvd_lcm hqD) _
    · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q)
        (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _
  have hLe := Nat.le_of_dvd (Nat.mul_pos hR hProd) hDiv
  calc
    _ ≤ (D.lcm id * ∏ q ∈ T \ D, q) / D.lcm id := Nat.div_le_div_right hLe
    _ = _ := Nat.mul_div_cancel_left _ hR

theorem card_localized_frequency_class {Q : ℕ} [NeZero Q] (N : ℕ) (K : ℝ) (T D : Finset ℕ)
    (F : Finset (ZMod Q)) (hQ : Q = T.lcm id)
    (hDT : D ⊆ T) (hPos : ∀ q ∈ T, 0 < q) (hTN : ∀ q ∈ T, q ≤ N) (hK : K ≤ N)
    (hLocal : ∀ h ∈ F, ∃ x : ℤ, |(x : ℝ) - (h.valMinAbs : ℝ)| < K / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ x) :
    F.card ≤ (2 * N + 1) * N ^ (T \ D).card := by
  have hR : 0 < D.lcm id := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun q hq => Nat.ne_of_gt (hPos q (hDT hq))))
  have hRQ : D.lcm id ∣ Q := by
    rw [hQ]
    exact Finset.lcm_dvd (fun q hq => Finset.dvd_lcm (hDT hq))
  have hCount := card_frequencies_near_multiples F N K hR hRQ hK (fun h hh => by
    obtain ⟨x, hx, hDiv⟩ := hLocal h hh
    exact ⟨x, hx, nat_lcm_dvd_int D x hDiv⟩)
  have hProd : (∏ q ∈ T \ D, q) ≤ N ^ (T \ D).card := by
    calc
      _ ≤ ∏ _q ∈ T \ D, N := Finset.prod_le_prod (fun q hq => hTN q (Finset.mem_sdiff.mp hq).1)
      _ = _ := Finset.prod_const _
  have hQuotient : Q / D.lcm id ≤ N ^ (T \ D).card := by
    rw [hQ]
    exact (lcm_complement_quotient_bound T D hDT hPos).trans hProd
  exact hCount.trans (Nat.mul_le_mul_left _ hQuotient)

theorem no_large_frequency_with_full_lcm {Q : ℕ} [NeZero Q] (h : ZMod Q) (x : ℤ) (K M : ℝ)
    (hKQ : K ≤ Q) (hKM : K ≤ M)
    (hNear : |(x : ℝ) - (h.valMinAbs : ℝ)| < K / 2) (hDiv : (Q : ℤ) ∣ x)
    (hLarge : M / 2 < |(h.valMinAbs : ℝ)|) : False := by
  have hCenter : |(h.valMinAbs : ℝ)| ≤ (Q : ℝ) / 2 := by
    have hi := h.valMinAbs_mem_Ioc
    have hLower : -(Q : ℝ) < (h.valMinAbs : ℝ) * 2 := by exact_mod_cast hi.1
    have hUpper : (h.valMinAbs : ℝ) * 2 ≤ Q := by exact_mod_cast hi.2
    rw [abs_le]
    constructor <;> linarith only [hLower, hUpper]
  have hXAbs : |(x : ℝ)| < Q := by
    have hh := abs_add_le ((x : ℝ) - h.valMinAbs) (h.valMinAbs : ℝ)
    have hIdentity : (x : ℝ) - h.valMinAbs + h.valMinAbs = x := by ring
    rw [hIdentity] at hh
    linarith only [hh, hNear, hCenter, hKQ]
  have hXSmall : x.natAbs < Q := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
    exact_mod_cast hXAbs
  have hXZero : x = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.mp hDiv) hXSmall)
  rw [hXZero, Int.cast_zero, zero_sub, abs_neg] at hNear
  linarith only [hNear, hKM, hLarge]

theorem exp_sub_one_le_mul_exp (z : ℝ) : Real.exp z - 1 ≤ z * Real.exp z := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-z)) (Real.exp_nonneg z)
  have hCancel : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  rw [hCancel] at hh
  nlinarith only [hh]

theorem nonempty_powerset_weight_bound {ι : Type*} [DecidableEq ι] (T : Finset ι) (x : ℝ) (hx : 0 ≤ x) :
    (∑ B ∈ T.powerset.erase ∅, x ^ B.card) ≤
      ((T.card : ℝ) * x) * Real.exp ((T.card : ℝ) * x) := by
  classical
  have hProd : (∏ _i ∈ T, (1 + x)) = ∑ B ∈ T.powerset, ∏ _i ∈ B, x := Finset.prod_one_add T
  have hTotal : (∑ B ∈ T.powerset, x ^ B.card) = (1 + x) ^ T.card := by
    simpa only [Finset.prod_const] using hProd.symm
  have hErase := Finset.sum_erase_add (T.powerset) (fun B => x ^ B.card)
    (Finset.mem_powerset.mpr (Finset.empty_subset T))
  simp only [Finset.card_empty, pow_zero] at hErase
  rw [hTotal] at hErase
  have hOneExp : 1 + x ≤ Real.exp x := by simpa only [add_comm] using Real.add_one_le_exp x
  have hPower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + x) hOneExp T.card
  rw [← Real.exp_nat_mul] at hPower
  have hLast := exp_sub_one_le_mul_exp ((T.card : ℝ) * x)
  linarith only [hErase, hPower, hLast]

theorem frequency_sum_of_classification {ι : Type*} (F : Finset ι) (T : Finset ℕ)
    (f : ι → ℂ) (missing : ι → Finset ℕ) (N : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hMissing : ∀ h ∈ F, missing h ⊆ T ∧ (missing h).Nonempty)
    (hCount : ∀ B ∈ T.powerset.erase ∅,
      (F.filter (fun h => missing h = B)).card ≤ (2 * N + 1) * N ^ B.card)
    (hNorm : ∀ h ∈ F, ‖f h‖ ≤ r ^ (missing h).card) :
    ‖∑ h ∈ F, f h‖ ≤ (2 * (N : ℝ) + 1) *
      (((T.card : ℝ) * ((N : ℝ) * r)) * Real.exp ((T.card : ℝ) * ((N : ℝ) * r))) := by
  classical
  have hMaps : ∀ h ∈ F, missing h ∈ T.powerset.erase ∅ := by
    intro h hh
    exact Finset.mem_erase.mpr ⟨(hMissing h hh).2.ne_empty, Finset.mem_powerset.mpr (hMissing h hh).1⟩
  have hSplit : (∑ h ∈ F, ‖f h‖) =
      ∑ B ∈ T.powerset.erase ∅, ∑ h ∈ F.filter (fun h => missing h = B), ‖f h‖ :=
    (Finset.sum_fiberwise_of_maps_to hMaps _).symm
  have hTerm : ∀ B ∈ T.powerset.erase ∅,
      (∑ h ∈ F.filter (fun h => missing h = B), ‖f h‖) ≤
        (2 * (N : ℝ) + 1) * ((N : ℝ) * r) ^ B.card := by
    intro B hB
    calc
      _ ≤ ∑ _h ∈ F.filter (fun h => missing h = B), r ^ B.card := by
        apply Finset.sum_le_sum
        intro h hh
        have hi := Finset.mem_filter.mp hh
        simpa only [hi.2] using hNorm h hi.1
      _ = ((F.filter (fun h => missing h = B)).card : ℝ) * r ^ B.card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((2 * N + 1) * N ^ B.card : ℕ) : ℝ) * r ^ B.card := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr _)
        exact_mod_cast hCount B hB
      _ = _ := by push_cast; rw [mul_pow]; ring
  calc
    _ ≤ ∑ h ∈ F, ‖f h‖ := norm_sum_le _ _
    _ = ∑ B ∈ T.powerset.erase ∅, ∑ h ∈ F.filter (fun h => missing h = B), ‖f h‖ := hSplit
    _ ≤ ∑ B ∈ T.powerset.erase ∅, (2 * (N : ℝ) + 1) * ((N : ℝ) * r) ^ B.card := Finset.sum_le_sum hTerm
    _ = (2 * (N : ℝ) + 1) * ∑ B ∈ T.powerset.erase ∅, ((N : ℝ) * r) ^ B.card := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (nonempty_powerset_weight_bound T ((N : ℝ) * r)
      (mul_nonneg (Nat.cast_nonneg N) hr)) (by positivity)

theorem tendsto_nat_pow_exp_neg_log (k : ℕ) (a : ℝ) (hka : (k : ℝ) < a) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-a * Real.log N)) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hka)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hExp : Real.exp (-a * Real.log N) = (N : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos hNReal]
    congr 1
    ring
  rw [hExp, ← Real.rpow_natCast (N : ℝ) k, ← Real.rpow_add hNReal]
  dsimp only [Function.comp_def]
  congr 1
  ring

noncomputable def classificationMajorant (N : ℕ) : ℝ :=
  (2 * (N : ℝ) + 1) * ((N : ℝ) ^ 2 * Real.exp (-100 * Real.log N)) *
    Real.exp ((N : ℝ) ^ 2 * Real.exp (-100 * Real.log N))

theorem tendsto_classificationMajorant : Tendsto classificationMajorant atTop (𝓝 0) := by
  have h2 := tendsto_nat_pow_exp_neg_log 2 100 (by norm_num)
  have h3 := tendsto_nat_pow_exp_neg_log 3 100 (by norm_num)
  have hExp := (Real.continuous_exp.tendsto (0 : ℝ)).comp h2
  have hlim : Tendsto (fun N : ℕ =>
      (2 * ((N : ℝ) ^ 3 * Real.exp (-100 * Real.log N)) + (N : ℝ) ^ 2 * Real.exp (-100 * Real.log N)) *
        Real.exp ((N : ℝ) ^ 2 * Real.exp (-100 * Real.log N))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, Real.exp_zero, zero_mul, Function.comp_def] using
      ((h3.const_mul 2).add h2).mul hExp
  convert hlim using 1
  funext N
  dsimp [classificationMajorant]
  ring

theorem frequency_sum_le_classificationMajorant {ι : Type*} (F : Finset ι) (T : Finset ℕ)
    (f : ι → ℂ) (missing : ι → Finset ℕ) (N : ℕ) (hTN : T.card ≤ N)
    (hMissing : ∀ h ∈ F, missing h ⊆ T ∧ (missing h).Nonempty)
    (hCount : ∀ B ∈ T.powerset.erase ∅,
      (F.filter (fun h => missing h = B)).card ≤ (2 * N + 1) * N ^ B.card)
    (hNorm : ∀ h ∈ F, ‖f h‖ ≤ (Real.exp (-100 * Real.log N)) ^ (missing h).card) :
    ‖∑ h ∈ F, f h‖ ≤ classificationMajorant N := by
  let r := Real.exp (-100 * Real.log N)
  let s := (T.card : ℝ) * ((N : ℝ) * r)
  let y := (N : ℝ) ^ 2 * r
  have hr : 0 ≤ r := Real.exp_nonneg _
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hCard : (T.card : ℝ) ≤ N := by exact_mod_cast hTN
  have hsy : s ≤ y := by
    have hh := mul_le_mul_of_nonneg_right hCard (mul_nonneg (Nat.cast_nonneg N) hr)
    dsimp [s, y]
    nlinarith only [hh]
  have hProd : s * Real.exp s ≤ y * Real.exp y :=
    mul_le_mul hsy (Real.exp_le_exp.mpr hsy) (Real.exp_nonneg _) hy
  have hBound := frequency_sum_of_classification F T f missing N r hr hMissing hCount hNorm
  calc
    _ ≤ (2 * (N : ℝ) + 1) * (s * Real.exp s) := hBound
    _ ≤ (2 * (N : ℝ) + 1) * (y * Real.exp y) := mul_le_mul_of_nonneg_left hProd (by positivity)
    _ = classificationMajorant N := by dsimp [y, r, classificationMajorant]; ring

theorem eventually_frequency_sum_of_classification {ι : Type*} :
    ∀ᶠ N : ℕ in atTop, ∀ F : Finset ι, ∀ T : Finset ℕ, ∀ f : ι → ℂ, ∀ missing : ι → Finset ℕ,
      T.card ≤ N → (∀ h ∈ F, missing h ⊆ T ∧ (missing h).Nonempty) →
      (∀ B ∈ T.powerset.erase ∅, (F.filter (fun h => missing h = B)).card ≤ (2 * N + 1) * N ^ B.card) →
      (∀ h ∈ F, ‖f h‖ ≤ (Real.exp (-100 * Real.log N)) ^ (missing h).card) →
      ‖∑ h ∈ F, f h‖ ≤ 1 / 4 := by
  filter_upwards [tendsto_classificationMajorant.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with N hSmall F T f missing hTN hMissing hCount hNorm
  exact (frequency_sum_le_classificationMajorant F T f missing N hTN hMissing hCount hNorm).trans hSmall.le

noncomputable def rareDivisorSet (c τ : ℝ) (N : ℕ) (A : Finset ℕ) (h : ℤ) : Finset ℕ :=
  (divisorPrimePowers N A).filter (fun q =>
    ((((A.filter (fun n => q ∣ n)).filter
      (fun n => localizationWidth c N / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) < localizationRarity c τ N))

theorem eventually_rareDivisorSet_localization (c τ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, ∀ h : ℤ,
      A ⊆ Finset.Icc 1 N → (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A, 1 / (Real.log (Real.log N)) ^ 2 ≤
        (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      ∃ x : ℤ, |(x : ℝ) - h| < localizationWidth c N / 2 ∧
        ∀ q ∈ rareDivisorSet c τ N A h, (q : ℤ) ∣ x := by
  filter_upwards [eventually_rare_divisor_localization c τ hc hc1 hτ] with N hLocal A h hA hmin hSmooth hMult hMass
  apply hLocal A (rareDivisorSet c τ N A h) h hA hmin hMult
  intro q hq
  have hqi := Finset.mem_filter.mp hq
  have hqPP := Finset.mem_filter.mp hqi.1
  have hqAll := Finset.mem_filter.mp hqPP.1
  obtain ⟨n, hn, hqn⟩ := hqPP.2
  refine ⟨(Finset.mem_Icc.mp hqAll.1).1, ?_, hMass q hqi.1, hqi.2⟩
  exact hSmooth n hn q hqAll.2 hqn

theorem bad_residue_energy (A : Finset ℕ) (N : ℕ) (p : ℕ → ℝ) (h : ℤ) (K τ : ℝ)
    (hN : 0 < N) (hK : 0 ≤ K) (hτ : 0 ≤ τ) (hA : A ⊆ Finset.Icc 1 N)
    (hVar : ∀ n ∈ A, τ ≤ p n * (1 - p n)) :
    (τ * (K / (2 * N)) ^ 2) * ((A.filter (fun n => K / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ) ≤
      ∑ n ∈ A, p n * (1 - p n) * balancedPhase h n ^ 2 := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  let B := A.filter (fun n => K / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)
  have hPoint : ∀ n ∈ B, τ * (K / (2 * N)) ^ 2 ≤ p n * (1 - p n) * balancedPhase h n ^ 2 := by
    intro n hn
    obtain ⟨hnA, hBad⟩ := Finset.mem_filter.mp hn
    have hni := Finset.mem_Icc.mp (hA hnA)
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hni.1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hni.2
    have hPhase : K / (2 * N) ≤ |balancedPhase h n| := by
      rw [balancedPhase, abs_div, abs_of_pos hnReal]
      calc
        _ = (K / 2) / N := by ring
        _ ≤ |((h : ZMod n).valMinAbs : ℝ)| / N := div_le_div_of_nonneg_right hBad hNReal.le
        _ ≤ |((h : ZMod n).valMinAbs : ℝ)| / n := div_le_div_of_nonneg_left (abs_nonneg _) hnReal hnN
    have hSquare : (K / (2 * N)) ^ 2 ≤ balancedPhase h n ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ K / (2 * N)) hPhase 2
    exact (mul_le_mul_of_nonneg_left hSquare hτ).trans
      (mul_le_mul_of_nonneg_right (hVar n hnA) (sq_nonneg _))
  calc
    _ = ∑ _n ∈ B, τ * (K / (2 * N)) ^ 2 := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ n ∈ B, p n * (1 - p n) * balancedPhase h n ^ 2 := Finset.sum_le_sum hPoint
    _ ≤ ∑ n ∈ A, p n * (1 - p n) * balancedPhase h n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hn hnnot
      exact mul_nonneg (hτ.trans (hVar n hn)) (sq_nonneg _)

theorem fourierTerm_norm_of_many_bad_groups {Q x N : ℕ} [NeZero Q]
    (A B : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (c τ : ℝ)
    (hN : 0 < N) (hc : 0 < c) (hτ : 0 < τ) (hLL : 0 < Real.log (Real.log N))
    (hA : A ⊆ Finset.Icc 1 N) (hDiv : ∀ n ∈ A, n ∣ Q)
    (hp : ∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) (hVar : ∀ n ∈ A, τ ≤ p n * (1 - p n))
    (hMult : ∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
    (hB : B ⊆ divisorPrimePowers N A)
    (hBad : ∀ q ∈ B, localizationRarity c τ N ≤
      ((((A.filter (fun n => q ∣ n)).filter
        (fun n => localizationWidth c N / 2 ≤ |((h : ZMod n).valMinAbs : ℝ)|)).card : ℝ))) :
    ‖fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) (h : ZMod Q)‖ ≤
      (Real.exp (-100 * Real.log N)) ^ B.card := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 < localizationWidth c N := by unfold localizationWidth; positivity
  have hPer : 0 ≤ τ * (localizationWidth c N / (2 * N)) ^ 2 := by positivity
  have hIdentity : (τ * (localizationWidth c N / (2 * N)) ^ 2) * localizationRarity c τ N =
      (25 / 2 : ℝ) * Real.log N * (Real.log (Real.log N)) ^ 2 := by
    unfold localizationRarity
    field_simp [hτ.ne', hK.ne', hNReal.ne']
    ring
  have hEnergy : ∀ q ∈ B, (25 / 2 : ℝ) * Real.log N * (Real.log (Real.log N)) ^ 2 ≤
      ∑ n ∈ A.filter (fun n => q ∣ n), p n * (1 - p n) * balancedPhase h n ^ 2 := by
    intro q hq
    have hCard := mul_le_mul_of_nonneg_left (hBad q hq) hPer
    rw [hIdentity] at hCard
    exact hCard.trans (bad_residue_energy _ N p h (localizationWidth c N) τ hN hK.le hτ.le
      ((Finset.filter_subset _ _).trans hA) (fun n hn => hVar n (Finset.mem_filter.mp hn).1))
  have hIncidence : ∀ n ∈ A, ((B.filter (fun q => n ∈ A.filter (fun m => q ∣ m))).card : ℝ) ≤
      (Real.log (Real.log N)) ^ 2 := by
    intro n hn
    have hSub : B.filter (fun q => n ∈ A.filter (fun m => q ∣ m)) ⊆
        ((Finset.Icc 1 N).filter IsPrimePow).filter (fun q => q ∣ n) := by
      intro q hq
      have hqi := Finset.mem_filter.mp hq
      have hPP := (Finset.mem_filter.mp (hB hqi.1)).1
      exact Finset.mem_filter.mpr ⟨hPP, (Finset.mem_filter.mp hqi.2).2⟩
    have hCard : ((B.filter (fun q => n ∈ A.filter (fun m => q ∣ m))).card : ℝ) ≤
        primePowerMultiplicity N n := by exact_mod_cast Finset.card_le_card hSub
    exact hCard.trans (hMult n hn)
  have hBound := fourierTerm_norm_le_group_energy (x := x) A B (fun q => A.filter (fun n => q ∣ n)) p h
    ((25 / 2 : ℝ) * Real.log N * (Real.log (Real.log N)) ^ 2) ((Real.log (Real.log N)) ^ 2)
    (fun n hn => (Finset.mem_Icc.mp (hA hn)).1) hDiv hp (sq_pos_of_pos hLL)
    (fun q hq => Finset.filter_subset _ _) hIncidence hEnergy
  have hExponent : -(8 * ((25 / 2 : ℝ) * Real.log N * (Real.log (Real.log N)) ^ 2) * B.card /
      (Real.log (Real.log N)) ^ 2) = (B.card : ℝ) * (-100 * Real.log N) := by field_simp [hLL.ne']; ring
  rw [hExponent, Real.exp_nat_mul] at hBound
  exact hBound

theorem eventually_large_frequency_bound_regular (c τ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q x : ℕ) [NeZero Q] (A : Finset ℕ) (p : ℕ → ℝ),
      Q = A.lcm id → A.Nonempty → A ⊆ Finset.Icc 1 N →
      (∀ n ∈ A, c * N ≤ (n : ℝ)) →
      (∀ n ∈ A, PrimePowerSmooth (smoothCutoff 6 N) n) →
      (∀ n ∈ A, (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2) →
      (∀ q ∈ divisorPrimePowers N A, 1 / (Real.log (Real.log N)) ^ 2 ≤
        (q : ℝ) * (reciprocalSum (A.filter (fun n => q ∣ n)) : ℝ)) →
      (∀ n ∈ A, 0 ≤ p n ∧ p n ≤ 1) → (∀ n ∈ A, τ ≤ p n * (1 - p n)) →
      ‖∑ h ∈ Finset.univ.filter (fun h : ZMod Q => c * N / 2 < |(h.valMinAbs : ℝ)|),
        fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) h‖ ≤ 1 / 4 := by
  classical
  filter_upwards [eventually_rareDivisorSet_localization c τ hc hc1 hτ,
    tendsto_classificationMajorant.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_gt_atTop (0 : ℕ),
    tendsto_log_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with N hLocal hSmall hN hLL Q x inst A p hQ hAne hA hmin hSmooth hMult hMass hp hVar
  let T := divisorPrimePowers N A
  let F := Finset.univ.filter (fun z : ZMod Q => c * N / 2 < |(z.valMinAbs : ℝ)|)
  let missing := fun z : ZMod Q => T \ rareDivisorSet c τ N A z.valMinAbs
  let f := fun z : ZMod Q => fourierTerm A p (fun n => ((Q / n : ℕ) : ZMod Q)) (x : ZMod Q) z
  have hTsub : T ⊆ Finset.Icc 1 N := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hTpos : ∀ q ∈ T, 0 < q := fun q hq => (Finset.mem_Icc.mp (hTsub hq)).1
  have hTN : ∀ q ∈ T, q ≤ N := fun q hq => (Finset.mem_Icc.mp (hTsub hq)).2
  have hTcard : T.card ≤ N := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hTsub
  have hQPrime : Q = T.lcm id := hQ.trans (divisorPrimePowers_lcm N A hA).symm
  have hDiv : ∀ n ∈ A, n ∣ Q := by
    intro n hn
    rw [hQ]
    exact Finset.dvd_lcm hn
  have hKmin : localizationWidth c N ≤ c * N := by
    have hU : 0 ≤ localizationPower N := Real.rpow_nonneg (log_nat_nonneg N) _
    exact mul_le_of_le_one_right (mul_nonneg hc.le (Nat.cast_nonneg N))
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hU))
  have hMQ : c * (N : ℝ) ≤ Q := by
    obtain ⟨n, hn⟩ := hAne
    have hnQ : n ≤ Q := Nat.le_of_dvd (NeZero.pos Q) (hDiv n hn)
    exact (hmin n hn).trans (by exact_mod_cast hnQ)
  have hKQ := hKmin.trans hMQ
  have hKN := localizationWidth_le c N hc.le hc1
  have hLocalA : ∀ h : ℤ, ∃ y : ℤ, |(y : ℝ) - h| < localizationWidth c N / 2 ∧
      ∀ q ∈ rareDivisorSet c τ N A h, (q : ℤ) ∣ y :=
    fun h => hLocal A h hA hmin hSmooth hMult hMass
  have hMissing : ∀ z ∈ F, missing z ⊆ T ∧ (missing z).Nonempty := by
    intro z hz
    refine ⟨Finset.sdiff_subset, ?_⟩
    by_contra hEmpty
    have hSub : T ⊆ rareDivisorSet c τ N A z.valMinAbs := by
      intro q hq
      by_contra hNot
      exact hEmpty ⟨q, Finset.mem_sdiff.mpr ⟨hq, hNot⟩⟩
    obtain ⟨y, hy, hyDiv⟩ := hLocalA z.valMinAbs
    have hyQ : (Q : ℤ) ∣ y := by
      rw [hQPrime]
      exact nat_lcm_dvd_int T y (fun q hq => hyDiv q (hSub hq))
    exact no_large_frequency_with_full_lcm z y (localizationWidth c N) (c * N) hKQ hKmin
      hy hyQ (Finset.mem_filter.mp hz).2
  have hCount : ∀ B ∈ T.powerset.erase ∅,
      (F.filter (fun z => missing z = B)).card ≤ (2 * N + 1) * N ^ B.card := by
    intro B hB
    let D := T \ B
    have hBT : B ⊆ T := Finset.mem_powerset.mp (Finset.mem_erase.mp hB).2
    have hDiff : T \ D = B := by
      ext q
      simp only [D, Finset.mem_sdiff]
      constructor
      · rintro ⟨hqT, hqNotD⟩
        by_contra hqNotB
        exact hqNotD ⟨hqT, hqNotB⟩
      · intro hqB
        exact ⟨hBT hqB, fun hh => hh.2 hqB⟩
    have hClassLocal : ∀ z ∈ F.filter (fun z => missing z = B),
        ∃ y : ℤ, |(y : ℝ) - z.valMinAbs| < localizationWidth c N / 2 ∧ ∀ q ∈ D, (q : ℤ) ∣ y := by
      intro z hz
      have hzi := Finset.mem_filter.mp hz
      obtain ⟨y, hy, hyDiv⟩ := hLocalA z.valMinAbs
      refine ⟨y, hy, ?_⟩
      intro q hq
      apply hyDiv q
      by_contra hNot
      have hqMissing : q ∈ missing z := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1, hNot⟩
      rw [hzi.2] at hqMissing
      exact (Finset.mem_sdiff.mp hq).2 hqMissing
    have hC := card_localized_frequency_class N (localizationWidth c N) T D _ hQPrime
      Finset.sdiff_subset hTpos hTN hKN hClassLocal
    rw [hDiff] at hC
    exact hC
  have hNorm : ∀ z ∈ F, ‖f z‖ ≤ (Real.exp (-100 * Real.log N)) ^ (missing z).card := by
    intro z hz
    have hBad : ∀ q ∈ missing z, localizationRarity c τ N ≤
        ((((A.filter (fun n => q ∣ n)).filter
          (fun n => localizationWidth c N / 2 ≤ |((z.valMinAbs : ZMod n).valMinAbs : ℝ)|)).card : ℝ)) := by
      intro q hq
      have hqi := Finset.mem_sdiff.mp hq
      apply le_of_not_gt
      intro hRare
      exact hqi.2 (Finset.mem_filter.mpr ⟨hqi.1, hRare⟩)
    have hh := fourierTerm_norm_of_many_bad_groups (x := x) A (missing z) p z.valMinAbs c τ hN hc hτ hLL
      hA hDiv hp hVar hMult Finset.sdiff_subset hBad
    simpa only [f, ZMod.coe_valMinAbs] using hh
  have hBound := frequency_sum_le_classificationMajorant F T f missing N hTcard hMissing hCount hNorm
  exact hBound.trans hSmall.le

theorem eventually_exact_subset_regular_family (F : ℕ → Finset ℕ) (p : ℕ → ℕ → ℝ)
    (target : ℕ → ℚ) (c α τ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hα : 0 < α) (hτ : 0 < τ)
    (hF : ∀ N, F N ⊆ Finset.Icc 1 N) (hmin : ∀ N n, n ∈ F N → c * N ≤ (n : ℝ))
    (hSmooth : ∀ N n, n ∈ F N → PrimePowerSmooth (smoothCutoff 6 N) n)
    (hMult : ∀ N n, n ∈ F N → (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
    (hMass : ∀ N q, q ∈ divisorPrimePowers N (F N) → 1 / (Real.log (Real.log N)) ^ 2 ≤
      (q : ℝ) * (reciprocalSum ((F N).filter (fun n => q ∣ n)) : ℝ))
    (hCard : ∀ᶠ N : ℕ in atTop, α * N ≤ ((F N).card : ℝ))
    (hp : ∀ᶠ N : ℕ in atTop, ∀ n ∈ F N, 0 ≤ p N n ∧ p N n ≤ 1)
    (hVar : ∀ᶠ N : ℕ in atTop, ∀ n ∈ F N, τ ≤ p N n * (1 - p N n))
    (hTarget : ∀ᶠ N : ℕ in atTop, 0 ≤ target N ∧ (target N).den ∣ (F N).lcm id)
    (hMean : ∀ᶠ N : ℕ in atTop, (∑ n ∈ F N, p N n / n) = (target N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ F N, reciprocalSum B = target N := by
  have hPos : ∀ N n, n ∈ F N → 0 < n := fun N n hn => (Finset.mem_Icc.mp (hF N hn)).1
  have hGrowth := eventually_smooth_lcm_fourier_growth F hPos 6 (by norm_num) hSmooth c hc
  filter_upwards [eventually_major_parameters c hc, eventually_middle_parameters α τ hα hτ,
    eventually_large_frequency_bound_regular c τ hc hc1 hτ, hGrowth,
    hCard, hp, hVar, hTarget, hMean, eventually_gt_atTop (0 : ℕ)]
      with N hMajor hMiddle hLarge hQGrowth hCardN hpN hVarN hTargetN hMeanN hN
  let Q := (F N).lcm id
  have hQPos : 0 < Q := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun n hn => (hPos N n hn).ne'))
  let : NeZero Q := ⟨hQPos.ne'⟩
  obtain ⟨x, hx⟩ := exists_numerator_over_common (Q := Q) (target N) hTargetN.1 hTargetN.2
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hFne : (F N).Nonempty := by
    apply Finset.card_pos.mp
    have hCardPos : (0 : ℝ) < (F N).card := (mul_pos hα hNReal).trans_le hCardN
    exact_mod_cast hCardPos
  have hExpected : (∑ n ∈ F N, p N n / n) = (x : ℝ) / Q := by
    rw [hMeanN]
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun t : ℚ => (t : ℝ)) hx
  have hMN : c * (N : ℝ) ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hNReal.le
  have hDiv : ∀ n ∈ F N, n ∣ Q := fun n hn => Finset.dvd_lcm hn
  have hLargeN := hLarge Q x (F N) (p N) rfl hFne (hF N) (hmin N) (hSmooth N)
    (hMult N) (hMass N) hpN hVarN
  obtain ⟨B, hB, hSum⟩ := exact_subset_of_large_frequency_bound (F N) (p N)
    ((N : ℝ) ^ (3 / 5 : ℝ)) (c * N) τ hN (mul_pos hc hNReal) hMN
    (Real.rpow_nonneg hNReal.le _) hMajor.1 (hF N) (hmin N) hDiv hpN hτ.le hVarN hExpected
    hMajor.2.1 hMajor.2.2 (hMiddle (F N).card hCardN) hLargeN hQGrowth.1 hQGrowth.2
  exact ⟨B, hB, hSum.trans hx.symm⟩

theorem eventually_complement_regular_family (F : ℕ → Finset ℕ) (c β κ : ℝ) (r : ℚ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 < β) (hκ : 0 < κ) (hr : 0 < r)
    (hF : ∀ N, F N ⊆ Finset.Icc 1 N) (hmin : ∀ N n, n ∈ F N → c * N ≤ (n : ℝ))
    (hSmooth : ∀ N n, n ∈ F N → PrimePowerSmooth (smoothCutoff 6 N) n)
    (hMult : ∀ N n, n ∈ F N → (primePowerMultiplicity N n : ℝ) ≤ (Real.log (Real.log N)) ^ 2)
    (hMass : ∀ N q, q ∈ divisorPrimePowers N (F N) → 1 / (Real.log (Real.log N)) ^ 2 ≤
      (q : ℝ) * (reciprocalSum ((F N).filter (fun n => q ∣ n)) : ℝ))
    (hR : Tendsto (fun N => (reciprocalSum (F N) : ℝ)) atTop (𝓝 ((r : ℝ) + κ)))
    (hDensity : Tendsto (fun N => (F N).card / (N : ℝ)) atTop (𝓝 β))
    (hDen : ∀ᶠ N : ℕ in atTop, r.den ∣ (F N).lcm id) :
    ∀ᶠ N : ℕ in atTop, ∃ G ⊆ F N, reciprocalSum G = reciprocalSum (F N) - r := by
  let target := fun N => reciprocalSum (F N) - r
  let w := fun N => (target N : ℝ) / (reciprocalSum (F N) : ℝ)
  let w₀ := κ / ((r : ℝ) + κ)
  let τ := w₀ * (1 - w₀) / 2
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hTotal : 0 < (r : ℝ) + κ := by positivity
  have hw₀ : 0 < w₀ := div_pos hκ hTotal
  have hw₀1 : w₀ < 1 := (div_lt_one hTotal).mpr (by linarith)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hRconst : Tendsto (fun _N : ℕ => (r : ℝ)) atTop (𝓝 (r : ℝ)) := tendsto_const_nhds
  have hDiff : Tendsto (fun N => (reciprocalSum (F N) : ℝ) - (r : ℝ)) atTop (𝓝 κ) := by
    simpa only [add_sub_cancel_left] using hR.sub hRconst
  have hw : Tendsto w atTop (𝓝 w₀) := by
    apply (hDiff.div hR hTotal.ne').congr'
    filter_upwards with N
    simp only [w, target, Rat.cast_sub, Pi.div_apply]
  have hwRange := hw.eventually (Ioo_mem_nhds hw₀ hw₀1)
  have hVariance : Tendsto (fun N => w N * (1 - w N)) atTop (𝓝 (w₀ * (1 - w₀))) :=
    hw.mul (tendsto_const_nhds.sub hw)
  have hτlt : τ < w₀ * (1 - w₀) := by dsimp [τ]; nlinarith [mul_pos hw₀ (sub_pos.mpr hw₀1)]
  have hVar : ∀ᶠ N : ℕ in atTop, ∀ n ∈ F N, τ ≤ w N * (1 - w N) := by
    filter_upwards [hVariance.eventually (Ioi_mem_nhds hτlt)]
      with N hN n hn
    exact hN.le
  have hp : ∀ᶠ N : ℕ in atTop, ∀ n ∈ F N, 0 ≤ w N ∧ w N ≤ 1 := by
    filter_upwards [hwRange] with N hN n hn
    exact ⟨hN.1.le, hN.2.le⟩
  have hRLower := hR.eventually (Ioi_mem_nhds (by linarith : (r : ℝ) < (r : ℝ) + κ))
  have hCard : ∀ᶠ N : ℕ in atTop, (β / 2) * N ≤ ((F N).card : ℝ) := by
    filter_upwards [hDensity.eventually (Ioi_mem_nhds (by linarith : β / 2 < β)),
      eventually_gt_atTop (0 : ℕ)] with N hD hN
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    exact ((le_div_iff₀ hNReal).mp hD.le)
  have hTarget : ∀ᶠ N : ℕ in atTop, 0 ≤ target N ∧ (target N).den ∣ (F N).lcm id := by
    filter_upwards [hDen, hRLower] with N hD hRL
    have hTargetNonneg : (0 : ℝ) ≤ (target N : ℝ) := by dsimp [target]; push_cast; linarith only [hRL]
    have hQPos : 0 < (F N).lcm id := Nat.pos_of_ne_zero
      (Finset.lcm_ne_zero_iff.mpr (fun n hn => Nat.ne_of_gt (Finset.mem_Icc.mp (hF N hn)).1))
    let : NeZero ((F N).lcm id) := ⟨hQPos.ne'⟩
    refine ⟨by exact_mod_cast hTargetNonneg, ?_⟩
    have hRecipDen := reciprocalSum_den_dvd_common (Q := (F N).lcm id) (F N) (fun n hn => Finset.dvd_lcm hn)
    exact (Rat.sub_den_dvd_lcm (reciprocalSum (F N)) r).trans (Nat.lcm_dvd hRecipDen hD)
  have hMean : ∀ᶠ N : ℕ in atTop, (∑ n ∈ F N, w N / n) = (target N : ℝ) := by
    filter_upwards [hRLower] with N hRL
    exact constant_probability_mean (F N) (target N : ℝ) (hrReal.trans hRL)
  exact eventually_exact_subset_regular_family F (fun N _n => w N) target c (β / 2) τ
    hc hc1 (half_pos hβ) hτ hF hmin hSmooth hMult hMass hCard hp hVar hTarget hMean

theorem windowDenseExpansions_proved : WindowDenseExpansions := by
  intro D hD _hDsf r hr hIntegral κ hκ _hκrange θ hθ
  let ρ := coprimeDensity D
  let c := Real.exp (-((r : ℝ) + κ) / ρ)
  let β := ρ * (1 - c)
  have hρ : 0 < ρ := coprimeDensity_pos hD
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hc : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hρ)
  have hβ : 0 < β := mul_pos hρ (sub_pos.mpr hc1)
  have hLog : ρ * Real.log (1 / c) = (r : ℝ) + κ := by
    rw [one_div, Real.log_inv, show Real.log c = -((r : ℝ) + κ) / ρ from Real.log_exp _]
    field_simp [hρ.ne']
  obtain ⟨F, hSub, hSmooth, hMult, hRich, hR, hDensity, hDen⟩ := exists_regular_coprimeWindow
    D hD c hc hc1 6 (by norm_num) r.den r.den_pos hIntegral
  have hF : ∀ N, F N ⊆ Finset.Icc 1 N := fun N => (hSub N).trans (coprimeWindow_subset D c N)
  have hmin : ∀ N n, n ∈ F N → c * N ≤ (n : ℝ) := by
    intro N n hn
    exact ((mem_coprimeWindow_iff D c hc.le N n).mp (hSub N hn)).2.2.2.le
  have hMass : ∀ N q, q ∈ divisorPrimePowers N (F N) →
      1 / (Real.log (Real.log N)) ^ 2 ≤
        (q : ℝ) * (reciprocalSum ((F N).filter (fun n => q ∣ n)) : ℝ) := by
    intro N q hq
    have hqi := Finset.mem_filter.mp hq
    have hPP := (Finset.mem_filter.mp hqi.1).2
    simpa only [one_div] using hRich N q hPP hqi.2
  rw [hLog] at hR
  have hComplement := eventually_complement_regular_family F c β κ r hc hc1.le hβ hκ hr
    hF hmin hSmooth hMult hMass hR hDensity hDen
  have hRconst : Tendsto (fun _N : ℕ => (r : ℝ)) atTop (𝓝 (r : ℝ)) := tendsto_const_nhds
  have hDifference : Tendsto (fun N => (F N).card / (N : ℝ) -
      ((reciprocalSum (F N) : ℝ) - (r : ℝ))) atTop (𝓝 (β - κ)) := by
    have hh := hDensity.sub (hR.sub hRconst)
    simpa only [add_sub_cancel_left, Pi.sub_apply] using hh
  filter_upwards [hComplement, hDifference.eventually
    (Ioi_mem_nhds (by linarith : β - κ - θ < β - κ)), eventually_gt_atTop (0 : ℕ)]
      with N hSelect hLower hN
  obtain ⟨G, hGF, hGSum⟩ := hSelect
  obtain ⟨hSum, hCard⟩ := complement_expansion (hF N) hGF hGSum
  refine ⟨F N \ G, Finset.sdiff_subset.trans (hF N), ?_, hSum, ?_⟩
  · intro n hn
    have hnF := (Finset.mem_sdiff.mp hn).1
    exact ((mem_coprimeWindow_iff D c hc.le N n).mp (hSub N hnF)).2.2.1.symm
  · have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hLowerMult := mul_le_mul_of_nonneg_right hLower.le hNReal.le
    have hExpression : (((F N).card / (N : ℝ)) -
        ((reciprocalSum (F N) : ℝ) - (r : ℝ))) * N =
          ((F N).card : ℝ) - N * (reciprocalSum G : ℝ) := by
      rw [hGSum, Rat.cast_sub]
      field_simp [hNReal.ne']
    rw [hExpression] at hLowerMult
    exact hLowerMult.trans hCard

theorem erdos_problem_319 : FullAsymptotic := by
  exact fullAsymptotic_of_windowDenseExpansions windowDenseExpansions_proved

theorem erdos_problem_319_limit :
    Tendsto (fun N : ℕ => (maxSize N : ℝ) / N) atTop (𝓝 1) := by
  exact erdos_problem_319

theorem erdos_problem_319_witnesses :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ∃ δ : ℕ → ℤ,
        (∀ n : ℕ, δ n = 1 ∨ δ n = -1) ∧
        (∑ n ∈ A, (δ n : ℚ) / n) = 0 ∧
        (∀ C ⊆ A, C ≠ ∅ → C ≠ A → (∑ n ∈ C, (δ n : ℚ) / n) ≠ 0) ∧
        (1 - ε) * N ≤ (A.card : ℝ) := by
  intro ε hε
  filter_upwards [nearFullWitnesses_of_fullAsymptotic erdos_problem_319 ε hε] with N hN
  obtain ⟨A, hA, ⟨δ, hSum, hMinimal⟩, hCard⟩ := hN
  refine ⟨A, hA, fun n => (δ n : ℤ), ?_, ?_, ?_, hCard⟩
  · intro n
    exact Int.isUnit_eq_one_or (δ n).isUnit
  · simpa only [signedSum] using hSum
  · intro C hC hCne hCA hZero
    have hh : signedSum C δ = 0 := by simpa only [signedSum] using hZero
    exact (hMinimal C hC hh).elim hCne hCA

end Erdos319Formal
