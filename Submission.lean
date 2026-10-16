import Erdos319

/-!
Literal statement comparison for the question printed on page 43 of
Erdos--Graham (1980). The signs below take integer values +1 or -1;
the SAME function is used for the whole set and every proper subsum.
This audit adds no mathematical hypotheses to the submitted conclusion.
-/

open Filter Finset
open scoped Topology

namespace Erdos319Submission

def LiteralPrimitive (A : Finset ℕ) : Prop :=
  ∃ δ : ℕ → ℤ,
    (∀ n, δ n = 1 ∨ δ n = -1) ∧
    (∑ n ∈ A, (δ n : ℚ) / n) = 0 ∧
    ∀ C : Finset ℕ, C ⊂ A → C.Nonempty →
      (∑ n ∈ C, (δ n : ℚ) / n) ≠ 0

theorem literalPrimitive_iff (A : Finset ℕ) :
    LiteralPrimitive A ↔ Erdos319Formal.Primitive A := by
  rw [Erdos319Formal.primitive_iff_proper_subsets]
  constructor
  · rintro ⟨δ, hsign, htotal, hproper⟩
    let σ : ℕ → ℤˣ := fun n =>
      if δ n = 1 then 1 else -1
    have hσ : ∀ n, (σ n : ℚ) = (δ n : ℚ) := by
      intro n
      rcases hsign n with h | h
      · simp [σ, h]
      · simp [σ, h]
    refine ⟨σ, ?_, ?_⟩
    · simpa only [Erdos319Formal.signedSum, hσ] using htotal
    · intro C hC hne
      simpa only [Erdos319Formal.signedSum, hσ] using hproper C hC hne
  · rintro ⟨σ, htotal, hproper⟩
    refine ⟨fun n => (σ n : ℤ), ?_, ?_, ?_⟩
    · intro n
      exact Int.isUnit_eq_one_or (σ n).isUnit
    · simpa only [Erdos319Formal.signedSum] using htotal
    · intro C hC hne
      simpa only [Erdos319Formal.signedSum] using hproper C hC hne

theorem literal_maximum (N : ℕ) : IsGreatest
    {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      LiteralPrimitive A ∧ A.card = k}
    (Erdos319Formal.maxSize N) := by
  simpa only [literalPrimitive_iff] using Erdos319Formal.maxSize_isGreatest N

theorem original_problem_density_one :
    Tendsto (fun N : ℕ => (Erdos319Formal.maxSize N : ℝ) / N)
      atTop (𝓝 1) := Erdos319Formal.erdos_problem_319_limit

theorem original_problem_nonempty_witnesses :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.Nonempty ∧
        LiteralPrimitive A ∧ (1 - ε) * N ≤ (A.card : ℝ) := by
  intro ε hε hε1
  filter_upwards [Erdos319Formal.erdos_problem_319_witnesses ε hε,
    eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  obtain ⟨A, hA, δ, hsign, htotal, hproper, hcard⟩ := hN
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hpositive : (0 : ℝ) < A.card :=
    (mul_pos (sub_pos.mpr hε1) hNReal).trans_le hcard
  have hne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpositive)
  refine ⟨A, hA, hne, ⟨δ, hsign, htotal, ?_⟩, hcard⟩
  intro C hC hCne
  exact hproper C (Finset.ssubset_iff_subset_ne.mp hC).1 hCne.ne_empty
    (Finset.ssubset_iff_subset_ne.mp hC).2

end Erdos319Submission
