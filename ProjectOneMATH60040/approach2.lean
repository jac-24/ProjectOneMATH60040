import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
The main file.
-/

namespace monotoneSetTheory

variable {α : Type*} {H : Set (α → ℝ)}

structure IsMonotoneClassSet (ℋ : Set (α → ℝ)) : Prop where
  fun_bounded_ax : ∀ f : α → ℝ, f ∈ ℋ → Bornology.IsBounded (f '' Set.univ)
  clos_add_ax : ∀ f g : α → ℝ, f ∈ ℋ → g ∈ ℋ → f + g ∈ ℋ
  clos_scal_mul_ax : ∀ f : α → ℝ, ∀ μ : ℝ, f ∈ ℋ → μ • f ∈ ℋ -- Scalar multiplication of a function
  has_one_ax : 1 ∈ ℋ
  clos_limits_ax :
    ∀ G : ℕ → (α → ℝ), Monotone G → ∀ n : ℕ, G n ≥ 0 →
    ∃ g : α → ℝ, Bornology.IsBounded (g '' Set.univ) ∧
    (∀ x : α, Filter.Tendsto (fun n => G n x) (Filter.atTop) (nhds (g x))) → g ∈ ℋ

lemma clos_add {f g : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) (hg : g ∈ H) : f + g ∈ H := by
  exact h.2 f g hf hg

lemma clos_scal_mul {f : α → ℝ} (μ : ℝ) (h : IsMonotoneClassSet H) (hf : f ∈ H) :
  μ • f ∈ H := by
  exact h.3 f μ hf

theorem clos_under_inv {f : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) : -f ∈ H := by
  rw [neg_eq_neg_one_mul]
  exact clos_scal_mul (-1) h hf

theorem clos_under_add_inv {f g : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) (hg : g ∈ H) :
  f - g ∈ H := by
  exact clos_add h hf (clos_under_inv h hg)

lemma one_in_set (h : IsMonotoneClassSet H) : 1 ∈ H := by
  exact h.4

lemma zero_in_set (h : IsMonotoneClassSet H) : 0 ∈ H := by
  rw [← sub_self 1]
  exact clos_under_add_inv h (one_in_set h) (one_in_set h)

lemma is_bounded {f : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) :
  ∃ M : ℝ, ∀ x ∈ f '' Set.univ, ‖x‖ ≤ M := by
  rw [← isBounded_iff_forall_norm_le]
  exact h.1 f hf

lemma ind_empty_set (h : IsMonotoneClassSet H) : (∅ : Set α).indicator 1 ∈ H := by
  simp only [Set.indicator_empty']
  exact zero_in_set h

lemma clos_under_compl {A : Set α} (h : IsMonotoneClassSet H) (hA : (A.indicator 1) ∈ H) :
  (Aᶜ.indicator 1 ∈ H) := by
  rw [Set.indicator_compl]
  exact clos_under_add_inv h (one_in_set h) hA



end monotoneSetTheory

variable {α : Type*} [MeasurableSpace α]

example (f : α → ℝ) (hf : Measurable f) : MeasureTheory.StronglyMeasurable f := by
  rw [stronglyMeasurable_iff_measurable]
  exact hf


example (Y : α → ℝ) (hY : Measurable Y) : Prop := by sorry

#check MeasurableSpace.measurableSet_comap


-- lemma clos_under_compl {A B : Set α} (hA : A.indicator 1 ∈ K.H) (hB : B.indicator 1 ∈ K.H)
--   (h : A ≤ B) : (B ∩ Aᶜ).indicator 1 ∈ K.H := by
--   rw [Set.inter_indicator_one, Set.indicator_compl, mul_sub_left_distrib,
--   ← Set.inter_indicator_one, mul_one, Set.inter_eq_self_of_subset_right h]
--   exact clos_under_add_inv hB hA
-- lemma clos_fin_add {n : ℕ} {f : Fin n → (α → ℝ)} (h : ∀ k : Fin n, H.Has (f k)) :
--   H.Has (∑ k , f k) := by -- f has finite domain Fin n
--   induction n with
--   | zero =>
--     -- empty sum (which is 0) is in the set
--     simp only [Finset.univ_eq_empty, Finset.sum_empty]
--     exact zero_in_set
--   | succ n ih =>
--     sorry
