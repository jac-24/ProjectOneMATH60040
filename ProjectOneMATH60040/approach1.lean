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

variable {α : Type*}

structure monotoneClassSet where
  H : Set (α → ℝ)
  -- f image is a bounded set in ℝ so in f is bounded
  fun_bounded : ∀ f ∈ H, Bornology.IsBounded (f '' Set.univ)
  clos_add : ∀ f ∈ H, ∀ g ∈ H, f + g ∈ H
  clos_scal_mul : ∀ f ∈ H, ∀ μ : ℝ, μ • f ∈ H -- Scalar multiplication of a function
  has_one : 1 ∈ H
  clos_inc_lim : sorry
  -- ∀ G : ℕ → (α → ℝ), Monotone G →
  -- (∃ g : α → ℝ, ∀ x : α, Filter.Tendsto (fun n => G n x) (Filter.atTop) (nhds (g x))
  -- → Bornology.IsBounded (g '' Set.univ) → g ∈ H)

variable {K : monotoneClassSet}

lemma clos_add {f g : α → ℝ} (hf : f ∈ K.H) (hg : g ∈ K.H) : f + g ∈ K.H := by
  exact K.clos_add f hf g hg

lemma clos_scal_mul {f : α → ℝ} (μ : ℝ) (hf : f ∈ K.H) :
  μ • f ∈ K.H := by
  exact K.clos_scal_mul f hf μ

theorem clos_under_inv {f : α → ℝ} (h : f ∈ K.H) : -f ∈ K.H := by
  rw [neg_eq_neg_one_mul]
  apply clos_scal_mul (-1) h

theorem clos_under_add_inv {f g : α → ℝ} (hf : f ∈ K.H) (hg : g ∈ K.H) :
  f - g ∈ K.H := by
  apply clos_add hf (clos_under_inv hg)

lemma one_in_set : (1 : α → ℝ) ∈ K.H := by
  exact K.has_one

lemma zero_in_set : (0 : α → ℝ) ∈ K.H := by
  rw [← sub_self 1]
  exact clos_under_add_inv (one_in_set) (one_in_set)

lemma clos_fin_add {n : ℕ} {f : Fin n → (α → ℝ)} (h : ∀ k : Fin n, f k ∈ K.H) :
  ∑ k , f k ∈ K.H := by -- f has finite domain Fin n
  induction n with
  | zero =>
    -- empty sum (which is 0) is in the set
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact zero_in_set
  | succ n ih =>
    sorry

lemma is_bounded {f : α → ℝ} (hf : f ∈ K.H) :
  ∃ M : ℝ, ∀ x ∈ f '' Set.univ, ‖x‖ ≤ M := by
  rw [← isBounded_iff_forall_norm_le]
  exact K.fun_bounded f hf

lemma ind_empty_set : (∅ : Set α).indicator 1 ∈ K.H := by
  simp only [Set.indicator_empty']
  exact zero_in_set

lemma clos_under_compl {A : Set α} (hA : A.indicator 1 ∈ K.H) : (Aᶜ.indicator 1 ∈ K.H) := by
  rw [Set.indicator_compl]
  exact clos_under_add_inv one_in_set hA



#check Set.indicator

end monotoneSetTheory



open monotoneSetTheory

variable {α : Type*} [MeasurableSpace α]
variable {K : monotoneClassSet}



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
