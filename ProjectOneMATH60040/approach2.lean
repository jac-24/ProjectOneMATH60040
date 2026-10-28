import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.Normed.Group.Indicator

/-!
The main file.
-/

open Set Function

namespace monotoneSetTheory

variable {α : Type*} {H : Set (α → ℝ)}

/-- A Monotone Class Set is a set of bounded functions which is closed under addition,
closed under scalar multiplication, contains the constant function 1, and is closed
under bounded limits of increasing sequences of non-negative functions.
-/
structure IsMonotoneClassSet (ℋ : Set (α → ℝ)) : Prop where
  fun_bounded_ax : ∀ f : α → ℝ, f ∈ ℋ → Bornology.IsBounded (f '' Set.univ)
  clos_add_ax : ∀ f g : α → ℝ, f ∈ ℋ → g ∈ ℋ → f + g ∈ ℋ
  clos_scal_mul_ax : ∀ f : α → ℝ, ∀ μ : ℝ, f ∈ ℋ → μ • f ∈ ℋ -- Scalar multiplication of a function
  has_one_ax : 1 ∈ ℋ
  -- `Monotone` means non-decreasing here
  clos_limits_ax {G : ℕ → (α → ℝ)} {g : α → ℝ} :
    (∀ n : ℕ, G n ∈ ℋ) → Monotone G → (∀ n : ℕ, G n ≥ 0) →
    (∀ x : α, Filter.Tendsto (fun n => G n x) (Filter.atTop) (nhds (g x))) →
    Bornology.IsBounded (g '' Set.univ ) → g ∈ ℋ

lemma clos_add {f g : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) (hg : g ∈ H) : f + g ∈ H := by
  exact h.2 f g hf hg

lemma clos_scal_mul {f : α → ℝ} (μ : ℝ) (h : IsMonotoneClassSet H) (hf : f ∈ H) :
  μ • f ∈ H := by
  exact h.3 f μ hf

lemma clos_under_inv {f : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) : -f ∈ H := by
  rw [neg_eq_neg_one_mul]
  exact clos_scal_mul (-1) h hf

lemma clos_under_add_inv {f g : α → ℝ} (h : IsMonotoneClassSet H) (hf : f ∈ H) (hg : g ∈ H) :
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

lemma clos_lims {g : α → ℝ} {G : ℕ → (α → ℝ)} (h : IsMonotoneClassSet H)
  (hg : Bornology.IsBounded (g '' Set.univ)) (GinH : ∀ n : ℕ, G n ∈ H) (monG : Monotone G)
  (nonG : ∀ n : ℕ, G n ≥ 0) (limG : ∀ x : α, Filter.Tendsto (fun n => G n x) (Filter.atTop)
  (nhds (g x))) : g ∈ H := by
  exact h.5 GinH monG nonG limG hg

/-- The indicator function of the empty set is contained in any Monotone Class Set. -/
lemma ind_empty_set (h : IsMonotoneClassSet H) : (∅ : Set α).indicator 1 ∈ H := by
  simp only [Set.indicator_empty']
  exact zero_in_set h

/-- The indicator function of the complement of a set whose indicator function is contained
in a Monotone Class Set is contained in this set. -/
lemma clos_under_compl {A : Set α} (h : IsMonotoneClassSet H) (hA : (A.indicator 1) ∈ H) :
  (Aᶜ.indicator 1 ∈ H) := by
  rw [Set.indicator_compl]
  exact clos_under_add_inv h (one_in_set h) hA

lemma set_stuff {G : ℕ → Set α} (hDis : Pairwise (Disjoint on G)) :
  Monotone (fun n => (⋃ i : Fin n , G i)) := by
  intro a b hab
  simp only [iUnion_subset_iff]
  intro k i hi
  simp only [mem_iUnion]
  sorry

lemma ind_is_bounded {A : Set α} : Bornology.IsBounded (A.indicator (1 : α → ℝ) '' Set.univ) := by
  rw [isBounded_iff_forall_norm_le]
  use 1
  intro x hx
  have : ∀ a : α, |A.indicator 1 a| ≤ |(1 : α → ℝ) a| := by
    intro a
    exact norm_indicator_le_norm_self (1 : α → ℝ) (a)
  simp only [Pi.one_apply, abs_one] at this
  simp only [image_univ, mem_range] at hx
  rcases hx with ⟨y, hy⟩
  rw [← hy]
  exact this y

-- Got Pairwise disjointness from `Dynkin system` in Mathlib
-- Need `open Function` to be able to use `on`
lemma increasing_indicator {G : ℕ → Set α} (h : IsMonotoneClassSet H)
  (hInd : ∀ n : ℕ, (G n).indicator 1 ∈ H) :
  (⋃ n, G n).indicator 1 ∈ H := by
  let B := (fun n => (⋃ i : Fin n, G i))
  have incrB : Monotone B := by
    sorry
  have unB : ⋃ i, B i = ⋃ i, G i := by
    sorry
  rw [← unB]
  -- `pure` means eventually equal
  have this : ∀ x : α, Filter.Tendsto (fun n => (B n).indicator (1 : α → ℝ) x)
    Filter.atTop (pure ((⋃ n, B n).indicator 1 x)) := by
    sorry
  sorry
  -- apply clos_lims h

end monotoneSetTheory

open monotoneSetTheory

variable {α : Type*} [MeasurableSpace α]
variable {H : Set (α → ℝ)}


example (f : α → ℝ) (hf : Measurable f) : MeasureTheory.StronglyMeasurable f := by
  rw [stronglyMeasurable_iff_measurable]
  exact hf


example (Y : α → ℝ) (hY : Measurable Y) : Prop := by sorry

#check MeasurableSpace.measurableSet_comap
