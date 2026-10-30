import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Algebra.BigOperators.Fin

/-!
The main file.
-/

open Set Function MeasureTheory

namespace monotoneSetTheory

variable {α : Type*} {H : Set (α → ℝ)}

/-- A Monotone Class Set is a set of bounded functions which is closed under addition,
closed under scalar multiplication, contains the constant function 1, and is closed
under bounded limits of increasing sequences of non-negative functions.
-/
structure IsMonotoneClassSet (ℋ : Set (α → ℝ)) : Prop where
  fun_bounded_ax : ∀ f : α → ℝ, f ∈ ℋ → Bornology.IsBounded (Set.range f)
  clos_add_ax : ∀ f g : α → ℝ, f ∈ ℋ → g ∈ ℋ → f + g ∈ ℋ
  clos_scal_mul_ax : ∀ f : α → ℝ, ∀ μ : ℝ, f ∈ ℋ → μ • f ∈ ℋ -- Scalar multiplication of a function
  has_one_ax : 1 ∈ ℋ
  clos_limits_ax {G : ℕ → (α → ℝ)} {g : α → ℝ} :
    (∀ n : ℕ, G n ∈ ℋ) → Monotone G → (∀ n : ℕ, G n ≥ 0) →
    (∀ x : α, Filter.Tendsto (fun n ↦ G n x) (Filter.atTop) (nhds (g x))) →
    Bornology.IsBounded (Set.range g) → g ∈ ℋ

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
  ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M := by
  rw [← isBounded_iff_forall_norm_le]
  exact h.1 f hf

lemma clos_lims {g : α → ℝ} {G : ℕ → (α → ℝ)} (h : IsMonotoneClassSet H)
  (hg : Bornology.IsBounded (Set.range g)) (GinH : ∀ n : ℕ, G n ∈ H) (monG : Monotone G)
  (nonG : ∀ n : ℕ, G n ≥ 0) (limG : ∀ x : α, Filter.Tendsto (fun n ↦ G n x) (Filter.atTop)
  (nhds (g x))) : g ∈ H := by
  exact h.5 GinH monG nonG limG hg

-- Cannot have `G : Fin n → H`, messes this up for some reason
/-- Monotone Class Sets are closed under finite sums -/
lemma clos_fin_sum {n : ℕ} {G : (Fin n) → α → ℝ} (h : IsMonotoneClassSet H)
  (inh : ∀ k : Fin n, G k ∈ H) : ∑ k, G k ∈ H := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact zero_in_set h
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    apply clos_add h
    · exact inh 0
      -- Applying induction hypothesis that for any Fin n sum, if all the elements are in H
      -- then so are the sum
    · refine ih fun k ↦ inh k.succ

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
  Monotone (fun n ↦ (⋃ i : Fin n , G i)) := by
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
  let B := (fun n ↦ (⋃ i : Fin n, G i))
  have incrB : Monotone B := by
    sorry
  have unB : ⋃ i, B i = ⋃ i, G i := by
    sorry
  rw [← unB]
  -- `pure` means eventually equal
  have this : ∀ x : α, Filter.Tendsto (fun n ↦ (B n).indicator (1 : α → ℝ) x)
    Filter.atTop (pure ((⋃ n, B n).indicator 1 x)) := by
    sorry
  sorry
  -- apply clos_lims h

end monotoneSetTheory

open monotoneSetTheory MeasurableSpace

namespace try1

variable {α : Type*} [MeasurableSpace α]
variable {H : Set (α → ℝ)}

def indic_d_system (h : IsMonotoneClassSet H) : DynkinSystem α where
  -- This takes a set and says whether it is in this d-system or not
  Has := fun A ↦ (MeasurableSet A ∧ A.indicator 1 ∈ H)
  has_empty := ⟨MeasurableSet.empty, ind_empty_set h⟩
  -- First proving complement of measurable set is measurable and then that the indicator
  -- of the complemented set is in H
  has_compl := fun hA ↦ ⟨MeasurableSet.compl hA.1, clos_under_compl h hA.2⟩
  -- First proving that the countable union of disjoint measurable sets is a measurable set
  -- and then that the indicator of this union is in H
  has_iUnion_nat := fun _ hG ↦ ⟨MeasurableSet.iUnion fun n ↦ (hG n).1,
    increasing_indicator h (fun n ↦ (hG n).2)⟩


lemma what (I : Set (Set α)) (A : Set α) (hA : A ∈ I) : MeasurableSet A := by
  apply measurableSet_generateFrom hA


theorem mon_class_indic_fun (h : IsMonotoneClassSet H) (I : Set (Set α)) (hI : IsPiSystem I)
  (indh : ∀ A ∈ I, A.indicator 1 ∈ H) :
  -- This [] is specifying which σ-algebra want the set to be in
  ∀ A : Set α, MeasurableSet[generateFrom I] (A) → A.indicator 1 ∈ H := by
  have this : ∀ A : Set α, A ∈ I → (indic_d_system h).Has A := by
    intro A hA
    constructor
    ·
    · exact indh A hA

end try1

namespace try2

variable {α : Type*} {H : Set (α → ℝ)}

def indic_d_system (h : IsMonotoneClassSet H) (I : Set (Set α)) : DynkinSystem α where
  -- This takes a set and says whether it is in this d-system or not
  Has := fun A ↦ (MeasurableSet[generateFrom I] A ∧ A.indicator 1 ∈ H)
  has_empty := ⟨GenerateMeasurable.empty, ind_empty_set h⟩
  -- First proving complement of measurable set is measurable and then that the indicator
  -- of the complemented set is in H
  has_compl := fun hA ↦ ⟨MeasurableSet.compl hA.1, clos_under_compl h hA.2⟩
  -- First proving that the countable union of disjoint measurable sets is a measurable set
  -- and then that the indicator of this union is in H
  has_iUnion_nat := fun _ hG ↦ ⟨MeasurableSet.iUnion fun n ↦ (hG n).1,
    increasing_indicator h (fun n ↦ (hG n).2)⟩

theorem mon_class_indic_fun (h : IsMonotoneClassSet H) (I : Set (Set α)) (hI : IsPiSystem I)
  (indh : ∀ A ∈ I, A.indicator 1 ∈ H) :
  -- This [] is specifying which σ-algebra want the set to be in
  ∀ A : Set α, MeasurableSet[generateFrom I] (A) → A.indicator 1 ∈ H := by
  have this' : ∀ A : Set α, A ∈ I → (indic_d_system h I).Has A := by
    intro A hA
    constructor
    · exact measurableSet_generateFrom hA
    · exact indh A hA
  have : DynkinSystem.generate I ≤ (indic_d_system h I):= by
    apply DynkinSystem.generate_le
    intro t ht
    specialize this' t ht
    exact this'
  have another : ∀ A : Set α, MeasurableSet[generateFrom I] A → (indic_d_system h I).Has A := by
    rw [DynkinSystem.generateFrom_eq hI]
    intro A hA
    apply this
    exact hA
  intro A hA
  specialize another A hA
  sorry -- Just need to apply definition to get that any set in the indic_d_system satisfies that
  -- its indicator is in H.






end try2
