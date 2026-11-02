/-
Copyright (c) 2026 Jibreel Chaudhry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jibreel Chaudhry
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Filter.IndicatorFunction

/-!
The main file.
-/

@[expose] public section

open Set
open Function
open MeasureTheory
open MeasurableSpace

variable {α : Type*} {H : Set (α → ℝ)} {I : Set (Set α)}

/-- A Monotone Class Set is a set of bounded functions which is closed under addition,
closed under scalar multiplication, contains the constant function `1`, and is closed
under bounded limits of increasing sequences of non-negative functions.
-/
structure IsMonotoneClassSet (ℋ : Set (α → ℝ)) where
  fun_bounded_ax : ∀ f : α → ℝ, f ∈ ℋ → Bornology.IsBounded (Set.range f)
  clos_add_ax : ∀ f g : α → ℝ, f ∈ ℋ → g ∈ ℋ → f + g ∈ ℋ
  clos_scal_mul_ax : ∀ f : α → ℝ, ∀ μ : ℝ, f ∈ ℋ → μ • f ∈ ℋ
  has_one_ax : 1 ∈ ℋ
  clos_limits_ax {G : ℕ → (α → ℝ)} {g : α → ℝ} :
    (∀ n : ℕ, G n ∈ ℋ) → Monotone G → (∀ n : ℕ, 0 ≤ G n) →
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
    (hg : Bornology.IsBounded (Set.range g)) (h_inH : ∀ n : ℕ, G n ∈ H) (h_mon : Monotone G)
    (nonG : ∀ n : ℕ, 0 ≤ G n) (limG : ∀ x : α, Filter.Tendsto (fun n ↦ G n x) (Filter.atTop)
    (nhds (g x))) : g ∈ H := by
  exact h.5 h_inH h_mon nonG limG hg

-- Cannot have `G : Fin n → H`, messes this up for some reason
/-- Monotone Class Sets are closed under finite sums. -/
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

lemma ind_bound_one {A : Set α} {x : α} : ‖A.indicator (1 : α → ℝ) x‖ ≤ 1 := by
  grw [norm_indicator_le_norm_self 1 x]
  simp

lemma ind_is_bounded {A : Set α} : Bornology.IsBounded (range (A.indicator (1 : α → ℝ))) := by
  rw [isBounded_iff_forall_norm_le]
  use 1
  refine fun x hx ↦ Exists.elim hx (fun y hy ↦ ?_)
  rw [← hy]
  exact ind_bound_one

lemma mon_sets_mon_ind {G : ℕ → Set α} (hG : Monotone G) :
    Monotone (fun n ↦ (G n).indicator (1 : α → ℝ)) := by
  refine fun a b ha x ↦ indicator_le_indicator_apply_of_subset (hG ha) ?_
  simp

#check Monotone.mulIndicator_eventuallyEq_iUnion

-- `Pure` filter means converges exactly
-- Check proof of this pure convergence
lemma stand_in {G : ℕ → Set α} (h_mon : Monotone G) : ∀ x : α, Filter.Tendsto
    (fun n ↦ (G n).indicator (1 : α → ℝ) x) Filter.atTop (pure ((⋃ n, G n).indicator 1 x)) := by
  apply Monotone.tendsto_indicator
  exact h_mon

lemma incr_ind_tendto_ind_union {G : ℕ → Set α} (h : IsMonotoneClassSet H)
    (h_ind : ∀ n : ℕ, (G n).indicator 1 ∈ H) (h_mon : Monotone G) : ∀ x : α, Filter.Tendsto
    (fun n ↦ (G n).indicator (1 : α → ℝ) x) Filter.atTop (nhds ((⋃ n, G n).indicator 1 x)) := by
  sorry

lemma ind_is_nonneg {A : Set α} {x : α} : (0 : ℝ) ≤ A.indicator 1 x := by
  apply Set.indicator_nonneg
  simp

/--
Given an increasing sequence of sets indexed by `ℕ`, all of whose indicator function belong to some
Monotone Class Set `H`, we have that the the indicator on their union is contained in `H`.
-/
lemma increasing_indicator' {G : ℕ → Set α} (h : IsMonotoneClassSet H)
    (h_ind : ∀ n : ℕ, (G n).indicator 1 ∈ H) (h_mon : Monotone G) : (⋃ n, G n).indicator 1 ∈ H := by
  apply clos_lims h ind_is_bounded h_ind (mon_sets_mon_ind h_mon) ?_
  · exact incr_ind_tendto_ind_union h h_ind h_mon
  · intro n x
    simp only [Pi.zero_apply]
    exact ind_is_nonneg

lemma union_set_incr {G : ℕ → Set α} : Monotone (fun n ↦ (⋃ i : Fin n, G i)) := by
  sorry

-- Disjoint union indicator gives sum of indicators
-- <;> applies the tactic to everything

-- Got Pairwise disjointness from `Dynkin system` in Mathlib
-- Need `open Function` to be able to use `on`
lemma increasing_indicator {G : ℕ → Set α} (h : IsMonotoneClassSet H)
    (h_disj : Pairwise (Disjoint on G)) (h_ind : ∀ n : ℕ, (G n).indicator 1 ∈ H) :
    (⋃ n, G n).indicator 1 ∈ H := by
  let B := (fun n ↦ (⋃ i : Fin n, G i))
  sorry

-- These arguments need to be explicit, Lean cannot work them out for some reason
/--
The d-system formed by sets that are measurable with respect to the σ-algebra generated
by some `I : Set (Set α)` and whose indicator function is contained in `H` some
Monotone Class Set.
-/
def indic_d_system (h : IsMonotoneClassSet H) (I : Set (Set α)) : DynkinSystem α where
  -- This takes a set and says whether it is in this d-system or not
  Has A := (MeasurableSet[generateFrom I] A ∧ A.indicator 1 ∈ H)
  has_empty := ⟨GenerateMeasurable.empty, ind_empty_set h⟩
  -- First proving complement of measurable set is measurable and then that the indicator
  -- of the complemented set is in H
  has_compl := fun hA ↦ ⟨MeasurableSet.compl hA.1, clos_under_compl h hA.2⟩
  -- First proving that the countable union of disjoint measurable sets is a measurable set
  -- and then that the indicator of this union is in H
  has_iUnion_nat := fun disG hG ↦ ⟨MeasurableSet.iUnion fun n ↦ (hG n).1,
    increasing_indicator h disG (fun n ↦ (hG n).2)⟩

/-
This is essentially by definition (as set in generating set is obviously measurable
with respect to the generated sigma algebra).
-/
lemma in_pi_indic_in_d_set {A : Set α} (h : IsMonotoneClassSet H) (hA : A ∈ I)
    (h_ind : ∀ A ∈ I, A.indicator 1 ∈ H) : (indic_d_system h I).Has A :=
  ⟨measurableSet_generateFrom hA, h_ind A hA⟩

/-
This says that the d-system generated by I is contained in the indicator d-system as
generating set contained in it.
-/
lemma gen_d_sys_in_d_set (h : IsMonotoneClassSet H) (h_ind : ∀ A ∈ I, A.indicator 1 ∈ H)
    : DynkinSystem.generate I ≤ indic_d_system h I := by
  apply DynkinSystem.generate_le
  intro A hA
  exact in_pi_indic_in_d_set h hA h_ind

/-
This is the main part of the theorem, it says that any measurable set's indicator function
is in the Monotone Class Set H. Uses Dynkin pi-lambda.
-/
-- Mathlib seems to keep hypotheses like IsPiSystem explicit
lemma gen_meas_in_d_set {A : Set α} (h : IsMonotoneClassSet H) (hI : IsPiSystem I)
    -- This [] is specifying which σ-algebra want the set to be in
    (hA : MeasurableSet[generateFrom I] A) (h_ind : ∀ A ∈ I, A.indicator 1 ∈ H) :
    (indic_d_system h I).Has A := by
  rw [DynkinSystem.generateFrom_eq hI] at hA
  apply gen_d_sys_in_d_set h h_ind
  exact hA

/--
The Monotone Class Theorem for Indicator Functions. If we have a Monotone Class Set `H` and a
π-system `I` such that the indicator function of every set in `I` is contained in `H`, then we
have that the indicator function of every set in the σ-algebra generated by `I` is contained in
`H`.
-/
theorem mon_class_indic_fun {A : Set α} (h : IsMonotoneClassSet H) (hI : IsPiSystem I)
    (hA : MeasurableSet[generateFrom I] A) (h_ind : ∀ A ∈ I, A.indicator 1 ∈ H) :
    A.indicator 1 ∈ H := by
  exact (gen_meas_in_d_set h hI hA h_ind).2

/-
`@` allows one to fill in all implicit arguments. Needed here as not specifying that
`α` a measurable space. Using generated sigma algebra.
-/

lemma what' (f : letI := generateFrom I; SimpleFunc α ℝ) : letI := generateFrom I;
    f.toFun = ∑ b ∈ f.range, b • Set.indicator (f ⁻¹' {b}) (1) := by
  funext x
  simp only [Finset.sum_apply]
  sorry

lemma hmm {ι : Finset ℝ} (h : IsMonotoneClassSet H) (G : ι → α → ℝ)
    (hG : ∀ i : ι, G i ∈ H) : ∑ b : ι, G b ∈ H := by
  sorry


theorem mon_class_simp_fun (s : letI := generateFrom I; SimpleFunc α ℝ) (h : IsMonotoneClassSet H)
    (hI : IsPiSystem I) : letI := generateFrom I; s.toFun ∈ H := by
  rw [what']
  sorry


lemma mon_class_nonneg_fun (f : α → ℝ) (h : IsMonotoneClassSet H)
    (hf : Measurable[generateFrom I] f) (nonnegf : 0 ≤ f) (boundf : Bornology.IsBounded (range f)) :
    f ∈ H := by
  let measI := generateFrom I
  sorry

-- Correspondence between simple functions and sum of scaled indicators?
