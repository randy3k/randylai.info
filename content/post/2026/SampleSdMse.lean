/-
  Formal Verification of Second-Order Asymptotic Expansions for Sample Standard Deviation
  Estimators S_n and σ̂_n in Lean 4 with Mathlib.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SdMseLean

set_option linter.unusedSectionVars false

open Filter Asymptotics MeasureTheory Finset
open scoped Topology

noncomputable section

/-!
## 1. Exact Finite-Sample Moments of Sample Averages under Mutual Independence
-/

section SampleMoments

variable {RV : Type*} [CommRing RV] [Algebra ℝ RV]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (E : RV →ₗ[ℝ] ℝ)
variable (X Y : ι → RV)

/-- Sample average of an indexed family of random variables. -/
def sampleAvg (W : ι → RV) : RV := (1 / (Fintype.card ι : ℝ)) • ∑ i, W i

/-- Linearity of expectation over single sums. -/
theorem E_sum (f : ι → RV) : E (∑ i, f i) = ∑ i, E (f i) :=
  map_sum E f univ

/-- Linearity of expectation over double sums. -/
theorem E_sum2 (f : ι → ι → RV) : E (∑ i, ∑ j, f i j) = ∑ i, ∑ j, E (f i j) := by
  rw [E_sum]
  exact sum_congr rfl (fun i _ => E_sum E (f i))

/-- Linearity of expectation over triple sums. -/
theorem E_sum3 (f : ι → ι → ι → RV) :
    E (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, E (f i j k) := by
  rw [E_sum]
  exact sum_congr rfl (fun i _ => E_sum2 E (f i))

/-- Linearity of expectation over quadruple sums. -/
theorem E_sum4 (f : ι → ι → ι → ι → RV) :
    E (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, E (f i j k l) := by
  rw [E_sum]
  exact sum_congr rfl (fun i _ => E_sum3 E (f i))

/-- Expansion of the square of a sum into a double sum. -/
theorem sum_mul_sum_self (W : ι → RV) :
    (∑ i, W i) ^ 2 = ∑ i, ∑ j, W i * W j := by
  rw [sq, Fintype.sum_mul_sum]

/-- Expansion of a sum times a squared sum into a triple sum. -/
theorem sum_mul_sum2 (W Z : ι → RV) :
    (∑ i, W i) * ((∑ j, Z j) ^ 2) =
      ∑ i, ∑ j, ∑ k, W i * Z j * Z k := by
  rw [sum_mul_sum_self, sum_mul]
  refine sum_congr rfl (fun i _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun k _ => ?_)
  rw [mul_assoc]

/-- Expansion of the product of two squared sums into a quadruple sum. -/
theorem sum2_mul_sum2 (W Z : ι → RV) :
    ((∑ i, W i) ^ 2) * ((∑ k, Z k) ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l, W i * W j * Z k * Z l := by
  rw [sum_mul_sum_self, sum_mul_sum_self, sum_mul]
  refine sum_congr rfl (fun i _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun j _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun k _ => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun l _ => ?_)
  ring

/-- Exact finite-sample first moment of sample average for mean-zero variables. -/
theorem sampleAvg_moment1 (hX : ∀ i, E (X i) = 0) :
    E (sampleAvg X) = 0 := by
  dsimp [sampleAvg]
  rw [E.map_smul, E_sum]
  have : (∑ i : ι, E (X i)) = 0 := by simp [hX]
  rw [this, smul_zero]

/-- Exact finite-sample second moment (variance) of sample average for mean-zero i.i.d. variables. -/
theorem sampleAvg_moment2 (EX2 : ℝ)
    (h_cov : ∀ i j, E (X i * X j) = if i = j then EX2 else 0) :
    E (sampleAvg X ^ 2) = EX2 / (Fintype.card ι : ℝ) := by
  dsimp [sampleAvg]
  have hsmul : ((1 / (Fintype.card ι : ℝ)) • ∑ i, X i) ^ 2 =
      ((1 / (Fintype.card ι : ℝ)) ^ 2) • ((∑ i, X i) ^ 2) := by
    rw [smul_pow]
  rw [hsmul, E.map_smul, sum_mul_sum_self, E_sum2]
  have hinner : ∀ i, (∑ j : ι, E (X i * X j)) = EX2 := by
    intro i
    simp_rw [h_cov i]
    rw [sum_ite_eq_of_mem univ i (fun _ => EX2) (mem_univ i)]
  have houter : (∑ i : ι, ∑ j : ι, E (X i * X j)) = (Fintype.card ι : ℝ) * EX2 := by
    simp_rw [hinner]
    simp
  rw [houter]
  set n : ℝ := (Fintype.card ι : ℝ)
  rcases eq_or_ne n 0 with hz | hne
  · rw [hz]; ring
  · change (1 / n) ^ 2 * (n * EX2) = EX2 / n
    have h1 : (1 / n) ^ 2 = 1 / n ^ 2 := by ring
    rw [h1]
    have h2 : (1 / n ^ 2) * (n * EX2) = (n * EX2) / n ^ 2 := by ring
    rw [h2]
    have hn2 : n ^ 2 = n * n := by ring
    rw [hn2, mul_div_mul_left _ _ hne]

/-- Exact finite-sample third joint moment `E[X̄ Ȳ²]` of sample averages for mean-zero i.i.d. variables. -/
theorem sampleAvg_moment3 (EXY2 : ℝ)
    (h_cov3 : ∀ i j k, E (X i * Y j * Y k) = if i = j ∧ j = k then EXY2 else 0) :
    E (sampleAvg X * sampleAvg Y ^ 2) = EXY2 / (Fintype.card ι : ℝ) ^ 2 := by
  dsimp [sampleAvg]
  have hsmul : ((1 / (Fintype.card ι : ℝ)) • ∑ i, X i) *
      (((1 / (Fintype.card ι : ℝ)) • ∑ j, Y j) ^ 2) =
      ((1 / (Fintype.card ι : ℝ)) ^ 3) • ((∑ i, X i) * ((∑ j, Y j) ^ 2)) := by
    rw [smul_pow]
    simp only [smul_mul_smul_comm]
    have : (1 / (Fintype.card ι : ℝ)) * (1 / (Fintype.card ι : ℝ)) ^ 2 =
        (1 / (Fintype.card ι : ℝ)) ^ 3 := by ring
    rw [this]
  rw [hsmul, E.map_smul, sum_mul_sum2, E_sum3]
  have hinner3 : ∀ i j, (∑ k : ι, E (X i * Y j * Y k)) = if i = j then EXY2 else 0 := by
    intro i j
    simp_rw [h_cov3 i j]
    split_ifs with hij
    · have hiff : (fun k => if i = j ∧ j = k then EXY2 else 0) =
          fun k => if k = j then EXY2 else 0 := by
        ext k
        exact if_congr ⟨fun h => h.2.symm, fun h => ⟨hij, h.symm⟩⟩ rfl rfl
      rw [hiff]
      simp [sum_ite_eq']
    · have : (fun k => if (i = j ∧ j = k) then EXY2 else 0) = fun _ => 0 := by
        ext k; split_ifs with h
        · exfalso; exact hij h.1
        · rfl
      rw [this]
      simp
  have hinner2 : ∀ i, (∑ j : ι, ∑ k : ι, E (X i * Y j * Y k)) = EXY2 := by
    intro i
    simp_rw [hinner3 i]
    rw [sum_ite_eq_of_mem univ i (fun _ => EXY2) (mem_univ i)]
  have houter : (∑ i : ι, ∑ j : ι, ∑ k : ι, E (X i * Y j * Y k)) =
      (Fintype.card ι : ℝ) * EXY2 := by
    simp_rw [hinner2]
    simp
  rw [houter]
  set n : ℝ := (Fintype.card ι : ℝ)
  rcases eq_or_ne n 0 with hz | hne
  · rw [hz]; ring
  · change (1 / n) ^ 3 * (n * EXY2) = EXY2 / n ^ 2
    have h1 : (1 / n) ^ 3 = 1 / n ^ 3 := by ring
    rw [h1]
    have h2 : (1 / n ^ 3) * (n * EXY2) = (n * EXY2) / n ^ 3 := by ring
    rw [h2]
    have hn3 : n ^ 3 = n * n ^ 2 := by ring
    rw [hn3, mul_div_mul_left _ _ hne]

/-- Exact finite-sample fourth joint moment `E[X̄² Ȳ²]` of sample averages for mean-zero i.i.d. variables,
including the exact `1/n³` fourth-cumulant finite-sample correction. -/
theorem sampleAvg_moment4 (EX2 EY2 EXY EX2Y2 : ℝ)
    (h_cov4 : ∀ i j, (∑ k, ∑ l, E (X i * X j * Y k * Y l)) =
      if i = j then EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2)
      else 2 * EXY ^ 2) :
    E (sampleAvg X ^ 2 * sampleAvg Y ^ 2) =
      (EX2 * EY2 + 2 * EXY ^ 2) / (Fintype.card ι : ℝ) ^ 2 +
      (EX2Y2 - EX2 * EY2 - 2 * EXY ^ 2) / (Fintype.card ι : ℝ) ^ 3 := by
  dsimp [sampleAvg]
  have hsmul : (((1 / (Fintype.card ι : ℝ)) • ∑ i, X i) ^ 2) *
      (((1 / (Fintype.card ι : ℝ)) • ∑ j, Y j) ^ 2) =
      ((1 / (Fintype.card ι : ℝ)) ^ 4) • (((∑ i, X i) ^ 2) * ((∑ j, Y j) ^ 2)) := by
    rw [smul_pow, smul_pow]
    simp only [smul_mul_smul_comm]
    have : (1 / (Fintype.card ι : ℝ)) ^ 2 * (1 / (Fintype.card ι : ℝ)) ^ 2 =
        (1 / (Fintype.card ι : ℝ)) ^ 4 := by ring
    rw [this]
  rw [hsmul, E.map_smul, sum2_mul_sum2, E_sum4]
  have hinner2 : ∀ i j, (∑ k : ι, ∑ l : ι, E (X i * X j * Y k * Y l)) =
      if i = j then EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2)
      else 2 * EXY ^ 2 := h_cov4
  simp_rw [hinner2]
  have hinner_j : ∀ i : ι, (∑ j : ι,
      (if i = j then EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2)
       else 2 * EXY ^ 2)) =
      EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2) +
      ((Fintype.card ι : ℝ) - 1) * (2 * EXY ^ 2) := by
    intro i
    have hsplit : (∑ j : ι,
        (if i = j then EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2)
         else 2 * EXY ^ 2)) =
        (∑ j : ι, (if i = j then (EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2) - 2 * EXY ^ 2) else 0)) +
        (∑ j : ι, 2 * EXY ^ 2) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl (fun j _ => ?_)
      split_ifs with hij <;> ring
    rw [hsplit]
    rw [sum_ite_eq_of_mem univ i _ (mem_univ i)]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    ring
  simp_rw [hinner_j]
  have houter : (∑ i : ι,
      (EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2) +
       ((Fintype.card ι : ℝ) - 1) * (2 * EXY ^ 2))) =
      (Fintype.card ι : ℝ) *
        (EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2) +
         ((Fintype.card ι : ℝ) - 1) * (2 * EXY ^ 2)) := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [houter]
  set n : ℝ := (Fintype.card ι : ℝ)
  rcases eq_or_ne n 0 with hz | hne
  · rw [hz]; ring
  · change (1 / n) ^ 4 * (n * (EX2Y2 + (n - 1) * (EX2 * EY2) + (n - 1) * (2 * EXY ^ 2))) =
        (EX2 * EY2 + 2 * EXY ^ 2) / n ^ 2 + (EX2Y2 - EX2 * EY2 - 2 * EXY ^ 2) / n ^ 3
    have h1 : (1 / n) ^ 4 = 1 / n ^ 4 := by ring
    rw [h1]
    have h2 : (1 / n ^ 4) * (n * (EX2Y2 + (n - 1) * (EX2 * EY2) + (n - 1) * (2 * EXY ^ 2))) =
        (n * (EX2Y2 + (n - 1) * (EX2 * EY2) + (n - 1) * (2 * EXY ^ 2))) / n ^ 4 := by ring
    rw [h2]
    have hn4 : n ^ 4 = n * n ^ 3 := by ring
    rw [hn4, mul_div_mul_left _ _ hne]
    have hpoly : EX2Y2 + (n - 1) * (EX2 * EY2) + (n - 1) * (2 * EXY ^ 2) =
        n * (EX2 * EY2 + 2 * EXY ^ 2) + (EX2Y2 - EX2 * EY2 - 2 * EXY ^ 2) := by ring
    rw [hpoly]
    rw [add_div]
    have hn3 : n ^ 3 = n * n ^ 2 := by ring
    rw [hn3, mul_div_mul_left _ _ hne]

end SampleMoments

/-!
### Independence identities for real random variables

The i.i.d. hypothesis only lets us apply ordinary real functions `φ : ℝ → ℝ` to the values of each
observation, i.e. we work with the composite random variable `φ ∘ Z i : Ω → ℝ`.
-/

section Independence

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : (Ω → ℝ) → ℝ)
variable {Z : ι → Ω → ℝ}

/-- Pairwise product factoring for distinct indices `i ≠ j` from `Finset` mutual independence. -/
theorem indep_pair
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    {i j : ι} (hij : i ≠ j) (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    E ((φ ∘ Z i) * (ψ ∘ Z j)) = E ((φ ∘ Z i)) * E ((ψ ∘ Z j)) := by
  let f : ι → ℝ → ℝ := fun m => if m = i then φ else ψ
  have h := h_indep {i, j} f (fun m => by dsimp only [f]; split_ifs <;> assumption)
  rw [prod_pair hij, prod_pair hij] at h
  simpa [f, hij.symm] using h

/-- Triple product factoring for pairwise distinct indices `i, j, k` from `Finset` mutual independence. -/
theorem indep_triple
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (φ₁ φ₂ φ₃ : ℝ → ℝ) (h₁ : Measurable φ₁) (h₂ : Measurable φ₂) (h₃ : Measurable φ₃) :
    E ((φ₁ ∘ Z i) * (φ₂ ∘ Z j) * (φ₃ ∘ Z k)) =
      E ((φ₁ ∘ Z i)) * E ((φ₂ ∘ Z j)) * E ((φ₃ ∘ Z k)) := by
  let f : ι → ℝ → ℝ := fun m => if m = i then φ₁ else if m = j then φ₂ else φ₃
  have hi_not_mem : i ∉ ({j, k} : Finset ι) := by
    simp [hij, hik]
  have h := h_indep (insert i {j, k}) f (fun m => by dsimp only [f]; split_ifs <;> assumption)
  rw [prod_insert hi_not_mem, prod_pair hjk, prod_insert hi_not_mem, prod_pair hjk] at h
  simpa [f, hij.symm, hik.symm, hjk.symm, mul_assoc] using h

/-- Quadruple product factoring for pairwise distinct indices `i, j, k, l` from `Finset` mutual independence. -/
theorem indep_quad
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    {i j k l : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (φ₁ φ₂ φ₃ φ₄ : ℝ → ℝ) (h₁ : Measurable φ₁) (h₂ : Measurable φ₂) (h₃ : Measurable φ₃)
    (h₄ : Measurable φ₄) :
    E ((φ₁ ∘ Z i) * (φ₂ ∘ Z j) * (φ₃ ∘ Z k) * (φ₄ ∘ Z l)) =
      E ((φ₁ ∘ Z i)) * E ((φ₂ ∘ Z j)) * E ((φ₃ ∘ Z k)) * E ((φ₄ ∘ Z l)) := by
  let f : ι → ℝ → ℝ := fun m =>
    if m = i then φ₁ else if m = j then φ₂ else if m = k then φ₃ else φ₄
  have hj_not_mem : j ∉ ({k, l} : Finset ι) := by simp [hjk, hjl]
  have hi_not_mem : i ∉ (insert j {k, l} : Finset ι) := by simp [hij, hik, hil]
  have h := h_indep (insert i (insert j {k, l})) f
    (fun m => by dsimp only [f]; split_ifs <;> assumption)
  rw [prod_insert hi_not_mem, prod_insert hj_not_mem, prod_pair hkl,
      prod_insert hi_not_mem, prod_insert hj_not_mem, prod_pair hkl] at h
  simpa [f, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm, mul_assoc] using h

/-- If index `l` is distinct from `i, j, k` and `E[φ₄(Z l)] = 0`, the four-factor expectation vanishes. -/
theorem E_mul4_eq_zero_of_isolated
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    {i j k l : ι} (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (φ₁ φ₂ φ₃ φ₄ : ℝ → ℝ) (h₁ : Measurable φ₁) (h₂ : Measurable φ₂) (h₃ : Measurable φ₃)
    (h₄ : Measurable φ₄) (h0 : E ((φ₄ ∘ Z l)) = 0) :
    E ((φ₁ ∘ Z i) * (φ₂ ∘ Z j) * (φ₃ ∘ Z k) * (φ₄ ∘ Z l)) = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rcases eq_or_ne i k with rfl | hik
    · have h := indep_pair E h_indep hil (fun z => φ₁ z * φ₂ z * φ₃ z) φ₄
        ((h₁.mul h₂).mul h₃) h₄
      rw [h0, mul_zero] at h; exact h
    · have h := indep_triple E h_indep hik hil hkl (fun z => φ₁ z * φ₂ z) φ₃ φ₄
        (h₁.mul h₂) h₃ h₄
      rw [h0, mul_zero] at h; exact h
  · rcases eq_or_ne k i with rfl | hki
    · have heq : (φ₁ ∘ Z k) * (φ₂ ∘ Z j) * (φ₃ ∘ Z k) * (φ₄ ∘ Z l) =
          ((φ₁ ∘ Z k) * (φ₃ ∘ Z k)) * (φ₂ ∘ Z j) * (φ₄ ∘ Z l) := by ring
      rw [heq]
      have h := indep_triple E h_indep hij hil hjl (fun z => φ₁ z * φ₃ z) φ₂ φ₄
        (h₁.mul h₃) h₂ h₄
      rw [h0, mul_zero] at h; exact h
    · rcases eq_or_ne k j with rfl | hkj
      · have heq : (φ₁ ∘ Z i) * (φ₂ ∘ Z k) * (φ₃ ∘ Z k) * (φ₄ ∘ Z l) =
            (φ₁ ∘ Z i) * ((φ₂ ∘ Z k) * (φ₃ ∘ Z k)) * (φ₄ ∘ Z l) := by ring
        rw [heq]
        have h := indep_triple E h_indep hij hil hjl φ₁ (fun z => φ₂ z * φ₃ z) φ₄
          h₁ (h₂.mul h₃) h₄
        rw [h0, mul_zero] at h; exact h
      · have h := indep_quad E h_indep hij hki.symm hil hkj.symm hjl hkl φ₁ φ₂ φ₃ φ₄
          h₁ h₂ h₃ h₄
        rw [h0, mul_zero] at h; exact h

/-- Proved degree-2 covariance identity from mutual independence and mean zero. -/
theorem cov2_of_indep
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    (φ : ℝ → ℝ) (hφ : Measurable φ) (EX2 : ℝ)
    (h1 : ∀ i, E ((φ ∘ Z i)) = 0)
    (h2 : ∀ i, E ((φ ∘ Z i) ^ 2) = EX2)
    (i j : ι) :
    E ((φ ∘ Z i) * (φ ∘ Z j)) = if i = j then EX2 else 0 := by
  split_ifs with hij
  · subst hij
    rw [← sq, h2 i]
  · rw [indep_pair E h_indep hij φ φ hφ hφ, h1 i, h1 j, mul_zero]

/-- Proved degree-3 joint product moment identity from mutual independence and mean zero. -/
theorem cov3_of_indep
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) (EXY2 : ℝ)
    (hφ1 : ∀ i, E ((φ ∘ Z i)) = 0)
    (hψ1 : ∀ i, E ((ψ ∘ Z i)) = 0)
    (hXY2 : ∀ i, E ((φ ∘ Z i) * (ψ ∘ Z i) ^ 2) = EXY2)
    (i j k : ι) :
    E ((φ ∘ Z i) * (ψ ∘ Z j) * (ψ ∘ Z k)) = if i = j ∧ j = k then EXY2 else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    have heq : (φ ∘ Z i) * (ψ ∘ Z i) * (ψ ∘ Z i) = (φ ∘ Z i) * (ψ ∘ Z i) ^ 2 := by ring
    rw [heq, hXY2 i]
  · rcases eq_or_ne j k with rfl | hjk
    · have hij : i ≠ j := fun hij => h ⟨hij, rfl⟩
      have heq : (φ ∘ Z i) * (ψ ∘ Z j) * (ψ ∘ Z j) = ((ψ ∘ Z j) * (ψ ∘ Z j)) * (φ ∘ Z i) := by ring
      rw [heq]
      have hp := indep_pair E h_indep hij.symm (fun z => ψ z * ψ z) φ
        (hψ.mul hψ) hφ
      rw [hφ1 i, mul_zero] at hp; exact hp
    · rcases eq_or_ne k i with rfl | hki
      · have heq : (φ ∘ Z k) * (ψ ∘ Z j) * (ψ ∘ Z k) = ((φ ∘ Z k) * (ψ ∘ Z k)) * (ψ ∘ Z j) := by ring
        rw [heq]
        have hp := indep_pair E h_indep hjk.symm (fun z => φ z * ψ z) ψ (hφ.mul hψ) hψ
        rw [hψ1 j, mul_zero] at hp; exact hp
      · rcases eq_or_ne i j with rfl | hij
        · have hp := indep_pair E h_indep hki.symm (fun z => φ z * ψ z) ψ (hφ.mul hψ) hψ
          rw [hψ1 k, mul_zero] at hp; exact hp
        · have hp := indep_triple E h_indep hij hki.symm hjk φ ψ ψ hφ hψ hψ
          rw [hp, hψ1 k, mul_zero]

/-- Proved degree-4 collision sum identity from mutual independence and marginal moments. -/
theorem cov4_of_indep
    (h_indep : ∀ (s : Finset ι) (f : ι → ℝ → ℝ), (∀ m, Measurable (f m)) →
      E (∏ m ∈ s, (f m ∘ Z m)) = ∏ m ∈ s, E ((f m ∘ Z m)))
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) (EX2 EY2 EXY EX2Y2 : ℝ)
    (hφ1 : ∀ i, E ((φ ∘ Z i)) = 0)
    (hψ1 : ∀ i, E ((ψ ∘ Z i)) = 0)
    (hX2 : ∀ i, E ((φ ∘ Z i) ^ 2) = EX2)
    (hY2 : ∀ i, E ((ψ ∘ Z i) ^ 2) = EY2)
    (hXY : ∀ i, E ((φ ∘ Z i) * (ψ ∘ Z i)) = EXY)
    (hX2Y2 : ∀ i, E ((φ ∘ Z i) ^ 2 * (ψ ∘ Z i) ^ 2) = EX2Y2)
    (i j : ι) :
    (∑ k : ι, ∑ l : ι, E ((φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z k) * (ψ ∘ Z l))) =
      if i = j then EX2Y2 + ((Fintype.card ι : ℝ) - 1) * (EX2 * EY2)
      else 2 * EXY ^ 2 := by
  split_ifs with hij
  · subst hij
    have h_inner : ∀ k : ι, (∑ l : ι, E ((φ ∘ Z i) * (φ ∘ Z i) * (ψ ∘ Z k) * (ψ ∘ Z l))) =
        if k = i then EX2Y2 else EX2 * EY2 := by
      intro k
      have h_term : ∀ l : ι, E ((φ ∘ Z i) * (φ ∘ Z i) * (ψ ∘ Z k) * (ψ ∘ Z l)) =
          if l = k then E ((φ ∘ Z i) ^ 2 * (ψ ∘ Z k) ^ 2) else 0 := by
        intro l
        split_ifs with hlk
        · subst hlk
          have heq : (φ ∘ Z i) * (φ ∘ Z i) * (ψ ∘ Z l) * (ψ ∘ Z l) = (φ ∘ Z i) ^ 2 * (ψ ∘ Z l) ^ 2 := by ring
          rw [heq]
        · rcases eq_or_ne l i with rfl | hli
          · have heq : (φ ∘ Z l) * (φ ∘ Z l) * (ψ ∘ Z k) * (ψ ∘ Z l) =
                (φ ∘ Z l) * (φ ∘ Z l) * (ψ ∘ Z l) * (ψ ∘ Z k) := by ring
            rw [heq]
            exact E_mul4_eq_zero_of_isolated E h_indep hlk hlk hlk
              φ φ ψ ψ hφ hφ hψ hψ (hψ1 k)
          · exact E_mul4_eq_zero_of_isolated E h_indep (Ne.symm hli) (Ne.symm hli) (Ne.symm hlk)
              φ φ ψ ψ hφ hφ hψ hψ (hψ1 l)
      simp_rw [h_term]
      rw [sum_ite_eq' univ k]
      simp only [mem_univ, ↓reduceIte]
      split_ifs with hki
      · subst hki
        exact hX2Y2 k
      · have hp := indep_pair E h_indep (Ne.symm hki) (fun z => φ z ^ 2) (fun z => ψ z ^ 2)
          (hφ.pow_const 2) (hψ.pow_const 2)
        have e1 : E ((fun z => φ z ^ 2) ∘ Z i) = EX2 := hX2 i
        have e2 : E ((fun z => ψ z ^ 2) ∘ Z k) = EY2 := hY2 k
        rw [e1, e2] at hp; exact hp
    simp_rw [h_inner]
    have hsplit : (∑ k : ι, (if k = i then EX2Y2 else EX2 * EY2)) =
        (∑ k : ι, (if k = i then EX2Y2 - EX2 * EY2 else 0)) +
        (∑ k : ι, EX2 * EY2) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl (fun k _ => ?_)
      split_ifs <;> ring
    rw [hsplit, sum_ite_eq' univ i]
    simp only [mem_univ, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul]
    ring
  · have h_term : ∀ k l : ι, E ((φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z k) * (ψ ∘ Z l)) =
        if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then EXY ^ 2 else 0 := by
      intro k l
      split_ifs with hkl_cases
      · rcases hkl_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have heq : (φ ∘ Z k) * (φ ∘ Z l) * (ψ ∘ Z k) * (ψ ∘ Z l) =
              ((φ ∘ Z k) * (ψ ∘ Z k)) * ((φ ∘ Z l) * (ψ ∘ Z l)) := by ring
          rw [heq]
          have hp := indep_pair E h_indep hij (fun z => φ z * ψ z) (fun z => φ z * ψ z)
            (hφ.mul hψ) (hφ.mul hψ)
          have e1 : E ((fun z => φ z * ψ z) ∘ Z k) = EXY := hXY k
          have e2 : E ((fun z => φ z * ψ z) ∘ Z l) = EXY := hXY l
          rw [e1, e2, ← sq] at hp; exact hp
        · have heq : (φ ∘ Z l) * (φ ∘ Z k) * (ψ ∘ Z k) * (ψ ∘ Z l) =
              ((φ ∘ Z l) * (ψ ∘ Z l)) * ((φ ∘ Z k) * (ψ ∘ Z k)) := by ring
          rw [heq]
          have hp := indep_pair E h_indep hij (fun z => φ z * ψ z) (fun z => φ z * ψ z)
            (hφ.mul hψ) (hφ.mul hψ)
          have e1 : E ((fun z => φ z * ψ z) ∘ Z k) = EXY := hXY k
          have e2 : E ((fun z => φ z * ψ z) ∘ Z l) = EXY := hXY l
          rw [e1, e2, ← sq] at hp; exact hp
      · rcases eq_or_ne k l with rfl | hkl
        · rcases eq_or_ne i k with rfl | hik
          · have heq : (φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z i) * (ψ ∘ Z i) =
                (φ ∘ Z i) * (ψ ∘ Z i) * (ψ ∘ Z i) * (φ ∘ Z j) := by ring
            rw [heq]
            exact E_mul4_eq_zero_of_isolated E h_indep hij hij hij φ ψ ψ φ hφ hψ hψ hφ (hφ1 j)
          · have heq : (φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z k) * (ψ ∘ Z k) =
                (φ ∘ Z j) * (ψ ∘ Z k) * (ψ ∘ Z k) * (φ ∘ Z i) := by ring
            rw [heq]
            exact E_mul4_eq_zero_of_isolated E h_indep (Ne.symm hij) (Ne.symm hik) (Ne.symm hik)
              φ ψ ψ φ hφ hψ hψ hφ (hφ1 i)
        · rcases eq_or_ne k i with rfl | hki
          · have hlj : l ≠ j := fun hlj => hkl_cases (Or.inl ⟨rfl, hlj⟩)
            exact E_mul4_eq_zero_of_isolated E h_indep hkl (Ne.symm hlj) hkl
              φ φ ψ ψ hφ hφ hψ hψ (hψ1 l)
          · rcases eq_or_ne k j with rfl | hkj
            · have hli : l ≠ i := fun hli => hkl_cases (Or.inr ⟨rfl, hli⟩)
              exact E_mul4_eq_zero_of_isolated E h_indep (Ne.symm hli) hkl hkl
                φ φ ψ ψ hφ hφ hψ hψ (hψ1 l)
            · have heq : (φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z k) * (ψ ∘ Z l) =
                  (φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z l) * (ψ ∘ Z k) := by ring
              rw [heq]
              exact E_mul4_eq_zero_of_isolated E h_indep (Ne.symm hki) (Ne.symm hkj) (Ne.symm hkl)
                φ φ ψ ψ hφ hφ hψ hψ (hψ1 k)
    have h_inner : ∀ k : ι, (∑ l : ι, E ((φ ∘ Z i) * (φ ∘ Z j) * (ψ ∘ Z k) * (ψ ∘ Z l))) =
        if k = i then EXY ^ 2 else if k = j then EXY ^ 2 else 0 := by
      intro k
      simp_rw [h_term k]
      split_ifs with hki hkj
      · subst hki
        trans (∑ l : ι, if l = j then EXY ^ 2 else 0)
        · refine sum_congr rfl (fun l _ => ?_)
          congr 1
          exact propext ⟨fun h => h.elim (fun h1 => h1.2) (fun h2 => (hij h2.1).elim),
                         fun h => Or.inl ⟨rfl, h⟩⟩
        · simp [sum_ite_eq']
      · subst hkj
        trans (∑ l : ι, if l = i then EXY ^ 2 else 0)
        · refine sum_congr rfl (fun l _ => ?_)
          congr 1
          exact propext ⟨fun h => h.elim (fun h1 => (hki h1.1).elim) (fun h2 => h2.2),
                         fun h => Or.inr ⟨rfl, h⟩⟩
        · simp [sum_ite_eq']
      · trans (∑ _l : ι, (0 : ℝ))
        · refine sum_congr rfl (fun l _ => ?_)
          simp [hki, hkj]
        · simp
    simp_rw [h_inner]
    have hsplit : (∑ k : ι, (if k = i then EXY ^ 2 else if k = j then EXY ^ 2 else 0)) =
        (∑ k : ι, (if k = i then EXY ^ 2 else 0)) +
        (∑ k : ι, (if k = j then EXY ^ 2 else 0)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl (fun k _ => ?_)
      split_ifs with h1 h2
      · exfalso; exact hij (h1.symm.trans h2)
      · ring
      · ring
      · ring
    rw [hsplit, sum_ite_eq' univ i, sum_ite_eq' univ j]
    simp only [mem_univ, ↓reduceIte]
    ring

end Independence

/-!
## 2. Exact Finite-Sample Model Setup (`structure IsIID` and `class SampleModel`)

We work on a general probability space `(Ω, μ)` (`[MeasurableSpace Ω] [IsProbabilityMeasure μ]`).
Random variables with all moments finite form the subalgebra `momAlg μ` of `Ω → ℝ`
(`X ^ k` integrable for every `k : ℕ`), on which expectation `E X = ∫ ω, X ω ∂μ` is linear.
-/

/-- Products of variables with all moments finite are integrable, via `|a b| ≤ a² + b²`. -/
theorem integrable_pow_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : ∀ k : ℕ, Integrable (X ^ k) μ) (hY : ∀ k : ℕ, Integrable (Y ^ k) μ) (a b : ℕ) :
    Integrable (X ^ a * Y ^ b) μ := by
  refine Integrable.mono' ((hX (2 * a)).add (hY (2 * b)))
    ((hX a).aestronglyMeasurable.mul (hY b).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs, pow_mul']
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (X ω ^ a + Y ω ^ b), sq_nonneg (X ω ^ a - Y ω ^ b),
    sq_nonneg (X ω ^ a), sq_nonneg (Y ω ^ b)]

/-- Real random variables with all moments finite (`X ^ k` integrable for every `k : ℕ`).
    They form a subalgebra of `Ω → ℝ`, so expectation is linear on it. -/
def momAlg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Subalgebra ℝ (Ω → ℝ) where
  carrier := {X | ∀ k : ℕ, Integrable (X ^ k) μ}
  mul_mem' {X Y} hX hY := by
    show ∀ k : ℕ, Integrable ((X * Y) ^ k) μ
    intro k
    rw [mul_pow]; exact integrable_pow_mul hX hY k k
  add_mem' {X Y} hX hY := by
    show ∀ k : ℕ, Integrable ((X + Y) ^ k) μ
    intro k
    rw [add_pow]
    refine integrable_finset_sum' _ fun m _ => ?_
    refine ((integrable_pow_mul hX hY m (k - m)).mul_const ((k.choose m : ℕ) : ℝ)).congr
      (ae_of_all _ fun ω => ?_)
    simp
  algebraMap_mem' c := by
    show ∀ k : ℕ, Integrable ((algebraMap ℝ (Ω → ℝ) c) ^ k) μ
    intro k
    have h : (algebraMap ℝ (Ω → ℝ) c) ^ k = fun _ => c ^ k := by funext ω; simp
    rw [h]; exact integrable_const _

theorem mem_momAlg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} : X ∈ momAlg μ ↔ ∀ k : ℕ, Integrable (X ^ k) μ := Iff.rfl

/-- **Textbook i.i.d. sample model.** The observations `X 0, X 1, X 2, …` are measurable,
    mutually independent (Mathlib's `iIndepFun`), identically distributed (Mathlib's
    `IdentDistrib`), have all moments finite, and have positive variance (Mathlib's `variance`). -/
class SampleModel (Ω : outParam Type*) [MeasurableSpace Ω]
    (μ : outParam (Measure Ω)) [IsProbabilityMeasure μ] where
  X : ℕ → Ω → ℝ
  measurable : ∀ i, Measurable (X i)
  indep : ProbabilityTheory.iIndepFun X μ
  ident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ
  moments : ∀ k : ℕ, Integrable (fun ω => X 0 ω ^ k) μ
  var_pos : 0 < ProbabilityTheory.variance (X 0) μ

namespace SampleModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] [SampleModel Ω μ]

/-- Raw expectation of a real function: Mathlib's Bochner integral. -/
def Eraw (ν : Measure Ω) (f : Ω → ℝ) : ℝ := ∫ ω, f ω ∂ν

/-- Expectation of a random variable with all moments finite. -/
def E (X : momAlg μ) : ℝ := Eraw μ X

theorem E_def (X : momAlg μ) : E X = ∫ ω, (X : Ω → ℝ) ω ∂μ := rfl

theorem momAlg_integrable_pow (X : momAlg μ) (k : ℕ) : Integrable ((X : Ω → ℝ) ^ k) μ :=
  mem_momAlg.mp X.2 k

theorem momAlg_integrable (X : momAlg μ) : Integrable (X : Ω → ℝ) μ := by
  simpa using momAlg_integrable_pow X 1

theorem sqrt_pow_le (x : ℝ) (k : ℕ) : |Real.sqrt x ^ k| ≤ 1 + x ^ (2 * k) := by
  have hs := Real.sqrt_nonneg x
  rw [abs_of_nonneg (pow_nonneg hs k)]
  have hx2 : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) k
  rcases le_total (Real.sqrt x) 1 with h | h
  · have := pow_le_one₀ (n := k) hs h
    linarith
  · have hx0 : 0 ≤ x := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero'.mpr hneg.le] at h
      linarith
    have hsq := Real.sq_sqrt hx0
    have hx1 : 1 ≤ x := by nlinarith
    have hsx : Real.sqrt x ≤ x := by nlinarith
    have h1 : Real.sqrt x ^ k ≤ x ^ k := pow_le_pow_left₀ hs hsx k
    have h2 : x ^ k ≤ x ^ (2 * k) := pow_le_pow_right₀ hx1 (by omega)
    linarith

/-- Pointwise square root, which keeps all moments finite. -/
def sqrt (X : momAlg μ) : momAlg μ :=
  ⟨fun ω => Real.sqrt ((X : Ω → ℝ) ω), mem_momAlg.mpr fun k => by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (momAlg_integrable_pow X (2 * k)))
      ((Real.continuous_sqrt.comp_aestronglyMeasurable
        (momAlg_integrable X).aestronglyMeasurable).pow k) (ae_of_all _ fun ω => ?_)
    simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs]
    exact sqrt_pow_le _ k⟩

/-- `E 1 = 1` from Mathlib's `integral_const` and `[IsProbabilityMeasure μ]`. -/
theorem E_one : E (1 : momAlg μ) = 1 := by
  simp [E_def]

/-- Linearity of expectation from Mathlib's `integral_add` and `integral_smul`. -/
def E_lm : momAlg μ →ₗ[ℝ] ℝ where
  toFun := E
  map_add' X Y := by
    simp only [E_def]
    exact integral_add (momAlg_integrable X) (momAlg_integrable Y)
  map_smul' c X := by
    simp only [E_def, RingHom.id_apply]
    exact integral_smul c (X : Ω → ℝ)

@[simp] theorem E_add (X Y : momAlg μ) : E (X + Y) = E X + E Y := E_lm.map_add X Y
@[simp] theorem E_smul (c : ℝ) (X : momAlg μ) : E (c • X) = c * E X := E_lm.map_smul c X
@[simp] theorem E_sub (X Y : momAlg μ) : E (X - Y) = E X - E Y := E_lm.map_sub X Y
@[simp] theorem E_neg (X : momAlg μ) : E (-X) = -E X := E_lm.map_neg X

/-- Population mean `m = E[X₀]`. -/
def mean : ℝ := ∫ ω, SampleModel.X 0 ω ∂μ

/-- Population standard deviation `σ = √Var(X₀)`. -/
def σ : ℝ := Real.sqrt (ProbabilityTheory.variance (SampleModel.X 0) μ)

/-- Standardized moments `λ_k = E[((X₀ - m) / σ)^k]`. -/
def lam (k : ℕ) : ℝ := ∫ ω, ((SampleModel.X 0 ω - mean (μ := μ)) / σ (μ := μ)) ^ k ∂μ

abbrev lam3 : ℝ := lam (μ := μ) 3
abbrev lam4 : ℝ := lam (μ := μ) 4
abbrev lam6 : ℝ := lam (μ := μ) 6
abbrev lam8 : ℝ := lam (μ := μ) 8

theorem hσ : (0 : ℝ) < σ (μ := μ) := Real.sqrt_pos.mpr SampleModel.var_pos

theorem X_mem (i : ℕ) : SampleModel.X i ∈ momAlg μ := mem_momAlg.mpr fun k =>
  ((SampleModel.ident (μ := μ) i).comp (u := fun x : ℝ => x ^ k) (by fun_prop)).integrable_iff.mpr
    (SampleModel.moments k)

/-- Standardized observation `Z_i = (X_i - m) / σ`. -/
def Zr (i : ℕ) : Ω → ℝ := fun ω => (SampleModel.X i ω - mean (μ := μ)) / σ (μ := μ)

theorem Zr_measurable (i : ℕ) : Measurable (Zr (μ := μ) i) :=
  ((SampleModel.measurable i).sub_const _).div_const _

theorem Zr_mem (i : ℕ) : Zr (μ := μ) i ∈ momAlg μ := by
  have h : Zr (μ := μ) i = algebraMap ℝ (Ω → ℝ) (1 / σ (μ := μ)) *
      (SampleModel.X i - algebraMap ℝ (Ω → ℝ) (mean (μ := μ))) := by
    funext ω
    show (SampleModel.X i ω - mean (μ := μ)) / σ (μ := μ) =
      (1 / σ (μ := μ)) * (SampleModel.X i ω - mean (μ := μ))
    ring
  rw [h]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (X_mem i) (Subalgebra.algebraMap_mem _ _))

/-- Standardized observation as an element of the moment algebra. -/
def Zs (i : ℕ) : momAlg μ := ⟨Zr i, Zr_mem i⟩

/-- The `i`-th standardized observation of a sample of size `n`. -/
def Zm (n : ℕ) (i : Fin n) : momAlg μ := Zs i.val

theorem Zr_indep : ProbabilityTheory.iIndepFun (fun i => Zr (μ := μ) i) μ :=
  SampleModel.indep.comp (fun _ x => (x - mean (μ := μ)) / σ (μ := μ)) (fun _ => by fun_prop)

theorem Zr_ident (i : ℕ) : ProbabilityTheory.IdentDistrib (Zr (μ := μ) i) (Zr 0) μ μ :=
  (SampleModel.ident i).comp (u := fun x => (x - mean (μ := μ)) / σ (μ := μ)) (by fun_prop)

theorem E_Zs_pow (i k : ℕ) : E ((Zs i : momAlg μ) ^ k) = lam k :=
  ((Zr_ident (μ := μ) i).comp (u := fun x : ℝ => x ^ k) (by fun_prop)).integral_eq

theorem lam_one : lam (μ := μ) 1 = 0 := by
  have hX : Integrable (SampleModel.X (μ := μ) 0) μ := by
    simpa using SampleModel.moments (μ := μ) 1
  simp only [lam, pow_one]
  rw [integral_div, integral_sub hX (integrable_const _)]
  simp [mean]

theorem lam_two : lam (μ := μ) 2 = 1 := by
  have hvar : ProbabilityTheory.variance (SampleModel.X 0) μ =
      ∫ ω, (SampleModel.X 0 ω - mean (μ := μ)) ^ 2 ∂μ :=
    ProbabilityTheory.variance_eq_integral (SampleModel.measurable 0).aemeasurable
  have hσ2 : σ (μ := μ) ^ 2 = ProbabilityTheory.variance (SampleModel.X 0) μ :=
    Real.sq_sqrt (le_of_lt SampleModel.var_pos)
  simp only [lam, div_pow]
  rw [integral_div, ← hvar, ← hσ2]
  exact div_self (pow_ne_zero 2 (hσ (μ := μ)).ne')

@[simp] theorem E_Z1 (n : ℕ) (i : Fin n) : E (Zm n i : momAlg μ) = 0 := by
  have h := E_Zs_pow (μ := μ) i.val 1
  rw [pow_one, lam_one] at h
  exact h
@[simp] theorem E_Z2 (n : ℕ) (i : Fin n) : E ((Zm n i : momAlg μ) ^ 2) = 1 := by
  rw [← lam_two (μ := μ)]; exact E_Zs_pow i.val 2
@[simp] theorem E_Z3 (n : ℕ) (i : Fin n) : E ((Zm n i : momAlg μ) ^ 3) = lam3 := E_Zs_pow i.val 3
@[simp] theorem E_Z4 (n : ℕ) (i : Fin n) : E ((Zm n i : momAlg μ) ^ 4) = lam4 := E_Zs_pow i.val 4
@[simp] theorem E_Z6 (n : ℕ) (i : Fin n) : E ((Zm n i : momAlg μ) ^ 6) = lam6 := E_Zs_pow i.val 6
@[simp] theorem E_Z8 (n : ℕ) (i : Fin n) : E ((Zm n i : momAlg μ) ^ 8) = lam8 := E_Zs_pow i.val 8

theorem E_A (n : ℕ) (i : Fin n) : E ((Zm n i : momAlg μ) ^ 2 - 1) = 0 := by
  simp [E_one]

@[simp] theorem E_lm_apply (X : momAlg μ) : E_lm X = E X := rfl

/-- Composite form of the centered square `A = Z² - 1`. -/
theorem comp_A (X : Ω → ℝ) : (fun z : ℝ => z ^ 2 - 1) ∘ X = X ^ 2 - 1 := by
  funext ω; simp

/-- Mutual independence (Mathlib's `iIndepFun.integral_fun_prod_comp`) for measurable test
    functions of the standardized observations of a sample of size `n`. -/
theorem indep_E (n : ℕ) : ∀ (s : Finset (Fin n)) (f : Fin n → ℝ → ℝ), (∀ m, Measurable (f m)) →
    Eraw μ (∏ m ∈ s, f m ∘ ((Zm n m : momAlg μ) : Ω → ℝ)) =
      ∏ m ∈ s, Eraw μ (f m ∘ ((Zm n m : momAlg μ) : Ω → ℝ)) := by
  intro s f hf
  have hind : ProbabilityTheory.iIndepFun (fun j : s => Zr (μ := μ) (j : Fin n).val) μ :=
    Zr_indep.precomp (Fin.val_injective.comp Subtype.val_injective)
  have h := hind.integral_fun_prod_comp (f := fun j : s => f j)
    (fun j => (Zr_measurable _).aemeasurable) (fun j => (hf j).aestronglyMeasurable)
  simp only [Finset.univ_eq_attach] at h
  have e1 : ∀ ω, ∏ i ∈ s.attach, f (↑i) (Zr (μ := μ) (↑↑i) ω) =
      ∏ m ∈ s, f m (Zr (μ := μ) m.val ω) :=
    fun ω => Finset.prod_attach s (fun m => f m (Zr (μ := μ) m.val ω))
  have e2 : ∏ i ∈ s.attach, ∫ ω, f (↑i) (Zr (μ := μ) (↑↑i) ω) ∂μ =
      ∏ m ∈ s, ∫ ω, f m (Zr (μ := μ) m.val ω) ∂μ :=
    Finset.prod_attach s (fun m => ∫ ω, f m (Zr (μ := μ) m.val ω) ∂μ)
  simp only [e1] at h
  rw [e2] at h
  simp only [Eraw, Finset.prod_apply, Function.comp_apply]
  exact h

/-!
## 2. Standard Mathematical Definitions (`def` / `abbrev`) and the Moment Rate Hypothesis
-/

/-- Scalar embedding `const c = algebraMap ℝ (momAlg μ) c`. -/
abbrev const (c : ℝ) : momAlg μ := algebraMap ℝ (momAlg μ) c

/-- Centered sample second moment: `U n = (1/n) ∑ (Z_i² - 1)`. -/
def U (n : ℕ) : momAlg μ := sampleAvg (fun i : Fin n => (Zm n i) ^ 2 - 1)

/-- Standardized sample mean: `V n = Z̄ = (1/n) ∑ Z_i`. -/
def V (n : ℕ) : momAlg μ := sampleAvg (Zm n)

/-- Scalar `1/n` embedded in `momAlg μ`. -/
def invN (n : ℕ) : momAlg μ := const (1 / (n : ℝ))

/-- Relative sample variance fluctuation for `σ̂_n²`: `1 + D n = (1/n) ∑ (Z_i - Z̄)² = 1 + U n - V n²`. -/
def D (n : ℕ) : momAlg μ := U n - V n ^ 2

/-- Relative sample variance fluctuation for `S_n²`: `1 + Δ n = (n / (n - 1)) (1 + D n)`. -/
def Δ (n : ℕ) : momAlg μ := const ((n : ℝ) / ((n : ℝ) - 1)) * (1 + D n) - 1

/-- Unadjusted sample standard deviation `σ̂_n = σ √(1 + D n)`. -/
def sigmaHat (n : ℕ) : momAlg μ := const σ * sqrt (1 + D n)

/-- Bessel-corrected sample standard deviation `S_n = σ √(1 + Δ n)`. -/
def S_n (n : ℕ) : momAlg μ := const σ * sqrt (1 + Δ n)

/-- Relative standard deviation fluctuation `δ_sigmaHat n = √(1 + D n) - 1`. -/
def δ_sigmaHat (n : ℕ) : momAlg μ := sqrt (1 + D n) - 1

/-- Relative standard deviation fluctuation `δ_Sn n = √(1 + Δ n) - 1`. -/
def δ_Sn (n : ℕ) : momAlg μ := sqrt (1 + Δ n) - 1

/-- Mean squared error of an estimator `X` of a scalar parameter `θ`: `MSE(X, θ) = E[(X - θ)²]`. -/
def MSE (X : momAlg μ) (θ : ℝ) : ℝ := E ((X - const θ) ^ 2)

/-- Root-n rate `rt n = 1 / √n`. -/
def rt (n : ℕ) : ℝ := 1 / Real.sqrt (n : ℝ)

/-- Bessel factor `cN n = n / (n - 1)`, so that `1 + Δ n = cN n * (1 + D n)`. -/
def cN (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) - 1)

/-- **Moment Rate Hypothesis (CLT order, stated with expectations)**:
    the eighth moments of the centered sample fluctuations `U`, `V`, and `D = U - V²` are of
    the Central Limit Theorem order `E[W_n⁸] = O(n⁻⁴) = O((1/√n)⁸)`.
    These are statements about the real sequences `n ↦ E[W_n⁸]`, not pointwise bounds.
    All higher order Taylor and polynomial remainders are **proved** to be `o(n⁻²)` in
    expectation from this hypothesis via the Cauchy–Schwarz inequality `E_mul_sq_le`. -/
def RemainderOrderHypothesis : Prop :=
  (fun n : ℕ => E (U n ^ 8 : momAlg μ)) =O[atTop] (fun n : ℕ => rt n ^ 8) ∧
  (fun n : ℕ => E (V n ^ 8 : momAlg μ)) =O[atTop] (fun n : ℕ => rt n ^ 8) ∧
  (fun n : ℕ => E (D n ^ 8 : momAlg μ)) =O[atTop] (fun n : ℕ => rt n ^ 8)

/-!
## 3. Basic Algebra, Linearity, and Mathlib Asymptotics (`=O[atTop]`, `=o[atTop]`) Helpers
-/

@[simp]
theorem E_const_mul (c : ℝ) (X : momAlg μ) : E (const c * X) = c * E X := by
  rw [← Algebra.smul_def, E_smul]

@[simp]
theorem E_const (c : ℝ) : E (const c : momAlg μ) = c := by
  have h : (const c : momAlg μ) = const c * 1 := by ring
  rw [h, E_const_mul, E_one, mul_one]

@[simp]
theorem E_invN (n : ℕ) : E (invN n : momAlg μ) = 1 / (n : ℝ) := E_const (1 / (n : ℝ))

@[simp]
theorem E_invN_mul (n : ℕ) (X : momAlg μ) : E (invN n * X) = (1 / (n : ℝ)) * E X := E_const_mul (1 / (n : ℝ)) X

@[simp]
theorem E_two_mul (X : momAlg μ) : E (2 * X) = 2 * E X := by
  have h : (2 : momAlg μ) = const 2 := (map_ofNat (algebraMap ℝ (momAlg μ)) 2).symm
  rw [h, E_const_mul]

@[simp]
theorem E_three_mul (X : momAlg μ) : E (3 * X) = 3 * E X := by
  have h : (3 : momAlg μ) = const 3 := (map_ofNat (algebraMap ℝ (momAlg μ)) 3).symm
  rw [h, E_const_mul]

@[simp]
theorem E_four_mul (X : momAlg μ) : E (4 * X) = 4 * E X := by
  have h : (4 : momAlg μ) = const 4 := (map_ofNat (algebraMap ℝ (momAlg μ)) 4).symm
  rw [h, E_const_mul]

@[simp]
theorem E_six_mul (X : momAlg μ) : E (6 * X) = 6 * E X := by
  have h : (6 : momAlg μ) = const 6 := (map_ofNat (algebraMap ℝ (momAlg μ)) 6).symm
  rw [h, E_const_mul]

theorem E_A2 (n : ℕ) (i : Fin n) : E (((Zm n i) ^ 2 - 1) ^ 2) = lam4 - 1 := by
  have h : ((Zm n i) ^ 2 - 1) ^ 2 = (Zm n i) ^ 4 - 2 * (Zm n i) ^ 2 + 1 := by ring
  rw [h]; simp [E_one]; ring

theorem E_A3 (n : ℕ) (i : Fin n) : E (((Zm n i) ^ 2 - 1) * ((Zm n i) ^ 2 - 1) ^ 2) = lam6 - 3 * lam4 + 2 := by
  have h : ((Zm n i) ^ 2 - 1) * ((Zm n i) ^ 2 - 1) ^ 2 =
      (Zm n i) ^ 6 - 3 * (Zm n i) ^ 4 + 3 * (Zm n i) ^ 2 - 1 := by ring
  rw [h]; simp [E_one]; ring

theorem E_AZ (n : ℕ) (i : Fin n) : E (((Zm n i) ^ 2 - 1) * (Zm n i)) = lam3 := by
  have h : ((Zm n i) ^ 2 - 1) * (Zm n i) = (Zm n i) ^ 3 - (Zm n i) := by ring
  rw [h]; simp

theorem E_AZ2 (n : ℕ) (i : Fin n) : E (((Zm n i) ^ 2 - 1) * (Zm n i) ^ 2) = lam4 - 1 := by
  have h : ((Zm n i) ^ 2 - 1) * (Zm n i) ^ 2 = (Zm n i) ^ 4 - (Zm n i) ^ 2 := by ring
  rw [h]; simp

theorem E_A2Z2 (n : ℕ) (i : Fin n) : E (((Zm n i) ^ 2 - 1) ^ 2 * (Zm n i) ^ 2) = lam6 - 2 * lam4 + 1 := by
  have h : ((Zm n i) ^ 2 - 1) ^ 2 * (Zm n i) ^ 2 =
      (Zm n i) ^ 6 - 2 * (Zm n i) ^ 4 + (Zm n i) ^ 2 := by ring
  rw [h]; simp

theorem E_A4 (n : ℕ) (i : Fin n) : E (((Zm n i) ^ 2 - 1) ^ 2 * ((Zm n i) ^ 2 - 1) ^ 2) = lam8 - 4 * lam6 + 6 * lam4 - 3 := by
  have h : ((Zm n i) ^ 2 - 1) ^ 2 * ((Zm n i) ^ 2 - 1) ^ 2 =
      (Zm n i) ^ 8 - 4 * (Zm n i) ^ 6 + 6 * (Zm n i) ^ 4 - 4 * (Zm n i) ^ 2 + 1 := by ring
  rw [h]; simp [E_one]; ring

/-- Proved 2nd-order pairwise covariance of `Z_obs` from `IsIID.indep`. -/
theorem h_cov2_Z (n : ℕ) (i j : Fin n) :
    E ((Zm n i : momAlg μ) * Zm n j) = if i = j then 1 else 0 := by
  have h := cov2_of_indep (Eraw μ) (indep_E n) id measurable_id 1 (fun i => E_Z1 n i) (fun i => E_Z2 n i) i j
  exact h

/-- Proved 2nd-order pairwise covariance of `A_i = Z_i² - 1` from `IsIID.indep`. -/
theorem h_cov2_U (n : ℕ) (i j : Fin n) :
    E (((Zm n i : momAlg μ) ^ 2 - 1) * (Zm n j ^ 2 - 1)) = if i = j then lam4 - 1 else 0 := by
  have h := cov2_of_indep (Eraw μ) (indep_E n) (fun z => z ^ 2 - 1) (by fun_prop) (lam4 - 1)
    (fun i => by simp only [comp_A]; exact E_A n i)
    (fun i => by simp only [comp_A]; exact E_A2 n i) i j
  simp only [comp_A] at h
  exact h

/-- Proved 3rd-order triple covariance of `A_i = Z_i² - 1` from `IsIID.indep`. -/
theorem h_cov3_UU (n : ℕ) (i j k : Fin n) :
    E (((Zm n i : momAlg μ) ^ 2 - 1) * (Zm n j ^ 2 - 1) * (Zm n k ^ 2 - 1)) =
    if i = j ∧ j = k then lam6 - 3 * lam4 + 2 else 0 := by
  have h := cov3_of_indep (Eraw μ) (indep_E n) (fun z => z ^ 2 - 1) (fun z => z ^ 2 - 1)
    (by fun_prop) (by fun_prop) (lam6 - 3 * lam4 + 2) (fun i => by simp only [comp_A]; exact E_A n i)
    (fun i => by simp only [comp_A]; exact E_A n i)
    (fun i => by simp only [comp_A]; exact E_A3 n i) i j k
  simp only [comp_A] at h
  exact h

/-- Proved 3rd-order mixed covariance of `A_i = Z_i² - 1` and `Z_j, Z_k` from `IsIID.indep`. -/
theorem h_cov3_UV (n : ℕ) (i j k : Fin n) :
    E (((Zm n i : momAlg μ) ^ 2 - 1) * Zm n j * Zm n k) =
    if i = j ∧ j = k then lam4 - 1 else 0 := by
  have h := cov3_of_indep (Eraw μ) (indep_E n) (fun z => z ^ 2 - 1) id
    (by fun_prop) measurable_id (lam4 - 1) (fun i => by simp only [comp_A]; exact E_A n i) (fun i => E_Z1 n i)
    (fun i => by simp only [comp_A]; exact E_AZ2 n i) i j k
  simp only [comp_A] at h
  exact h

/-- Proved 4th-order quadruple sum of `Z_obs` from `IsIID.indep`. -/
theorem h_cov4_VV (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n, ∑ l : Fin n, E ((Zm n i : momAlg μ) * Zm n j * Zm n k * Zm n l)) =
    if i = j then lam4 + ((n : ℝ) - 1) * (1 * 1) else 2 * (1 : ℝ) ^ 2 := by
  have h := cov4_of_indep (Eraw μ) (indep_E n) id id measurable_id measurable_id 1 1 1 lam4
    (fun i => E_Z1 n i) (fun i => E_Z1 n i) (fun i => E_Z2 n i) (fun i => E_Z2 n i)
    (fun idx => by
      change E ((Zm n idx : momAlg μ) * Zm n idx) = 1; rw [← sq]; exact E_Z2 n idx)
    (fun idx => by
      change E ((Zm n idx : momAlg μ) ^ 2 * Zm n idx ^ 2) = lam4; rw [← pow_add]; exact E_Z4 n idx)
    i j
  simp only [Fintype.card_fin] at h
  exact h

/-- Proved 4th-order mixed quadruple sum of `A_i = Z_i² - 1` and `Z_k` from `IsIID.indep`. -/
theorem h_cov4_UV (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n, ∑ l : Fin n, E (((Zm n i : momAlg μ) ^ 2 - 1) * (Zm n j ^ 2 - 1) *
      Zm n k * Zm n l)) =
    if i = j then (lam6 - 2 * lam4 + 1) + ((n : ℝ) - 1) * ((lam4 - 1) * 1) else 2 * lam3 ^ 2 := by
  have h := cov4_of_indep (Eraw μ) (indep_E n) (fun z => z ^ 2 - 1) id
    (by fun_prop) measurable_id (lam4 - 1) 1 lam3 (lam6 - 2 * lam4 + 1)
    (fun i => by simp only [comp_A]; exact E_A n i) (fun i => E_Z1 n i)
    (fun i => by simp only [comp_A]; exact E_A2 n i) (fun i => E_Z2 n i)
    (fun i => by simp only [comp_A]; exact E_AZ n i)
    (fun i => by simp only [comp_A]; exact E_A2Z2 n i)
    i j
  simp only [Fintype.card_fin, comp_A] at h
  exact h

/-- Proved 4th-order quadruple sum of `A_i = Z_i² - 1` from `IsIID.indep`. -/
theorem h_cov4_UU (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n, ∑ l : Fin n, E (((Zm n i : momAlg μ) ^ 2 - 1) * (Zm n j ^ 2 - 1) *
      (Zm n k ^ 2 - 1) * (Zm n l ^ 2 - 1))) =
    if i = j then (lam8 - 4 * lam6 + 6 * lam4 - 3) + ((n : ℝ) - 1) * ((lam4 - 1) * (lam4 - 1))
    else 2 * (lam4 - 1) ^ 2 := by
  have h := cov4_of_indep (Eraw μ) (indep_E n) (fun z => z ^ 2 - 1) (fun z => z ^ 2 - 1)
    (by fun_prop) (by fun_prop) (lam4 - 1) (lam4 - 1) (lam4 - 1) (lam8 - 4 * lam6 + 6 * lam4 - 3)
    (fun i => by simp only [comp_A]; exact E_A n i) (fun i => by simp only [comp_A]; exact E_A n i)
    (fun i => by simp only [comp_A]; exact E_A2 n i) (fun i => by simp only [comp_A]; exact E_A2 n i)
    (fun idx => by
      simp only [comp_A]
      change E (((Zm n idx : momAlg μ) ^ 2 - 1) * (Zm n idx ^ 2 - 1)) = lam4 - 1
      rw [← sq]; exact E_A2 n idx)
    (fun i => by simp only [comp_A]; exact E_A4 n i)
    i j
  simp only [Fintype.card_fin, comp_A] at h
  exact h

/-- Proved Bessel variance identity `(1 - 1/n)(1 + Δ n) = 1 + D n` for `1 < n` from `Δ`. -/
theorem h_Δ (n : ℕ) (hn : 1 < n) : (1 - invN n : momAlg μ) * (1 + Δ n) = 1 + D n := by
  have hn_real : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h_scalar : (1 - const (1 / (n : ℝ)) : momAlg μ) * const ((n : ℝ) / ((n : ℝ) - 1)) = 1 := by
    rw [← map_one (algebraMap ℝ (momAlg μ)), ← map_sub, ← map_mul]
    congr 1
    field_simp
  dsimp [invN, Δ]
  linear_combination (1 + D n) * h_scalar

theorem coe_U_apply (n : ℕ) (ω : Ω) : ((U n : momAlg μ) : Ω → ℝ) ω =
    (1 / (n : ℝ)) * ∑ i : Fin n, ((((Zm n i : momAlg μ) : Ω → ℝ) ω) ^ 2 - 1) := by
  simp [U, sampleAvg, Finset.sum_apply]

theorem coe_V_apply (n : ℕ) (ω : Ω) : ((V n : momAlg μ) : Ω → ℝ) ω =
    (1 / (n : ℝ)) * ∑ i : Fin n, ((Zm n i : momAlg μ) : Ω → ℝ) ω := by
  simp [V, sampleAvg, Finset.sum_apply]

/-- Real identity `1 + (1/n) ∑ (z_i² - 1) - z̄² = (1/n) ∑ (z_i - z̄)² ≥ 0`. -/
theorem sample_var_nonneg {n : ℕ} (z : Fin n → ℝ) :
    0 ≤ 1 + ((1 / (n : ℝ)) * ∑ i, (z i ^ 2 - 1) - ((1 / (n : ℝ)) * ∑ i, z i) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    set v := (1 / (n : ℝ)) * ∑ i, z i with hv
    have hsum : ∑ i, z i = (n : ℝ) * v := by rw [hv]; field_simp
    have h1 : ∑ i, (z i - v) ^ 2 = ∑ i, z i ^ 2 - 2 * v * ∑ i, z i + (n : ℝ) * v ^ 2 := by
      have hpt : ∀ i, (z i - v) ^ 2 = z i ^ 2 - 2 * v * z i + v ^ 2 := fun i => by ring
      simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∑ i, (z i ^ 2 - 1) = ∑ i, z i ^ 2 - (n : ℝ) := by
      simp [Finset.sum_sub_distrib]
    have hid : 1 + ((1 / (n : ℝ)) * ∑ i, (z i ^ 2 - 1) - v ^ 2) =
        (1 / (n : ℝ)) * ∑ i, (z i - v) ^ 2 := by
      rw [h1, h2, hsum]; field_simp; ring
    rw [hid]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Pointwise nonnegativity of `(1 + D n) ω = (1/n) ∑ (Z_i ω - Z̄ ω)² ≥ 0`. -/
theorem one_add_D_nonneg (n : ℕ) (ω : Ω) : 0 ≤ ((1 + D n : momAlg μ) : Ω → ℝ) ω := by
  have h : ((1 + D n : momAlg μ) : Ω → ℝ) ω =
      1 + (((U n : momAlg μ) : Ω → ℝ) ω - (((V n : momAlg μ) : Ω → ℝ) ω) ^ 2) := rfl
  rw [h, coe_U_apply, coe_V_apply]
  exact sample_var_nonneg (fun i => ((Zm n i : momAlg μ) : Ω → ℝ) ω)

theorem n_div_n_sub_one_nonneg (n : ℕ) : 0 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · norm_num
  · rcases eq_or_ne n 1 with rfl | hn1
    · norm_num
    · have hn2 : 2 ≤ n := by omega
      have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact div_nonneg (by linarith) (by linarith)

/-- Pointwise nonnegativity of `(1 + Δ n) ω = (n / (n - 1)) (1 + D n) ω ≥ 0`. -/
theorem one_add_Δ_nonneg (n : ℕ) (ω : Ω) : 0 ≤ ((1 + Δ n : momAlg μ) : Ω → ℝ) ω := by
  have h_eq : ((1 + Δ n : momAlg μ) : Ω → ℝ) ω =
      ((n : ℝ) / ((n : ℝ) - 1)) * ((1 + D n : momAlg μ) : Ω → ℝ) ω := by
    change (1 : ℝ) + (((n : ℝ) / ((n : ℝ) - 1)) * ((1 + D n : momAlg μ) : Ω → ℝ) ω - 1) = _
    ring
  rw [h_eq]
  exact mul_nonneg (n_div_n_sub_one_nonneg n) (one_add_D_nonneg n ω)

theorem sqrt_sq_of_nonneg (X : momAlg μ) (hX : ∀ ω, 0 ≤ (X : Ω → ℝ) ω) : (sqrt X) ^ 2 = X := by
  apply Subtype.ext
  funext ω
  exact Real.sq_sqrt (hX ω)

/-- Proved square-root identity `(1 + δ_sigmaHat n)² = 1 + D n` from `one_add_D_nonneg`. -/
theorem h_sigmaHat_sq (n : ℕ) : (1 + δ_sigmaHat n : momAlg μ) ^ 2 = 1 + D n := by
  have h : (1 : momAlg μ) + δ_sigmaHat n = sqrt (1 + D n) := by dsimp [δ_sigmaHat]; ring
  rw [h, sqrt_sq_of_nonneg (1 + D n) (one_add_D_nonneg n)]

/-- Proved square-root identity `(1 + δ_Sn n)² = 1 + Δ n` from `one_add_Δ_nonneg`. -/
theorem h_Sn_sq (n : ℕ) : (1 + δ_Sn n : momAlg μ) ^ 2 = 1 + Δ n := by
  have h : (1 : momAlg μ) + δ_Sn n = sqrt (1 + Δ n) := by dsimp [δ_Sn]; ring
  rw [h, sqrt_sq_of_nonneg (1 + Δ n) (one_add_Δ_nonneg n)]

theorem sigmaHat_eq (n : ℕ) : (sigmaHat n : momAlg μ) = const σ * (1 + δ_sigmaHat n) := by
  dsimp [sigmaHat, δ_sigmaHat]; ring

theorem S_n_eq (n : ℕ) : (S_n n : momAlg μ) = const σ * (1 + δ_Sn n) := by
  dsimp [S_n, δ_Sn]; ring

/-- `1 / √n = o(1)` as `n → ∞` along `atTop`. -/
theorem inv_sqrt_isLittleO_one :
    (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (Nat.ceil (max 1 ((2 / c) ^ 2)) + 1)] with n hn
  have hn1_real : 1 ≤ (n : ℝ) := by
    have h1 : 1 ≤ Nat.ceil (max 1 ((2 / c) ^ 2)) + 1 := Nat.le_add_left 1 _
    have h2 : (1 : ℝ) ≤ (Nat.ceil (max 1 ((2 / c) ^ 2)) + 1 : ℕ) := by exact_mod_cast h1
    exact le_trans h2 (by exact_mod_cast hn)
  have hnc : (2 / c) ^ 2 ≤ (n : ℝ) := by
    have h1 : (2 / c) ^ 2 ≤ max 1 ((2 / c) ^ 2) := le_max_right _ _
    have h2 : max 1 ((2 / c) ^ 2) ≤ (Nat.ceil (max 1 ((2 / c) ^ 2)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (max 1 ((2 / c) ^ 2)) : ℝ) ≤ (Nat.ceil (max 1 ((2 / c) ^ 2)) + 1 : ℕ) := by
      exact_mod_cast Nat.le_succ _
    have h4 : ((Nat.ceil (max 1 ((2 / c) ^ 2)) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn0 : 0 < (n : ℝ) := by linarith
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq_eq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have h2c_pos : 0 < 2 / c := by positivity
  have h_le_sqrt : 2 / c ≤ Real.sqrt (n : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 2 / c)]
  have h_prod : 2 ≤ c * Real.sqrt (n : ℝ) := by
    have := (div_le_iff₀ hc).mp h_le_sqrt
    linarith
  rw [Real.norm_of_nonneg (by positivity), norm_one, mul_one]
  rw [div_le_iff₀ hsq]
  linarith

/-- `(1 / √n)⁴ = O(1 / n²)` as `n → ∞` along `atTop`. -/
theorem inv_sqrt_pow4_isBigO_inv_n2 :
    (fun n : ℕ => (1 / Real.sqrt (n : ℝ)) ^ 4) =O[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsq_eq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have heq : (1 / Real.sqrt (n : ℝ)) ^ 4 = 1 / (n : ℝ) ^ 2 := by
    calc (1 / Real.sqrt (n : ℝ)) ^ 4 = ((1 / Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
      _ = (1 / (Real.sqrt (n : ℝ) ^ 2)) ^ 2 := by rw [div_pow, one_pow]
      _ = 1 / (n : ℝ) ^ 2 := by rw [hsq_eq]; ring
  rw [heq, one_mul]

/-- `(1 / √n)⁵ = o(1 / n²)` as `n → ∞` along `atTop`. -/
theorem inv_sqrt_pow5_isLittleO_inv_n2 :
    (fun n : ℕ => (1 / Real.sqrt (n : ℝ)) ^ 5) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  have h := inv_sqrt_isLittleO_one.mul_isBigO inv_sqrt_pow4_isBigO_inv_n2
  exact h.congr' (Eventually.of_forall fun n => by ring) (Eventually.of_forall fun n => by ring)

/-- `(1 / n) * (1 / n²) = o(1 / n²)` as `n → ∞` along `atTop`. -/
theorem inv_n_mul_inv_n2_isLittleO :
    (fun n : ℕ => (1 / (n : ℝ)) * (1 / (n : ℝ) ^ 2)) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  have h_inv_n : (fun n : ℕ => 1 / (n : ℝ)) =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    have h2 := inv_sqrt_isLittleO_one.mul_isBigO inv_sqrt_isLittleO_one.isBigO
    refine h2.congr' ?_ (Eventually.of_forall fun _ => one_mul 1)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
    calc (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) = 1 / (Real.sqrt (n : ℝ) ^ 2) := by ring
      _ = 1 / (n : ℝ) := by rw [hsq]
  have h := h_inv_n.mul_isBigO (isBigO_refl (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop)
  exact h.congr' EventuallyEq.rfl (Eventually.of_forall fun n => one_mul _)

/-- `c / n³ = o(1 / n²)` as `n → ∞` along `atTop`. -/
theorem o_div_n3 (c : ℝ) :
    (fun n : ℕ => c / (n : ℝ) ^ 3) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  have h := inv_n_mul_inv_n2_isLittleO.const_mul_left c
  exact h.congr' (Eventually.of_forall fun n => by ring) EventuallyEq.rfl

theorem isLittleO_inv_n2_refl (f : ℕ → ℝ) :
    (fun n : ℕ => f n - f n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  isLittleO_refl_left (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop

theorem isLittleO_inv_n2_of_eq (f g r : ℕ → ℝ) (h : ∀ n, f n - g n = r n)
    (hr : r =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => f n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  hr.congr' (Eventually.of_forall fun n => (h n).symm) EventuallyEq.rfl

theorem isLittleO_inv_n2_of_add (f g r : ℕ → ℝ) (h : ∀ n, f n = g n + r n)
    (hr : r =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => f n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  isLittleO_inv_n2_of_eq f g r (fun n => by linarith [h n]) hr

theorem isLittleO_inv_n2_eq_right {f g h : ℕ → ℝ}
    (hfg : (fun n : ℕ => f n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2))
    (hgh : ∀ n, g n = h n) :
    (fun n : ℕ => f n - h n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  hfg.congr' (Eventually.of_forall fun n => by dsimp; rw [hgh n]) EventuallyEq.rfl

theorem isLittleO_inv_n2_eq_left {f1 f2 g : ℕ → ℝ}
    (h12 : ∀ n, f1 n = f2 n)
    (h : (fun n : ℕ => f1 n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => f2 n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  h.congr' (Eventually.of_forall fun n => by dsimp; rw [h12 n]) EventuallyEq.rfl

theorem isLittleO_inv_n2_add {f1 g1 f2 g2 : ℕ → ℝ}
    (h1 : (fun n : ℕ => f1 n - g1 n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2))
    (h2 : (fun n : ℕ => f2 n - g2 n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => (f1 n + f2 n) - (g1 n + g2 n)) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  (h1.add h2).congr' (Eventually.of_forall fun n => by ring) EventuallyEq.rfl

theorem isLittleO_inv_n2_sub {f1 g1 f2 g2 : ℕ → ℝ}
    (h1 : (fun n : ℕ => f1 n - g1 n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2))
    (h2 : (fun n : ℕ => f2 n - g2 n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => (f1 n - f2 n) - (g1 n - g2 n)) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  (h1.sub h2).congr' (Eventually.of_forall fun n => by ring) EventuallyEq.rfl

theorem isLittleO_inv_n2_smul (c : ℝ) {f g : ℕ → ℝ}
    (h : (fun n : ℕ => f n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => c * f n - c * g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  (h.const_mul_left c).congr' (Eventually.of_forall fun n => by ring) EventuallyEq.rfl

theorem isLittleO_inv_n2_trans {f g h : ℕ → ℝ}
    (h1 : (fun n : ℕ => f n - g n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2))
    (h2 : (fun n : ℕ => g n - h n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => f n - h n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  h1.triangle h2

/-!
### Moment toolkit: monotonicity, Cauchy–Schwarz, and the root-n rate `rt n = 1 / √n`
-/

theorem ev_eq {f g : ℕ → ℝ} (h : ∀ n, f n = g n) : f =ᶠ[atTop] g := Eventually.of_forall h

theorem ev_eq2 {f g : ℕ → ℝ} (h : ∀ n, 2 ≤ n → f n = g n) : f =ᶠ[atTop] g :=
  (eventually_ge_atTop 2).mono h

theorem E_zero : E (0 : momAlg μ) = 0 := E_lm.map_zero

/-- Monotonicity of expectation, from Mathlib's `integral_mono`. -/
theorem E_mono {X Y : momAlg μ} (h : ∀ ω, (X : Ω → ℝ) ω ≤ (Y : Ω → ℝ) ω) : E X ≤ E Y :=
  integral_mono (momAlg_integrable X) (momAlg_integrable Y) h

theorem E_pow_even_nonneg (X : momAlg μ) {j : ℕ} (hj : Even j) : 0 ≤ E (X ^ j) :=
  integral_nonneg fun ω => (show (0 : ℝ) ≤ ((X : Ω → ℝ) ω) ^ j from hj.pow_nonneg _)

/-- **Cauchy–Schwarz inequality** `E[XY]² ≤ E[X²] E[Y²]`, from the nonnegative quadratic
    `t ↦ E[(X + tY)²]` and Mathlib's `discrim_le_zero`. -/
theorem E_mul_sq_le (X Y : momAlg μ) : E (X * Y) ^ 2 ≤ E (X ^ 2) * E (Y ^ 2) := by
  have h : ∀ t : ℝ, 0 ≤ E (Y ^ 2) * (t * t) + 2 * E (X * Y) * t + E (X ^ 2) := by
    intro t
    have h0 := E_pow_even_nonneg (X + const t * Y) even_two
    have heq : (X + const t * Y) ^ 2 =
        X ^ 2 + 2 * (const t * (X * Y)) + const t * (const t * Y ^ 2) := by ring
    rw [heq, E_add, E_add, E_two_mul, E_const_mul, E_const_mul, E_const_mul] at h0
    exact h0.trans_eq (by ring)
  have hd := discrim_le_zero h
  rw [discrim] at hd
  nlinarith [hd]

theorem rt_sq (n : ℕ) : rt n ^ 2 = 1 / (n : ℝ) := by
  rw [rt, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem rt_pow4 (n : ℕ) : rt n ^ 4 = 1 / (n : ℝ) ^ 2 := by
  rw [show rt n ^ 4 = (rt n ^ 2) ^ 2 by ring, rt_sq]; ring

theorem rt_nonneg (n : ℕ) : 0 ≤ rt n := by
  unfold rt; positivity

theorem rt_le_one (n : ℕ) : rt n ≤ 1 := by
  unfold rt
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    rw [div_le_one (by linarith)]
    exact h1

/-- `rt n ^ k = o(n⁻²)` for every `k ≥ 5`. -/
theorem rt_pow_isLittleO {k : ℕ} (hk : 5 ≤ k) :
    (fun n : ℕ => rt n ^ k) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  have h1 : (fun n : ℕ => rt n ^ k) =O[atTop] (fun n : ℕ => rt n ^ 5) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [one_mul, Real.norm_of_nonneg (pow_nonneg (rt_nonneg n) _),
      Real.norm_of_nonneg (pow_nonneg (rt_nonneg n) _)]
    exact pow_le_pow_of_le_one (rt_nonneg n) (rt_le_one n) hk
  exact h1.trans_isLittleO inv_sqrt_pow5_isLittleO_inv_n2

theorem isLittleO_of_rt_pow {f : ℕ → ℝ} {k : ℕ} (hk : 5 ≤ k)
    (h : f =O[atTop] (fun n : ℕ => rt n ^ k)) : f =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  h.trans_isLittleO (rt_pow_isLittleO hk)

/-- A sequence equal to `c / n² + o(n⁻²)` is `O(rt n ^ 4) = O(n⁻²)`. -/
theorem isBigO_rt4_of_asymp {f : ℕ → ℝ} (c : ℝ)
    (h : (fun n : ℕ => f n - c / (n : ℝ) ^ 2) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    f =O[atTop] (fun n : ℕ => rt n ^ 4) := by
  have hc : (fun n : ℕ => c / (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    ((isBigO_refl (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop).const_mul_left c).congr'
      (ev_eq fun n => by ring) EventuallyEq.rfl
  exact (h.isBigO.add hc).congr' (ev_eq fun n => by ring) (ev_eq fun n => (rt_pow4 n).symm)

theorem isBigO_of_nonneg_le {f g r : ℕ → ℝ} (hg : g =O[atTop] r) (hf0 : ∀ n, 0 ≤ f n)
    (hfg : ∀ n, f n ≤ g n) : f =O[atTop] r := by
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)) hg
  rw [one_mul, Real.norm_of_nonneg (hf0 n), Real.norm_of_nonneg ((hf0 n).trans (hfg n))]
  exact hfg n

theorem mom_congr {f g : ℕ → momAlg μ} {k m : ℕ} (hfg : ∀ n, f n = g n) (hkm : k = m)
    (h : (fun n => E (f n)) =O[atTop] (fun n => rt n ^ k)) :
    (fun n => E (g n)) =O[atTop] (fun n => rt n ^ m) := by
  subst hkm
  exact h.congr' (ev_eq fun n => congrArg E (hfg n)) EventuallyEq.rfl

/-- **Asymptotic Cauchy–Schwarz**: if `E[X_n²] = O(rt^(2p))` and `E[Y_n²] = O(rt^(2q))`,
    then `E[X_n Y_n] = O(rt^(p+q))`. -/
theorem isBigO_E_mul {X Y : ℕ → momAlg μ} {p q : ℕ}
    (hX : (fun n => E (X n ^ 2)) =O[atTop] (fun n => rt n ^ (2 * p)))
    (hY : (fun n => E (Y n ^ 2)) =O[atTop] (fun n => rt n ^ (2 * q))) :
    (fun n => E (X n * Y n)) =O[atTop] (fun n => rt n ^ (p + q)) := by
  have hprod : (fun n => E (X n ^ 2) * E (Y n ^ 2)) =O[atTop] (fun n => (rt n ^ (p + q)) ^ 2) :=
    (hX.mul hY).congr' EventuallyEq.rfl (ev_eq fun n => by ring)
  have hsq : (fun n => E (X n * Y n) ^ 2) =O[atTop] (fun n => (rt n ^ (p + q)) ^ 2) := by
    refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)) hprod
    have h1 := E_pow_even_nonneg (X n) even_two
    have h2 := E_pow_even_nonneg (Y n) even_two
    rw [one_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (mul_nonneg h1 h2)]
    exact E_mul_sq_le (X n) (Y n)
  exact IsBigO.of_pow (f := fun n => E (X n * Y n)) (g := fun n => rt n ^ (p + q))
    two_ne_zero hsq

/-- Cauchy–Schwarz for monomials `E[W₁^a W₂^b]` from the even moments `E[W₁^(2a)]`, `E[W₂^(2b)]`. -/
theorem cs_pow {W₁ W₂ : ℕ → momAlg μ} (a b p q : ℕ)
    (h₁ : (fun n => E (W₁ n ^ (2 * a))) =O[atTop] (fun n => rt n ^ (2 * p)))
    (h₂ : (fun n => E (W₂ n ^ (2 * b))) =O[atTop] (fun n => rt n ^ (2 * q))) :
    (fun n => E (W₁ n ^ a * W₂ n ^ b)) =O[atTop] (fun n => rt n ^ (p + q)) :=
  isBigO_E_mul (X := fun n => W₁ n ^ a) (Y := fun n => W₂ n ^ b)
    (mom_congr (fun n => by beta_reduce; ring) rfl h₁)
    (mom_congr (fun n => by beta_reduce; ring) rfl h₂)

theorem pow_even_le_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) {j : ℕ} (hj : Even j) :
    a ^ j ≤ b ^ j := by
  rw [← hj.pow_abs a, ← hj.pow_abs b]
  exact pow_le_pow_left₀ (abs_nonneg a) h j

/-- Pointwise domination `|δ| ≤ |x|` transfers even moment rates from `x` to `δ`. -/
theorem isBigO_mom_of_abs_le {δ x : ℕ → momAlg μ}
    (h : ∀ n ω, |(δ n : Ω → ℝ) ω| ≤ |(x n : Ω → ℝ) ω|) {j m : ℕ}
    (hj : Even j) (hx : (fun n => E (x n ^ j)) =O[atTop] (fun n => rt n ^ m)) :
    (fun n => E (δ n ^ j)) =O[atTop] (fun n => rt n ^ m) :=
  isBigO_of_nonneg_le hx (fun n => E_pow_even_nonneg (δ n) hj)
    (fun n => E_mono fun ω => by
      show ((δ n : Ω → ℝ) ω) ^ j ≤ ((x n : Ω → ℝ) ω) ^ j
      exact pow_even_le_of_abs_le (h n ω) hj)

/-- `|√(1 + x) - 1| ≤ |x|` whenever `1 + x ≥ 0`. -/
theorem abs_sqrt_one_add_sub_one_le {x : ℝ} (hx : 0 ≤ 1 + x) :
    |Real.sqrt (1 + x) - 1| ≤ |x| := by
  have hs := Real.sqrt_nonneg (1 + x)
  have hsq := Real.sq_sqrt hx
  have h1 : |Real.sqrt (1 + x) - 1| * (Real.sqrt (1 + x) + 1) = |x| := by
    rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt (1 + x) + 1), ← abs_mul]
    congr 1
    linear_combination hsq
  rw [mul_add, mul_one] at h1
  linarith [mul_nonneg (abs_nonneg (Real.sqrt (1 + x) - 1)) hs]

theorem abs_δ_sigmaHat_le (n : ℕ) (ω : Ω) :
    |((δ_sigmaHat n : momAlg μ) : Ω → ℝ) ω| ≤ |((D n : momAlg μ) : Ω → ℝ) ω| := by
  have h := abs_sqrt_one_add_sub_one_le (x := ((D n : momAlg μ) : Ω → ℝ) ω) (one_add_D_nonneg n ω)
  exact h

theorem abs_δ_Sn_le (n : ℕ) (ω : Ω) :
    |((δ_Sn n : momAlg μ) : Ω → ℝ) ω| ≤ |((Δ n : momAlg μ) : Ω → ℝ) ω| := by
  have h := abs_sqrt_one_add_sub_one_le (x := ((Δ n : momAlg μ) : Ω → ℝ) ω) (one_add_Δ_nonneg n ω)
  exact h

/-- `(x + y)⁸ ≤ 128 (x⁸ + y⁸)`, by three applications of `(a + b)² ≤ 2 (a² + b²)`. -/
theorem add_pow_eight_le (x y : ℝ) : (x + y) ^ 8 ≤ 128 * (x ^ 8 + y ^ 8) := by
  have h2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have s1 : (x + y) ^ 8 ≤ (2 * (x ^ 2 + y ^ 2)) ^ 4 := by
    rw [show (x + y) ^ 8 = ((x + y) ^ 2) ^ 4 by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) (h2 x y) 4
  have s4 : (x ^ 2 + y ^ 2) ^ 4 ≤ (2 * ((x ^ 2) ^ 2 + (y ^ 2) ^ 2)) ^ 2 := by
    rw [show (x ^ 2 + y ^ 2) ^ 4 = ((x ^ 2 + y ^ 2) ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) (h2 _ _) 2
  have s3 := h2 ((x ^ 2) ^ 2) ((y ^ 2) ^ 2)
  calc (x + y) ^ 8 ≤ (2 * (x ^ 2 + y ^ 2)) ^ 4 := s1
    _ = 16 * (x ^ 2 + y ^ 2) ^ 4 := by ring
    _ ≤ 16 * (2 * ((x ^ 2) ^ 2 + (y ^ 2) ^ 2)) ^ 2 := by linarith [s4]
    _ = 64 * ((x ^ 2) ^ 2 + (y ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ 64 * (2 * (((x ^ 2) ^ 2) ^ 2 + ((y ^ 2) ^ 2) ^ 2)) := by linarith [s3]
    _ = 128 * (x ^ 8 + y ^ 8) := by ring

theorem tendsto_cN : Tendsto cN atTop (𝓝 1) := by
  have h := tendsto_natCast_div_add_atTop (-1 : ℝ)
  refine h.congr (fun n => ?_)
  unfold cN; rw [sub_eq_add_neg]

/-- Any continuous function of `(cN n, 1/n)` is bounded along `atTop`. -/
theorem bdd_cu (F : ℝ → ℝ → ℝ) (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    (fun n : ℕ => F (cN n) (1 / (n : ℝ))) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (cN n, 1 / (n : ℝ))) atTop (𝓝 (1, 0)) :=
    tendsto_cN.prodMk_nhds tendsto_one_div_atTop_nhds_zero_nat
  exact ((hF.tendsto (1, 0)).comp h).isBigO_one ℝ

theorem o_of_bdd_div_n3 {B : ℕ → ℝ} (hB : B =O[atTop] (fun _ : ℕ => (1 : ℝ))) :
    (fun n : ℕ => B n / (n : ℝ) ^ 3) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  (hB.mul_isLittleO inv_n_mul_inv_n2_isLittleO).congr' (ev_eq fun n => by ring)
    (ev_eq fun n => one_mul _)

theorem o_of_bdd_mul {B r : ℕ → ℝ} (hB : B =O[atTop] (fun _ : ℕ => (1 : ℝ)))
    (hr : r =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :
    (fun n : ℕ => B n * r n) =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  (hB.mul_isLittleO hr).congr' EventuallyEq.rfl (ev_eq fun n => one_mul _)

/-!
## 4. Proving the Taylor and Polynomial Remainder Theorems from the Definitions
-/

/-- **Exact 4th-order Taylor theorem `taylorSqrt4`**:
    For any `δ, x : momAlg μ` satisfying `(1 + δ)² = 1 + x`, we **prove** that the remainder after the
    4th-order Taylor polynomial `1 + (1/2)x - (1/8)x² + (1/16)x³ - (5/128)x⁴` factors as `P * δ⁵`
    for the explicit polynomial `P = 7/8 + (7/8)δ + (5/16)δ² + (5/128)δ³`. -/
theorem taylorSqrt4 (δ x : momAlg μ) (h_sq : (1 + δ) ^ 2 = 1 + x) :
    1 + δ - (1 + const (1 / 2) * x - const (1 / 8) * x ^ 2 +
      const (1 / 16) * x ^ 3 - const (5 / 128) * x ^ 4) =
    (const (7 / 8) + const (7 / 8) * δ + const (5 / 16) * δ ^ 2 + const (5 / 128) * δ ^ 3) *
      δ ^ 5 := by
  have h1 : 128 * (const (1 / 128) : momAlg μ) = 1 := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 128, ← map_mul]; norm_num
  have h2 : (const (1 / 2) : momAlg μ) = 64 * const (1 / 128) := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 64, ← map_mul]; norm_num
  have h8 : (const (1 / 8) : momAlg μ) = 16 * const (1 / 128) := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 16, ← map_mul]; norm_num
  have h7_8 : (const (7 / 8) : momAlg μ) = 112 * const (1 / 128) := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 112, ← map_mul]; norm_num
  have h16 : (const (1 / 16) : momAlg μ) = 8 * const (1 / 128) := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 8, ← map_mul]; norm_num
  have h5_16 : (const (5 / 16) : momAlg μ) = 40 * const (1 / 128) := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 40, ← map_mul]; norm_num
  have h128 : (const (5 / 128) : momAlg μ) = 5 * const (1 / 128) := by
    rw [← map_ofNat (algebraMap ℝ (momAlg μ)) 5, ← map_mul]; norm_num
  rw [h2, h8, h7_8, h16, h5_16, h128]
  linear_combination
    const (1 / 128) *
      (64 - 16 * (x + 2 * δ + δ ^ 2) +
       8 * (x ^ 2 + x * (2 * δ + δ ^ 2) + (2 * δ + δ ^ 2) ^ 2) -
       5 * (x ^ 3 + x ^ 2 * (2 * δ + δ ^ 2) +
         x * (2 * δ + δ ^ 2) ^ 2 + (2 * δ + δ ^ 2) ^ 3)) * h_sq -
    δ * h1

/-- **Taylor remainder in expectation**: if `(1 + δ)² = 1 + x`, `|δ| ≤ |x|` pointwise, and
    `E[x⁴] = O(n⁻²)`, `E[x⁸] = O(n⁻⁴)`, then the expected 4th-order Taylor remainder is `o(n⁻²)`. -/
theorem taylor_remainder_E_small (δ x : ℕ → momAlg μ) (h_sq : ∀ n, (1 + δ n) ^ 2 = 1 + x n)
    (hδx : ∀ n ω, |(δ n : Ω → ℝ) ω| ≤ |(x n : Ω → ℝ) ω|)
    (hx4 : (fun n => E (x n ^ 4)) =O[atTop] (fun n => rt n ^ 4))
    (hx8 : (fun n => E (x n ^ 8)) =O[atTop] (fun n => rt n ^ 8)) :
    (fun n => E (1 + δ n) - E (1 + const (1 / 2) * x n - const (1 / 8) * x n ^ 2 +
        const (1 / 16) * x n ^ 3 - const (5 / 128) * x n ^ 4))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hδ4 : (fun n => E (δ n ^ 4)) =O[atTop] (fun n => rt n ^ 4) :=
    isBigO_mom_of_abs_le hδx ⟨2, rfl⟩ hx4
  have hδ8 : (fun n => E (δ n ^ 8)) =O[atTop] (fun n => rt n ^ 8) :=
    isBigO_mom_of_abs_le hδx ⟨4, rfl⟩ hx8
  have hδ6 : (fun n => E (δ n ^ 6)) =O[atTop] (fun n => rt n ^ 6) :=
    mom_congr (fun n => by ring) rfl (cs_pow (W₁ := δ) (W₂ := δ) 2 4 2 4 hδ4 hδ8)
  have hδ5 : (fun n => E (δ n ^ 5)) =O[atTop] (fun n => rt n ^ 5) :=
    mom_congr (fun n => by ring) rfl (cs_pow (W₁ := δ) (W₂ := δ) 2 3 2 3 hδ4 hδ6)
  have hδ7 : (fun n => E (δ n ^ 7)) =O[atTop] (fun n => rt n ^ 7) :=
    mom_congr (fun n => by ring) rfl (cs_pow (W₁ := δ) (W₂ := δ) 3 4 3 4 hδ6 hδ8)
  have key : ∀ n, E (1 + δ n) - E (1 + const (1 / 2) * x n - const (1 / 8) * x n ^ 2 +
        const (1 / 16) * x n ^ 3 - const (5 / 128) * x n ^ 4) =
      7 / 8 * E (δ n ^ 5) + 7 / 8 * E (δ n ^ 6) + 5 / 16 * E (δ n ^ 7) +
        5 / 128 * E (δ n ^ 8) := by
    intro n
    rw [← E_sub, taylorSqrt4 (δ n) (x n) (h_sq n)]
    have hexp : (const (7 / 8) + const (7 / 8) * δ n + const (5 / 16) * δ n ^ 2 +
        const (5 / 128) * δ n ^ 3) * δ n ^ 5 = const (7 / 8) * δ n ^ 5 +
        const (7 / 8) * δ n ^ 6 + const (5 / 16) * δ n ^ 7 + const (5 / 128) * δ n ^ 8 := by
      ring
    rw [hexp, E_add, E_add, E_add, E_const_mul, E_const_mul, E_const_mul, E_const_mul]
  have hsum := ((((isLittleO_of_rt_pow (by norm_num) hδ5).const_mul_left (7 / 8)).add
      ((isLittleO_of_rt_pow (by norm_num) hδ6).const_mul_left (7 / 8))).add
      ((isLittleO_of_rt_pow (by norm_num) hδ7).const_mul_left (5 / 16))).add
      ((isLittleO_of_rt_pow (by norm_num) hδ8).const_mul_left (5 / 128))
  exact hsum.congr' (ev_eq fun n => (key n).symm) EventuallyEq.rfl

/-!
## 5. Sample Mean Moments and Second-Order Moments of `D` and `Δ` up to `o(n⁻²)`
-/

/-- Moments of `U` and `V` derived from `sampleAvg_moment1`..`sampleAvg_moment4` and Mathlib's `c / n³ = o(1 / n²)`. -/
theorem sample_mean_moments :
    (∀ n, E (U n) = 0) ∧
    (∀ n, E (U n ^ 2) = (lam4 - 1) / (n : ℝ)) ∧
    (∀ n, E (V n ^ 2) = 1 / (n : ℝ)) ∧
    (∀ n, E (U n ^ 3) = (lam6 - 3 * lam4 + 2) / (n : ℝ) ^ 2) ∧
    (∀ n, E (U n * V n ^ 2) = (lam4 - 1) / (n : ℝ) ^ 2) ∧
    (fun n => E (V n ^ 4) - 3 / (n : ℝ) ^ 2) =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (U n ^ 2 * V n ^ 2) - (lam4 - 1 + 2 * lam3 ^ 2) / (n : ℝ) ^ 2) =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (U n ^ 4) - 3 * (lam4 - 1) ^ 2 / (n : ℝ) ^ 2) =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  refine ⟨fun n => by
            change E_lm (sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1)) = 0
            exact sampleAvg_moment1 E_lm _ (fun i => E_A n i),
          fun n => by
            change E_lm (sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) ^ 2) = (lam4 - 1) / (n : ℝ)
            have h := sampleAvg_moment2 E_lm (fun i : Fin n => Zm n i ^ 2 - 1) (lam4 - 1) (h_cov2_U n)
            simp only [Fintype.card_fin] at h
            exact h,
          fun n => by
            change E_lm (sampleAvg (Zm n) ^ 2) = 1 / (n : ℝ)
            have h := sampleAvg_moment2 E_lm (Zm n) 1 (h_cov2_Z n)
            simp only [Fintype.card_fin] at h
            exact h,
          fun n => by
            have h3 : (U n : momAlg μ) ^ 3 = U n * U n ^ 2 := by ring
            rw [h3]
            change E_lm (sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) *
                         sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) ^ 2) =
                   (lam6 - 3 * lam4 + 2) / (n : ℝ) ^ 2
            have h := sampleAvg_moment3 E_lm
              (fun i : Fin n => Zm n i ^ 2 - 1)
              (fun i : Fin n => Zm n i ^ 2 - 1)
              (lam6 - 3 * lam4 + 2)
              (h_cov3_UU n)
            simp only [Fintype.card_fin] at h
            exact h,
          fun n => by
            change E_lm (sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) *
                         sampleAvg (Zm n) ^ 2) =
                   (lam4 - 1) / (n : ℝ) ^ 2
            have h := sampleAvg_moment3 E_lm
              (fun i : Fin n => Zm n i ^ 2 - 1)
              (Zm n)
              (lam4 - 1)
              (h_cov3_UV n)
            simp only [Fintype.card_fin] at h
            exact h,
          ?_, ?_, ?_⟩
  · have hE : ∀ n : ℕ, E (V n ^ 4) = 3 / (n : ℝ) ^ 2 + (lam4 - 3) / (n : ℝ) ^ 3 := by
      intro n
      have h4 : (V n : momAlg μ) ^ 4 = V n ^ 2 * V n ^ 2 := by ring
      rw [h4]
      change E_lm (sampleAvg (Zm n) ^ 2 * sampleAvg (Zm n) ^ 2) = _
      have h_cov4' : ∀ i j : Fin n,
          (∑ k : Fin n, ∑ l : Fin n, E_lm (Zm n i * Zm n j *
            Zm n k * Zm n l)) =
          if i = j then lam4 + ((Fintype.card (Fin n) : ℝ) - 1) * (1 * 1)
          else 2 * (1 : ℝ) ^ 2 := by
        intro i j
        have := h_cov4_VV (Ω := Ω) n i j
        simp only [Fintype.card_fin]
        exact this
      have h := sampleAvg_moment4 E_lm (Zm n) (Zm n) 1 1 1 lam4 h_cov4'
      simp only [Fintype.card_fin] at h
      rw [h]
      ring
    exact isLittleO_inv_n2_of_add (fun n => E (V n ^ 4)) (fun n => 3 / (n : ℝ) ^ 2)
      (fun n => (lam4 - 3) / (n : ℝ) ^ 3) hE (o_div_n3 (lam4 - 3))
  · have hE : ∀ n : ℕ, E (U n ^ 2 * V n ^ 2) =
        (lam4 - 1 + 2 * lam3 ^ 2) / (n : ℝ) ^ 2 +
        (lam6 - 2 * lam4 + 1 - (lam4 - 1) - 2 * lam3 ^ 2) / (n : ℝ) ^ 3 := by
      intro n
      change E_lm (sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) ^ 2 *
                   sampleAvg (Zm n) ^ 2) = _
      have h_cov4' : ∀ i j : Fin n,
          (∑ k : Fin n, ∑ l : Fin n, E_lm (((Zm n i) ^ 2 - 1) *
            ((Zm n j) ^ 2 - 1) *
            Zm n k * Zm n l)) =
          if i = j then (lam6 - 2 * lam4 + 1) + ((Fintype.card (Fin n) : ℝ) - 1) * ((lam4 - 1) * 1)
          else 2 * lam3 ^ 2 := by
        intro i j
        have := h_cov4_UV (Ω := Ω) n i j
        simp only [Fintype.card_fin]
        exact this
      have h := sampleAvg_moment4 E_lm
        (fun i : Fin n => Zm n i ^ 2 - 1)
        (Zm n)
        (lam4 - 1) 1 lam3 (lam6 - 2 * lam4 + 1) h_cov4'
      simp only [Fintype.card_fin] at h
      rw [h]
      ring
    exact isLittleO_inv_n2_of_add _ _ _ hE (o_div_n3 _)
  · have hE : ∀ n : ℕ, E (U n ^ 4) =
        3 * (lam4 - 1) ^ 2 / (n : ℝ) ^ 2 +
        ((lam8 - 4 * lam6 + 6 * lam4 - 3) - (lam4 - 1) ^ 2 - 2 * (lam4 - 1) ^ 2) / (n : ℝ) ^ 3 := by
      intro n
      have h4 : (U n : momAlg μ) ^ 4 = U n ^ 2 * U n ^ 2 := by ring
      rw [h4]
      change E_lm (sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) ^ 2 *
                   sampleAvg (fun i : Fin n => Zm n i ^ 2 - 1) ^ 2) = _
      have h_cov4' : ∀ i j : Fin n,
          (∑ k : Fin n, ∑ l : Fin n, E_lm (((Zm n i) ^ 2 - 1) *
            ((Zm n j) ^ 2 - 1) *
            ((Zm n k) ^ 2 - 1) *
            ((Zm n l) ^ 2 - 1))) =
          if i = j then (lam8 - 4 * lam6 + 6 * lam4 - 3) + ((Fintype.card (Fin n) : ℝ) - 1) * ((lam4 - 1) * (lam4 - 1))
          else 2 * (lam4 - 1) ^ 2 := by
        intro i j
        have := h_cov4_UU (Ω := Ω) n i j
        simp only [Fintype.card_fin]
        exact this
      have h := sampleAvg_moment4 E_lm
        (fun i : Fin n => Zm n i ^ 2 - 1)
        (fun i : Fin n => Zm n i ^ 2 - 1)
        (lam4 - 1) (lam4 - 1) (lam4 - 1) (lam8 - 4 * lam6 + 6 * lam4 - 3) h_cov4'
      simp only [Fintype.card_fin] at h
      rw [h]
      ring
    exact isLittleO_inv_n2_of_add _ _ _ hE (o_div_n3 _)

/-- Second-order moments `E[D^k]` and `E[Δ^k]` (`k = 1..4`) up to `o(n⁻²)`. -/
theorem derived_moments (h_rem : RemainderOrderHypothesis) :
    (∀ n, E (D n) = -1 / (n : ℝ)) ∧
    (fun n => E (D n ^ 2) - ((lam4 - 1) / (n : ℝ) - 2 * (lam4 - 1) / (n : ℝ) ^ 2 + 3 / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (D n ^ 3) - ((lam6 - 6 * lam4 - 6 * lam3 ^ 2 + 5) / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (D n ^ 4) - (3 * (lam4 - 1) ^ 2 / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (Δ n) - 0) =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (Δ n ^ 2) - ((lam4 - 1) / (n : ℝ) + 2 / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (Δ n ^ 3) - ((lam6 - 3 * lam4 - 6 * lam3 ^ 2 + 2) / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) ∧
    (fun n => E (Δ n ^ 4) - (3 * (lam4 - 1) ^ 2 / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  rcases sample_mean_moments (Ω := Ω) with
    ⟨hU1, hU2, hV2, hU3, hUV2, hV4, hU2V2, hU4⟩
  rcases h_rem with ⟨hU8, hV8, _⟩
  -- Moment rates of `U` and `V`.
  have hU2b : (fun n => E (U n ^ 2 : momAlg μ)) =O[atTop] (fun n => rt n ^ 2) :=
    ((isBigO_refl (fun n : ℕ => rt n ^ 2) atTop).const_mul_left (lam4 - 1)).congr'
      (ev_eq fun n => by rw [hU2 n, rt_sq]; ring) EventuallyEq.rfl
  have hU4b : (fun n => E (U n ^ 4 : momAlg μ)) =O[atTop] (fun n => rt n ^ 4) :=
    isBigO_rt4_of_asymp _ hU4
  have hV4b : (fun n => E (V n ^ 4 : momAlg μ)) =O[atTop] (fun n => rt n ^ 4) :=
    isBigO_rt4_of_asymp _ hV4
  have hU6b : (fun n => E (U n ^ 6 : momAlg μ)) =O[atTop] (fun n => rt n ^ 6) :=
    mom_congr (fun n => by ring) rfl (cs_pow (W₁ := U) (W₂ := U) 2 4 2 4 hU4b hU8)
  have hV6b : (fun n => E (V n ^ 6 : momAlg μ)) =O[atTop] (fun n => rt n ^ 6) :=
    mom_congr (fun n => by ring) rfl (cs_pow (W₁ := V) (W₂ := V) 2 4 2 4 hV4b hV8)
  -- Mixed monomials of degree at least 5, bounded by Cauchy–Schwarz.
  have hUV4 : (fun n => E (U n ^ 1 * V n ^ 4 : momAlg μ)) =O[atTop] (fun n => rt n ^ 5) :=
    cs_pow 1 4 1 4 hU2b hV8
  have hU3V2 : (fun n => E (U n ^ 3 * V n ^ 2 : momAlg μ)) =O[atTop] (fun n => rt n ^ 5) :=
    cs_pow 3 2 3 2 hU6b hV4b
  have hU2V4 : (fun n => E (U n ^ 2 * V n ^ 4 : momAlg μ)) =O[atTop] (fun n => rt n ^ 6) :=
    cs_pow 2 4 2 4 hU4b hV8
  have hUV6 : (fun n => E (U n * V n ^ 6 : momAlg μ)) =O[atTop] (fun n => rt n ^ 7) :=
    mom_congr (fun n => by beta_reduce; ring) rfl
      (isBigO_E_mul (X := fun n => U n * V n ^ 2) (Y := fun n => V n ^ 4) (p := 3) (q := 4)
        (mom_congr (fun n => by beta_reduce; ring) rfl hU2V4)
        (mom_congr (fun n => by beta_reduce; ring) rfl hV8))
  -- Moments of `D = U - V²`.
  have hD2_eq : ∀ n, (D n : momAlg μ) ^ 2 = U n ^ 2 - 2 * (U n * V n ^ 2) + V n ^ 4 :=
    fun n => by unfold D; ring
  have hED1 : ∀ n : ℕ, E (D n : momAlg μ) = -1 / (n : ℝ) := by
    intro n; dsimp [D]; simp [hU1 n, hV2 n]; ring
  have hED2 : (fun n => E ((D n : momAlg μ) ^ 2) -
      ((lam4 - 1) / (n : ℝ) - 2 * (lam4 - 1) / (n : ℝ) ^ 2 + 3 / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
    have heq : ∀ n : ℕ, (lam4 - 1) / (n : ℝ) - 2 * ((lam4 - 1) / (n : ℝ) ^ 2) + E (V n ^ 4) =
        E ((D n : momAlg μ) ^ 2) := by
      intro n; rw [hD2_eq n, E_add, E_sub, E_two_mul, hU2 n, hUV2 n]
    have h_step := isLittleO_inv_n2_add
      (isLittleO_inv_n2_refl (fun n => (lam4 - 1) / (n : ℝ) - 2 * ((lam4 - 1) / (n : ℝ) ^ 2))) hV4
    exact isLittleO_inv_n2_eq_left heq (isLittleO_inv_n2_eq_right h_step (fun n => by ring))
  have hD3_eq : ∀ n, E (D n ^ 3 : momAlg μ) = E (U n ^ 3) - 3 * E (U n ^ 2 * V n ^ 2) +
      3 * E (U n ^ 1 * V n ^ 4) - E (V n ^ 6) := by
    intro n
    have h : (D n : momAlg μ) ^ 3 =
        U n ^ 3 - 3 * (U n ^ 2 * V n ^ 2) + 3 * (U n ^ 1 * V n ^ 4) - V n ^ 6 := by
      unfold D; ring
    rw [h, E_sub, E_add, E_sub, E_three_mul, E_three_mul]
  have hED3 : (fun n => E ((D n : momAlg μ) ^ 3) -
      ((lam6 - 6 * lam4 - 6 * lam3 ^ 2 + 5) / (n : ℝ) ^ 2))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
    have h := ((hU2V2.const_mul_left (-3)).add
      ((isLittleO_of_rt_pow (by norm_num) hUV4).const_mul_left 3)).sub
      (isLittleO_of_rt_pow (by norm_num) hV6b)
    exact h.congr' (ev_eq fun n => by rw [hD3_eq n, hU3 n]; ring) EventuallyEq.rfl
  have hD4_eq : ∀ n, E (D n ^ 4 : momAlg μ) = E (U n ^ 4) - 4 * E (U n ^ 3 * V n ^ 2) +
      6 * E (U n ^ 2 * V n ^ 4) - 4 * E (U n * V n ^ 6) + E (V n ^ 8) := by
    intro n
    have h : (D n : momAlg μ) ^ 4 = U n ^ 4 - 4 * (U n ^ 3 * V n ^ 2) +
        6 * (U n ^ 2 * V n ^ 4) - 4 * (U n * V n ^ 6) + V n ^ 8 := by
      unfold D; ring
    rw [h, E_add, E_sub, E_add, E_sub, E_four_mul, E_six_mul, E_four_mul]
  have hED4 : (fun n : ℕ => E ((D n : momAlg μ) ^ 4) -
      (3 * (lam4 - 1) ^ 2 / (n : ℝ) ^ 2))
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    have h := (((hU4.sub ((isLittleO_of_rt_pow (by norm_num) hU3V2).const_mul_left 4)).add
      ((isLittleO_of_rt_pow (by norm_num) hU2V4).const_mul_left 6)).sub
      ((isLittleO_of_rt_pow (by norm_num) hUV6).const_mul_left 4)).add
      (isLittleO_of_rt_pow (by norm_num) hV8)
    exact h.congr' (ev_eq fun n => by rw [hD4_eq n]; ring) EventuallyEq.rfl
  -- Exact moments of `Δ = (cN - 1) + cN D` in terms of the moments of `D`.
  have hEΔ1 : ∀ n, E (Δ n : momAlg μ) = cN n * (1 + E (D n)) - 1 := by
    intro n
    rw [show (Δ n : momAlg μ) = const (cN n) * (1 + D n) - 1 from rfl, E_sub, E_const_mul,
      E_add, E_one]
  have hEΔ2 : ∀ n, E (Δ n ^ 2 : momAlg μ) =
      (cN n - 1) ^ 2 + 2 * (cN n - 1) * cN n * E (D n) + cN n ^ 2 * E (D n ^ 2) := by
    intro n
    have hid : (Δ n : momAlg μ) ^ 2 = const ((cN n - 1) ^ 2) +
        const (2 * (cN n - 1) * cN n) * D n + const (cN n ^ 2) * D n ^ 2 := by
      simp only [Δ, cN, const, map_sub, map_mul, map_pow, map_one, map_ofNat]; ring
    rw [hid, E_add, E_add, E_const, E_const_mul, E_const_mul]
  have hEΔ3 : ∀ n, E (Δ n ^ 3 : momAlg μ) =
      (cN n - 1) ^ 3 + 3 * (cN n - 1) ^ 2 * cN n * E (D n) +
        3 * (cN n - 1) * cN n ^ 2 * E (D n ^ 2) + cN n ^ 3 * E (D n ^ 3) := by
    intro n
    have hid : (Δ n : momAlg μ) ^ 3 = const ((cN n - 1) ^ 3) +
        const (3 * (cN n - 1) ^ 2 * cN n) * D n + const (3 * (cN n - 1) * cN n ^ 2) * D n ^ 2 +
        const (cN n ^ 3) * D n ^ 3 := by
      simp only [Δ, cN, const, map_sub, map_mul, map_pow, map_one, map_ofNat]; ring
    rw [hid, E_add, E_add, E_add, E_const, E_const_mul, E_const_mul, E_const_mul]
  have hEΔ4 : ∀ n, E (Δ n ^ 4 : momAlg μ) =
      (cN n - 1) ^ 4 + 4 * (cN n - 1) ^ 3 * cN n * E (D n) +
        6 * (cN n - 1) ^ 2 * cN n ^ 2 * E (D n ^ 2) + 4 * (cN n - 1) * cN n ^ 3 * E (D n ^ 3) +
        cN n ^ 4 * E (D n ^ 4) := by
    intro n
    have hid : (Δ n : momAlg μ) ^ 4 = const ((cN n - 1) ^ 4) +
        const (4 * (cN n - 1) ^ 3 * cN n) * D n +
        const (6 * (cN n - 1) ^ 2 * cN n ^ 2) * D n ^ 2 +
        const (4 * (cN n - 1) * cN n ^ 3) * D n ^ 3 + const (cN n ^ 4) * D n ^ 4 := by
      simp only [Δ, cN, const, map_sub, map_mul, map_pow, map_one, map_ofNat]; ring
    rw [hid, E_add, E_add, E_add, E_add, E_const, E_const_mul, E_const_mul, E_const_mul,
      E_const_mul]
  refine ⟨hED1, hED2, hED3, hED4, ?_, ?_, ?_, ?_⟩
  · refine (isLittleO_zero _ _).congr' (ev_eq2 fun n hn => ?_) EventuallyEq.rfl
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [hEΔ1 n, hED1 n]
    simp only [cN]
    field_simp
    ring
  · have h1 := o_of_bdd_mul (bdd_cu (fun c _ => c ^ 2) (by fun_prop)) hED2
    have h2 := o_of_bdd_div_n3 (bdd_cu (fun c u => c ^ 2 * (5 - lam4 - 2 * u)) (by fun_prop))
    refine (h1.add h2).congr' (ev_eq2 fun n hn => ?_) EventuallyEq.rfl
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [hEΔ2 n, hED1 n]
    simp only [cN]
    field_simp
    ring
  · have h1 := (o_of_bdd_mul (bdd_cu (fun c _ => 3 * (c - 1) * c ^ 2) (by fun_prop)) hED2).add
      (o_of_bdd_mul (bdd_cu (fun c _ => c ^ 3) (by fun_prop)) hED3)
    have h2 := o_of_bdd_div_n3 (bdd_cu (fun c u => c ^ 3 *
      (3 * lam6 - 15 * lam4 - 18 * lam3 ^ 2 + 19 + u * (-3 * lam6 + 9 * lam4 + 18 * lam3 ^ 2 - 6) +
        u ^ 2 * (lam6 - 3 * lam4 - 6 * lam3 ^ 2 + 2))) (by fun_prop))
    refine (h1.add h2).congr' (ev_eq2 fun n hn => ?_) EventuallyEq.rfl
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [hEΔ3 n, hED1 n]
    simp only [cN]
    field_simp
    ring
  · have h1 := ((o_of_bdd_mul (bdd_cu (fun c _ => 6 * (c - 1) ^ 2 * c ^ 2) (by fun_prop)) hED2).add
      (o_of_bdd_mul (bdd_cu (fun c _ => 4 * (c - 1) * c ^ 3) (by fun_prop)) hED3)).add
      (o_of_bdd_mul (bdd_cu (fun c _ => c ^ 4) (by fun_prop)) hED4)
    have h2 := o_of_bdd_div_n3 (bdd_cu (fun c u => c ^ 4 *
      (12 * lam4 ^ 2 - 42 * lam4 + 4 * lam6 - 24 * lam3 ^ 2 + 26 +
        u * (-18 * lam4 ^ 2 + 24 * lam4 + 9) + u ^ 2 * (12 * lam4 ^ 2 - 24 * lam4 + 12) +
        u ^ 3 * (-3 * lam4 ^ 2 + 6 * lam4 - 3))) (by fun_prop))
    refine (h1.add h2).congr' (ev_eq2 fun n hn => ?_) EventuallyEq.rfl
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
    rw [hEΔ4 n, hED1 n]
    simp only [cN]
    field_simp
    ring

/-- Moment rates `E[D⁴], E[Δ⁴] = O(n⁻²)` and `E[D⁸], E[Δ⁸] = O(n⁻⁴)` used by the Taylor step. -/
theorem moment_bounds (h_rem : RemainderOrderHypothesis) :
    (fun n => E (D n ^ 4 : momAlg μ)) =O[atTop] (fun n => rt n ^ 4) ∧
    (fun n => E (D n ^ 8 : momAlg μ)) =O[atTop] (fun n => rt n ^ 8) ∧
    (fun n => E (Δ n ^ 4 : momAlg μ)) =O[atTop] (fun n => rt n ^ 4) ∧
    (fun n => E (Δ n ^ 8 : momAlg μ)) =O[atTop] (fun n => rt n ^ 8) := by
  rcases derived_moments (Ω := Ω) h_rem with ⟨_, _, _, hD4, _, _, _, hΔ4⟩
  have hD8 := h_rem.2.2
  refine ⟨isBigO_rt4_of_asymp _ hD4, hD8, isBigO_rt4_of_asymp _ hΔ4, ?_⟩
  have hΔ_eq : ∀ n, (Δ n : momAlg μ) = const (cN n - 1) + const (cN n) * D n := by
    intro n; simp only [Δ, cN, const, map_sub, map_one]; ring
  have hpt : ∀ n, E (Δ n ^ 8 : momAlg μ) ≤ 128 * ((cN n - 1) ^ 8 + cN n ^ 8 * E (D n ^ 8)) := by
    intro n
    have h := E_mono (X := ((const (cN n - 1) + const (cN n) * D n) ^ 8 : momAlg μ))
      (Y := (128 : ℝ) • ((const (cN n - 1)) ^ 8 + (const (cN n) * D n) ^ 8))
      (fun ω => by
        show (((const (cN n - 1) : momAlg μ) : Ω → ℝ) ω +
            ((const (cN n) * D n : momAlg μ) : Ω → ℝ) ω) ^ 8 ≤
          128 * ((((const (cN n - 1) : momAlg μ) : Ω → ℝ) ω) ^ 8 +
            (((const (cN n) * D n : momAlg μ) : Ω → ℝ) ω) ^ 8)
        exact add_pow_eight_le _ _)
    rw [← hΔ_eq n, E_smul, E_add, ← map_pow, E_const, mul_pow, ← map_pow, E_const_mul] at h
    exact h
  have hc1 : (fun n : ℕ => cN n - 1) =O[atTop] (fun n => rt n ^ 2) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have heq : cN n - 1 = 1 / ((n : ℝ) - 1) := by
      unfold cN; rw [div_sub_one (ne_of_gt hn1)]; congr 1; ring
    have hle : 1 / ((n : ℝ) - 1) ≤ 2 / n := by
      rw [div_le_div_iff₀ hn1 hn0]; linarith
    rw [heq, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (pow_nonneg (rt_nonneg n) 2),
      rt_sq]
    calc 1 / ((n : ℝ) - 1) ≤ 2 / n := hle
      _ = 2 * (1 / (n : ℝ)) := by ring
  have hc8 : (fun n : ℕ => (cN n - 1) ^ 8) =O[atTop] (fun n => rt n ^ 8) := by
    refine (hc1.pow 8).trans (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_))
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      ← pow_mul]
    exact pow_le_pow_of_le_one (rt_nonneg n) (rt_le_one n) (by norm_num)
  have hc8' : (fun n : ℕ => cN n ^ 8) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    bdd_cu (fun c _ => c ^ 8) (by fun_prop)
  have hbound : (fun n => 128 * ((cN n - 1) ^ 8 + cN n ^ 8 * E (D n ^ 8 : momAlg μ)))
      =O[atTop] (fun n => rt n ^ 8) :=
    (hc8.add ((hc8'.mul hD8).congr' EventuallyEq.rfl (ev_eq fun n => one_mul _))).const_mul_left 128
  exact isBigO_of_nonneg_le hbound (fun n => E_pow_even_nonneg _ ⟨4, rfl⟩) hpt

/-!
### Deriving the eighth moment rates from the moment assumptions

For i.i.d. mean zero `W_i` with all moments finite, `E[(∑_{i<n} W_i)^m] = O(n^(m/2))`. This is proved
from the exact recursion `E[(S + W_n)^m] = ∑_j C(m,j) E[S^j] E[W^(m-j)]` (independence of `S` and `W_n`),
using `E[W] = 0` to kill the `j = m - 1` term.
-/

/-- Real recursion lemma behind the moment growth bound. -/
theorem moment_growth (a : ℕ → ℕ → ℝ) (M : ℕ → ℝ) (hM0 : M 0 = 1) (hM1 : M 1 = 0)
    (h0 : ∀ m, a m 0 = if m = 0 then 1 else 0)
    (hrec : ∀ m n, a m (n + 1) =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * a j n * M (m - j)) :
    ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ N, ∀ n, |a j n| ≤ B * ((n : ℝ) + 1) ^ (j / 2) := by
  intro N
  induction N with
  | zero =>
    refine ⟨1, zero_le_one, fun j hj n => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    have ha : ∀ n, a 0 n = 1 := by
      intro n
      induction n with
      | zero => simp [h0]
      | succ n hn => rw [hrec]; simp [hn, hM0]
    simp [ha]
  | succ N ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    have hstep : ∀ n, a (N + 1) (n + 1) = a (N + 1) n +
        ∑ j ∈ Finset.range N, ((N + 1).choose j : ℝ) * a j n * M (N + 1 - j) := by
      intro n
      rw [hrec, Finset.sum_range_succ, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self,
        Nat.add_sub_cancel_left, hM0, hM1, Nat.cast_one]
      ring
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = B * ∑ j ∈ Finset.range N, ((N + 1).choose j : ℝ) * |M (N + 1 - j)| :=
      ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by
      rw [hK]; exact mul_nonneg hB0 (Finset.sum_nonneg fun j _ => by positivity)
    have hinc : ∀ n, |∑ j ∈ Finset.range N, ((N + 1).choose j : ℝ) * a j n * M (N + 1 - j)| ≤
        K * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) := by
      intro n
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc _ ≤ ∑ j ∈ Finset.range N, |((N + 1).choose j : ℝ) * a j n * M (N + 1 - j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range N, ((N + 1).choose j : ℝ) * |M (N + 1 - j)| *
              (B * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_range] at hj
            rw [abs_mul, abs_mul, Nat.abs_cast]
            have h1 : |a j n| ≤ B * ((n : ℝ) + 1) ^ (j / 2) := hB j (by omega) n
            have h2 : ((n : ℝ) + 1) ^ (j / 2) ≤ ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) :=
              pow_le_pow_right₀ hn1 (by omega)
            have h3 : |a j n| ≤ B * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) :=
              h1.trans (mul_le_mul_of_nonneg_left h2 hB0)
            have hc : (0 : ℝ) ≤ ((N + 1).choose j : ℝ) := Nat.cast_nonneg _
            calc ((N + 1).choose j : ℝ) * |a j n| * |M (N + 1 - j)|
                = ((N + 1).choose j : ℝ) * |M (N + 1 - j)| * |a j n| := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg hc (abs_nonneg _))
        _ = K * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) := by
            rw [hK, ← Finset.sum_mul]; ring
    have hmain : ∀ n, |a (N + 1) n| ≤ K * n * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) := by
      intro n
      induction n with
      | zero => simp [h0]
      | succ n hn =>
        rw [hstep n]
        have hpow : ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) ≤ ((n : ℝ) + 1 + 1) ^ ((N + 1) / 2 - 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        calc _ ≤ |a (N + 1) n| +
              |∑ j ∈ Finset.range N, ((N + 1).choose j : ℝ) * a j n * M (N + 1 - j)| :=
              abs_add_le _ _
          _ ≤ K * n * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) + K * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) :=
              add_le_add hn (hinc n)
          _ = K * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) := by ring
          _ ≤ K * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) ^ ((N + 1) / 2 - 1) :=
              mul_le_mul_of_nonneg_left hpow (mul_nonneg hK0 (by positivity))
          _ = K * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) ^ ((N + 1) / 2 - 1) := by
              push_cast; ring
    refine ⟨max B K, le_max_of_le_left hB0, fun j hj n => ?_⟩
    rcases Nat.lt_or_ge j (N + 1) with hlt | hge
    · exact (hB j (by omega) n).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hjN : j = N + 1 := by omega
      subst hjN
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        have hK' : K = 0 := by rw [hK]; simp
        have h := hmain n
        rw [hK', zero_mul, zero_mul] at h
        exact h.trans (mul_nonneg (le_max_of_le_left hB0) (by positivity))
      · have hq1 : 1 ≤ (N + 1) / 2 := by omega
        have hkey : (n : ℝ) * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) ≤ ((n : ℝ) + 1) ^ ((N + 1) / 2) := by
          calc (n : ℝ) * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1)
              ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) :=
                mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = ((n : ℝ) + 1) ^ ((N + 1) / 2) := by
                rw [← pow_succ']; congr 1; omega
        calc |a (N + 1) n| ≤ K * n * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1) := hmain n
          _ = K * ((n : ℝ) * ((n : ℝ) + 1) ^ ((N + 1) / 2 - 1)) := by ring
          _ ≤ K * ((n : ℝ) + 1) ^ ((N + 1) / 2) := mul_le_mul_of_nonneg_left hkey hK0
          _ ≤ max B K * ((n : ℝ) + 1) ^ ((N + 1) / 2) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- `E[A^j B^l] = E[A^j] E[B^l]` for independent measurable `A, B` (Mathlib's `IndepFun`). -/
theorem E_pow_mul_pow_of_indep {A B : momAlg μ}
    (h : ProbabilityTheory.IndepFun (A : Ω → ℝ) (B : Ω → ℝ) μ)
    (hA : Measurable (A : Ω → ℝ)) (hB : Measurable (B : Ω → ℝ)) (j l : ℕ) :
    E (A ^ j * B ^ l) = E (A ^ j) * E (B ^ l) := by
  have hp := h.comp (measurable_id.pow_const j) (measurable_id.pow_const l)
  exact hp.integral_mul_eq_mul_integral ((measurable_id.pow_const j).comp hA).aestronglyMeasurable
    ((measurable_id.pow_const l).comp hB).aestronglyMeasurable

/-- Moment growth `E[(∑_{i<n} W_i)^m] = O((n+1)^(m/2))` for `W_i = φ(Z_i)` with `E[W] = 0`. -/
theorem sum_moment_bound (φ : ℝ → ℝ) (hφ : Measurable φ) (W : ℕ → momAlg μ)
    (hW : ∀ i, (W i : Ω → ℝ) = φ ∘ Zr (μ := μ) i) (hW0 : E (W 0) = 0) :
    ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ m ≤ N, ∀ n,
      |E ((∑ i ∈ Finset.range n, W i) ^ m)| ≤ B * ((n : ℝ) + 1) ^ (m / 2) := by
  have hWm : ∀ i, Measurable (W i : Ω → ℝ) := fun i => by
    rw [hW]; exact hφ.comp (Zr_measurable i)
  have hind : ProbabilityTheory.iIndepFun (fun i => (W i : Ω → ℝ)) μ := by
    have h := (Zr_indep (μ := μ)).comp (fun _ => φ) (fun _ => hφ)
    have he : (fun i => (W i : Ω → ℝ)) = fun i => φ ∘ Zr (μ := μ) i := funext hW
    rw [he]; exact h
  have hident : ∀ i l, E (W i ^ l) = E (W 0 ^ l) := by
    intro i l
    have h := ((Zr_ident (μ := μ) i).comp (u := fun x => φ x ^ l) (hφ.pow_const l)).integral_eq
    show ∫ ω, ((W i : Ω → ℝ) ω) ^ l ∂μ = ∫ ω, ((W 0 : Ω → ℝ) ω) ^ l ∂μ
    rw [hW, hW]; exact h
  have hsumcoe : ∀ n, ((∑ i ∈ Finset.range n, W i : momAlg μ) : Ω → ℝ) =
      ∑ i ∈ Finset.range n, (W i : Ω → ℝ) := fun n => by simp
  refine moment_growth (fun m n => E ((∑ i ∈ Finset.range n, W i) ^ m)) (fun l => E (W 0 ^ l))
    ?_ ?_ ?_ ?_
  · beta_reduce; rw [pow_zero, E_one]
  · beta_reduce; rw [pow_one, hW0]
  · intro m
    beta_reduce
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [E_one]
    · rw [Finset.sum_range_zero, zero_pow hm.ne', E_zero, if_neg hm.ne']
  · intro m n
    beta_reduce
    rw [Finset.sum_range_succ, add_pow]
    show E_lm _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hS : Measurable ((∑ i ∈ Finset.range n, W i : momAlg μ) : Ω → ℝ) := by
      rw [hsumcoe, Finset.sum_fn]; exact Finset.measurable_sum _ fun i _ => hWm i
    have hI : ProbabilityTheory.IndepFun ((∑ i ∈ Finset.range n, W i : momAlg μ) : Ω → ℝ)
        (W n : Ω → ℝ) μ := by
      rw [hsumcoe]; exact hind.indepFun_finsetSum_of_notMem hWm Finset.notMem_range_self
    have hc : (∑ i ∈ Finset.range n, W i) ^ j * W n ^ (m - j) * ((m.choose j : ℕ) : momAlg μ) =
        const ((m.choose j : ℕ) : ℝ) * ((∑ i ∈ Finset.range n, W i) ^ j * W n ^ (m - j)) := by
      rw [show (const ((m.choose j : ℕ) : ℝ) : momAlg μ) = ((m.choose j : ℕ) : momAlg μ) from
        map_natCast (algebraMap ℝ (momAlg μ)) _]
      ring
    rw [E_lm_apply, hc, E_const_mul, E_pow_mul_pow_of_indep hI hS (hWm n), hident n]
    ring

/-- Real algebra: `(u - v²)⁸ ≤ 128 (u⁸ + v¹⁶)`. -/
theorem sub_sq_pow_eight_le (u v : ℝ) : (u - v ^ 2) ^ 8 ≤ 128 * (u ^ 8 + v ^ 16) := by
  have h := add_pow_eight_le u (-(v ^ 2))
  have e1 : (u - v ^ 2) ^ 8 = (u + -(v ^ 2)) ^ 8 := by ring
  have e2 : (-(v ^ 2)) ^ 8 = v ^ 16 := by ring
  rw [e1]; rw [e2] at h; exact h

/-- From `|E[S_n^m]| ≤ B (n+1)^k` with `m = 2k`, the average satisfies `E[(S_n/n)^m] = O(rt^m)`. -/
theorem rate_of_sum {W : ℕ → momAlg μ} (m k : ℕ) (hm : m = 2 * k) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n, |E ((∑ i ∈ Finset.range n, W i) ^ m)| ≤ B * ((n : ℝ) + 1) ^ k) :
    (fun n : ℕ => E (((1 / (n : ℝ)) • ∑ i ∈ Finset.range n, W i) ^ m)) =O[atTop]
      (fun n : ℕ => rt n ^ m) := by
  subst hm
  refine IsBigO.of_bound (B * 2 ^ k) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hrt : rt n ^ (2 * k) = (1 / (n : ℝ)) ^ k := by rw [pow_mul, rt_sq]
  rw [smul_pow, E_smul, hrt, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ (2 * k)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ k)]
  have h1 : ((n : ℝ) + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
  have hsq : (1 / (n : ℝ)) ^ 2 * n = 1 / n := by
    field_simp
  have h2 : (1 / (n : ℝ)) ^ (2 * k) * (2 * n) ^ k = 2 ^ k * (1 / (n : ℝ)) ^ k := by
    rw [pow_mul, mul_pow, show ((1 / (n : ℝ)) ^ 2) ^ k * (2 ^ k * (n : ℝ) ^ k) =
      2 ^ k * ((1 / (n : ℝ)) ^ 2 * n) ^ k by rw [mul_pow]; ring, hsq]
  calc (1 / (n : ℝ)) ^ (2 * k) * |E ((∑ i ∈ Finset.range n, W i) ^ (2 * k))|
      ≤ (1 / (n : ℝ)) ^ (2 * k) * (B * (2 * n) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (hB n).trans (mul_le_mul_of_nonneg_left h1 hB0)
    _ = B * ((1 / (n : ℝ)) ^ (2 * k) * (2 * n) ^ k) := by ring
    _ = B * 2 ^ k * (1 / (n : ℝ)) ^ k := by rw [h2]; ring

theorem V_eq (n : ℕ) : (V n : momAlg μ) = (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, Zs i := by
  simp only [V, sampleAvg, Fintype.card_fin]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => Zs (μ := μ) i) n

theorem U_eq (n : ℕ) :
    (U n : momAlg μ) = (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, (Zs i ^ 2 - 1) := by
  simp only [U, sampleAvg, Fintype.card_fin]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => (Zs (μ := μ) i) ^ 2 - 1) n

/-- **The eighth moment rates are proved** from the textbook moment assumptions. -/
theorem remainder_order : RemainderOrderHypothesis (μ := μ) := by
  have hZ0 : E (Zs (μ := μ) 0) = 0 := by
    have h := E_Zs_pow (μ := μ) 0 1
    rwa [pow_one, lam_one] at h
  have hA0 : E ((Zs (μ := μ) 0) ^ 2 - 1) = 0 := by
    rw [E_sub, E_Zs_pow, lam_two, E_one, sub_self]
  obtain ⟨BV, hBV0, hBV⟩ := sum_moment_bound (μ := μ) id measurable_id Zs (fun i => rfl) hZ0 16
  obtain ⟨BU, hBU0, hBU⟩ := sum_moment_bound (μ := μ) (fun z => z ^ 2 - 1) (by fun_prop)
    (fun i => Zs i ^ 2 - 1) (fun i => by funext ω; rfl) hA0 8
  have hV8 : (fun n => E (V n ^ 8 : momAlg μ)) =O[atTop] (fun n => rt n ^ 8) := by
    refine (rate_of_sum 8 4 rfl BV hBV0 (fun n => hBV 8 (by norm_num) n)).congr'
      (ev_eq fun n => ?_) EventuallyEq.rfl
    rw [V_eq]
  have hV16 : (fun n => E (V n ^ 16 : momAlg μ)) =O[atTop] (fun n => rt n ^ 16) := by
    refine (rate_of_sum 16 8 rfl BV hBV0 (fun n => hBV 16 le_rfl n)).congr'
      (ev_eq fun n => ?_) EventuallyEq.rfl
    rw [V_eq]
  have hU8 : (fun n => E (U n ^ 8 : momAlg μ)) =O[atTop] (fun n => rt n ^ 8) := by
    refine (rate_of_sum 8 4 rfl BU hBU0 (fun n => hBU 8 le_rfl n)).congr'
      (ev_eq fun n => ?_) EventuallyEq.rfl
    rw [U_eq]
  have h16 : (fun n : ℕ => rt n ^ 16) =O[atTop] (fun n => rt n ^ 8) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [one_mul, Real.norm_of_nonneg (pow_nonneg (rt_nonneg n) _),
      Real.norm_of_nonneg (pow_nonneg (rt_nonneg n) _)]
    exact pow_le_pow_of_le_one (rt_nonneg n) (rt_le_one n) (by norm_num)
  have hpt : ∀ n, E (D n ^ 8 : momAlg μ) ≤ 128 * (E (U n ^ 8) + E (V n ^ 16)) := by
    intro n
    have h := E_mono (X := (D n ^ 8 : momAlg μ)) (Y := (128 : ℝ) • (U n ^ 8 + V n ^ 16))
      (fun ω => by
        show ((((U n : momAlg μ) : Ω → ℝ) ω) - (((V n : momAlg μ) : Ω → ℝ) ω) ^ 2) ^ 8 ≤
          128 * ((((U n : momAlg μ) : Ω → ℝ) ω) ^ 8 + (((V n : momAlg μ) : Ω → ℝ) ω) ^ 16)
        exact sub_sq_pow_eight_le _ _)
    rwa [E_smul, E_add] at h
  have hg : (fun n => 128 * (E (U n ^ 8 : momAlg μ) + E (V n ^ 16)))
      =O[atTop] (fun n => rt n ^ 8) :=
    (hU8.add (hV16.trans h16)).const_mul_left 128
  exact ⟨hU8, hV8, isBigO_of_nonneg_le hg (fun n => E_pow_even_nonneg _ ⟨4, rfl⟩) hpt⟩

/-!
## 6. Second-Order Asymptotic Expansions of `E[S_n]`, `MSE(S_n)`, `E[σ̂_n]`, and `MSE(σ̂_n)`
-/

/-- Asymptotic expectation expansion of `σ (1 + δ n)` proved via `taylor_remainder_E_small`. -/
theorem E_sqrt_expansion (δ x : ℕ → momAlg μ) (h_sq : ∀ n, (1 + δ n) ^ 2 = 1 + x n)
    (hδx : ∀ n ω, |(δ n : Ω → ℝ) ω| ≤ |(x n : Ω → ℝ) ω|)
    (hx4 : (fun n => E (x n ^ 4)) =O[atTop] (fun n => rt n ^ 4))
    (hx8 : (fun n => E (x n ^ 8)) =O[atTop] (fun n => rt n ^ 8)) :
    (fun n => E (const σ * (1 + δ n)) - σ * (1 + (1 / 2) * E (x n) - (1 / 8) * E (x n ^ 2) +
        (1 / 16) * E (x n ^ 3) - (5 / 128) * E (x n ^ 4)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have h_s := taylor_remainder_E_small δ x h_sq hδx hx4 hx8
  have h_sc := isLittleO_inv_n2_smul σ h_s
  have hL : ∀ n, σ * E (1 + δ n) = E (const σ * (1 + δ n)) :=
    fun n => (E_const_mul σ (1 + δ n)).symm
  have hR : ∀ n,
      σ * E (1 + const (1 / 2) * x n - const (1 / 8) * x n ^ 2 +
        const (1 / 16) * x n ^ 3 - const (5 / 128) * x n ^ 4) =
      σ * (1 + (1 / 2) * E (x n) - (1 / 8) * E (x n ^ 2) +
        (1 / 16) * E (x n ^ 3) - (5 / 128) * E (x n ^ 4)) := by
    intro n; simp [E_one]
  exact isLittleO_inv_n2_eq_left hL (isLittleO_inv_n2_eq_right h_sc hR)

/-- Asymptotic MSE expansion for any square-root estimator `θ̂ n = σ (1 + δ n)` with `(1 + δ n)² = 1 + x n`. -/
theorem MSE_sqrt_expansion (δ x : ℕ → momAlg μ) (h_sq : ∀ n, (1 + δ n) ^ 2 = 1 + x n)
    (hδx : ∀ n ω, |(δ n : Ω → ℝ) ω| ≤ |(x n : Ω → ℝ) ω|)
    (hx4 : (fun n => E (x n ^ 4)) =O[atTop] (fun n => rt n ^ 4))
    (hx8 : (fun n => E (x n ^ 8)) =O[atTop] (fun n => rt n ^ 8)) :
    (fun n => MSE (const σ * (1 + δ n)) σ -
      σ ^ 2 * ((1 / 4) * E (x n ^ 2) - (1 / 8) * E (x n ^ 3) + (5 / 64) * E (x n ^ 4)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  dsimp [MSE]
  have h_s := taylor_remainder_E_small δ x h_sq hδx hx4 hx8
  have hE_lhs : ∀ n, σ ^ 2 * ((1 + E (x n)) - 2 * E (1 + δ n) + 1) =
      E ((const σ * (1 + δ n) - const σ) ^ 2) := by
    intro n
    have heq : (const σ * (1 + δ n) - const σ) ^ 2 =
        const σ * (const σ * (1 + x n)) -
        const σ * (const σ * ((1 + δ n) + (1 + δ n))) +
        const σ * (const σ * 1) := by
      linear_combination const σ * const σ * h_sq n
    rw [heq]; simp [E_one]; ring
  have hR : ∀ n, E (1 + const (1 / 2) * x n - const (1 / 8) * x n ^ 2 +
      const (1 / 16) * x n ^ 3 - const (5 / 128) * x n ^ 4) =
      1 + (1 / 2) * E (x n) - (1 / 8) * E (x n ^ 2) +
        (1 / 16) * E (x n ^ 3) - (5 / 128) * E (x n ^ 4) := by
    intro n; simp [E_one]
  have h_s' := isLittleO_inv_n2_eq_right h_s hR
  have h_lin := isLittleO_inv_n2_smul (σ ^ 2)
    (isLittleO_inv_n2_add
      (isLittleO_inv_n2_sub (isLittleO_inv_n2_refl (fun n => 1 + E (x n))) (isLittleO_inv_n2_smul 2 h_s'))
      (isLittleO_inv_n2_refl (fun _ => 1)))
  exact isLittleO_inv_n2_eq_left hE_lhs (isLittleO_inv_n2_eq_right h_lin (fun n => by ring))

/-- Second-order asymptotic expansion of `E[S_n]` up to `o(n⁻²)`. -/
theorem E_Sn_formula (h_rem : RemainderOrderHypothesis) :
    (fun n => E (S_n n) - (σ - (σ / (8 * (n : ℝ))) * (lam4 - 1) +
        (σ / (128 * (n : ℝ) ^ 2)) * (8 * lam6 - 15 * lam4 ^ 2 + 6 * lam4 - 48 * lam3 ^ 2 - 31)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  rcases derived_moments (Ω := Ω) h_rem with ⟨_, _, _, _, hd1, hd2, hd3, hd4⟩
  rcases moment_bounds (Ω := Ω) h_rem with ⟨hD4b, hD8b, hΔ4b, hΔ8b⟩
  have h_tSn := isLittleO_inv_n2_eq_left
    (fun n => by rw [← S_n_eq n])
    (E_sqrt_expansion δ_Sn Δ h_Sn_sq abs_δ_Sn_le hΔ4b hΔ8b)
  have h_poly := isLittleO_inv_n2_smul σ
    (isLittleO_inv_n2_sub
      (isLittleO_inv_n2_add
        (isLittleO_inv_n2_sub
          (isLittleO_inv_n2_add (isLittleO_inv_n2_refl (fun _ => 1)) (isLittleO_inv_n2_smul (1 / 2) hd1))
          (isLittleO_inv_n2_smul (1 / 8) hd2))
        (isLittleO_inv_n2_smul (1 / 16) hd3))
      (isLittleO_inv_n2_smul (5 / 128) hd4))
  exact isLittleO_inv_n2_eq_right (isLittleO_inv_n2_trans h_tSn h_poly) (fun n => by ring)

/-- Second-order asymptotic expansion of `MSE(S_n, σ)` up to `o(n⁻²)`. -/
theorem MSE_Sn_formula (h_rem : RemainderOrderHypothesis) :
    (fun n => MSE (S_n n) σ - ((σ ^ 2 / (4 * (n : ℝ))) * (lam4 - 1) +
        (σ ^ 2 / (64 * (n : ℝ) ^ 2)) * (48 * lam3 ^ 2 + 15 * lam4 ^ 2 - 6 * lam4 - 8 * lam6 + 31)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  rcases derived_moments (Ω := Ω) h_rem with ⟨_, _, _, _, _, hd2, hd3, hd4⟩
  rcases moment_bounds (Ω := Ω) h_rem with ⟨hD4b, hD8b, hΔ4b, hΔ8b⟩
  have h_tSn := isLittleO_inv_n2_eq_left
    (fun n => by rw [← S_n_eq n])
    (MSE_sqrt_expansion δ_Sn Δ h_Sn_sq abs_δ_Sn_le hΔ4b hΔ8b)
  have h_poly := isLittleO_inv_n2_smul (σ ^ 2)
    (isLittleO_inv_n2_add
      (isLittleO_inv_n2_sub (isLittleO_inv_n2_smul (1 / 4) hd2) (isLittleO_inv_n2_smul (1 / 8) hd3))
      (isLittleO_inv_n2_smul (5 / 64) hd4))
  exact isLittleO_inv_n2_eq_right (isLittleO_inv_n2_trans h_tSn h_poly) (fun n => by ring)

/-- Second-order asymptotic expansion of `E[σ̂_n]` up to `o(n⁻²)`. -/
theorem E_sigmaHat_formula (h_rem : RemainderOrderHypothesis) :
    (fun n => E (sigmaHat n) - (σ - (σ / (8 * (n : ℝ))) * (lam4 + 3) +
        (σ / (128 * (n : ℝ) ^ 2)) * (8 * lam6 - 15 * lam4 ^ 2 + 14 * lam4 - 48 * lam3 ^ 2 - 55)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  rcases derived_moments (Ω := Ω) h_rem with ⟨hD1, hD2, hD3, hD4, _, _, _, _⟩
  rcases moment_bounds (Ω := Ω) h_rem with ⟨hD4b, hD8b, hΔ4b, hΔ8b⟩
  have h_tSH1 := isLittleO_inv_n2_eq_left
    (fun n => by rw [← sigmaHat_eq n])
    (E_sqrt_expansion δ_sigmaHat D h_sigmaHat_sq abs_δ_sigmaHat_le hD4b hD8b)
  have h_tSH : (fun n => E (sigmaHat n) -
      σ * (1 + (1 / 2) * (-1 / (n : ℝ)) - (1 / 8) * E (D n ^ 2) +
        (1 / 16) * E (D n ^ 3) - (5 / 128) * E (D n ^ 4)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) :=
    isLittleO_inv_n2_eq_right h_tSH1 (fun n => by rw [hD1 n])
  have h_poly := isLittleO_inv_n2_smul σ
    (isLittleO_inv_n2_sub
      (isLittleO_inv_n2_add
        (isLittleO_inv_n2_sub
          (isLittleO_inv_n2_refl (fun n => 1 + (1 / 2) * (-1 / (n : ℝ))))
          (isLittleO_inv_n2_smul (1 / 8) hD2))
        (isLittleO_inv_n2_smul (1 / 16) hD3))
      (isLittleO_inv_n2_smul (5 / 128) hD4))
  exact isLittleO_inv_n2_eq_right (isLittleO_inv_n2_trans h_tSH h_poly) (fun n => by ring)

/-- Second-order asymptotic expansion of `MSE(σ̂_n, σ)` up to `o(n⁻²)`. -/
theorem MSE_sigmaHat_formula (h_rem : RemainderOrderHypothesis) :
    (fun n => MSE (sigmaHat n) σ - ((σ ^ 2 / (4 * (n : ℝ))) * (lam4 - 1) +
        (σ ^ 2 / (64 * (n : ℝ) ^ 2)) * (48 * lam3 ^ 2 + 15 * lam4 ^ 2 - 14 * lam4 - 8 * lam6 + 55)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  rcases derived_moments (Ω := Ω) h_rem with ⟨_, hD2, hD3, hD4, _, _, _, _⟩
  rcases moment_bounds (Ω := Ω) h_rem with ⟨hD4b, hD8b, hΔ4b, hΔ8b⟩
  have h_tSH := isLittleO_inv_n2_eq_left
    (fun n => by rw [← sigmaHat_eq n])
    (MSE_sqrt_expansion δ_sigmaHat D h_sigmaHat_sq abs_δ_sigmaHat_le hD4b hD8b)
  have h_poly := isLittleO_inv_n2_smul (σ ^ 2)
    (isLittleO_inv_n2_add
      (isLittleO_inv_n2_sub (isLittleO_inv_n2_smul (1 / 4) hD2) (isLittleO_inv_n2_smul (1 / 8) hD3))
      (isLittleO_inv_n2_smul (5 / 64) hD4))
  exact isLittleO_inv_n2_eq_right (isLittleO_inv_n2_trans h_tSH h_poly) (fun n => by ring)

/-!
## 7. Main Comparison Theorems, Kurtosis Threshold `lam4 = 3`, and Normal Special Case
-/

/-- Second-order MSE difference `MSE(S_n, σ) - MSE(σ̂_n, σ) = σ²(lam4 - 3) / (8 n²) + o(n⁻²)`. -/
theorem MSE_diff_formula (h_rem : RemainderOrderHypothesis) :
    (fun n => (MSE (S_n n) σ - MSE (sigmaHat n) σ) - (σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) :=
  isLittleO_inv_n2_eq_right
    (isLittleO_inv_n2_sub (MSE_Sn_formula h_rem) (MSE_sigmaHat_formula h_rem))
    (fun n => by ring)

/-- Claim 1(a): When `lam4 = 3`, `MSE(S_n) = MSE(σ̂_n) + o(n⁻²)`. -/
theorem MSE_eq_at_kurtosis_three (h_rem : RemainderOrderHypothesis) (h : lam4 = 3) :
    (fun n => MSE (S_n n) σ - MSE (sigmaHat n) σ) =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hdiff := MSE_diff_formula (Ω := Ω) h_rem
  rw [h] at hdiff
  exact hdiff.congr' (Eventually.of_forall fun n => by ring) EventuallyEq.rfl

/-- Claim 1(b): For `0 < n`, the leading `O(n⁻²)` difference term `σ²(lam4 - 3)/(8n²)` vanishes iff `lam4 = 3`. -/
theorem MSE_leading_diff_zero_iff_kurtosis_three (n : ℕ) (hn : 0 < n) :
    σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2) = 0 ↔ lam4 = 3 := by
  have hσ0 : (0 : ℝ) < σ := hσ (Ω := Ω)
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  constructor
  · intro h
    have h_pos : 0 < σ ^ 2 / (8 * (n : ℝ) ^ 2) := by positivity
    have h_prod : (σ ^ 2 / (8 * (n : ℝ) ^ 2)) * (lam4 - 3) = 0 := by
      linarith [show (σ ^ 2 / (8 * (n : ℝ) ^ 2)) * (lam4 - 3) = σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2) by ring]
    nlinarith
  · intro h; rw [h]; ring

/-- Claim 1(c): For heavier tails (`lam4 > 3`) and `0 < n`, the `1/n²` MSE difference `σ²(lam4 - 3)/(8n²)` is strictly positive. -/
theorem MSE_leading_diff_pos_of_kurtosis_gt_three (n : ℕ) (hn : 0 < n) (h : 3 < lam4) :
    0 < σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2) := by
  have hσ0 : (0 : ℝ) < σ := hσ (Ω := Ω)
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_sub : 0 < lam4 - 3 := sub_pos.mpr h
  positivity

/-- Claim 1(d): For lighter tails (`lam4 < 3`) and `0 < n`, the `1/n²` MSE difference `σ²(lam4 - 3)/(8n²)` is strictly negative. -/
theorem MSE_leading_diff_neg_of_kurtosis_lt_three (n : ℕ) (hn : 0 < n) (h : lam4 < 3) :
    σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2) < 0 := by
  have hσ0 : (0 : ℝ) < σ := hσ (Ω := Ω)
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_pos : 0 < σ ^ 2 * (3 - lam4) / (8 * (n : ℝ) ^ 2) := by
    have h_sub : 0 < 3 - lam4 := sub_pos.mpr h
    positivity
  have h_eq : σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2) = - (σ ^ 2 * (3 - lam4) / (8 * (n : ℝ) ^ 2)) := by ring
  linarith

/-- Claim 2(a): General `MSE(S_n)` expansion up to `o(n⁻²)` when `lam4 = 3`. -/
theorem MSE_Sn_at_kurtosis_three (h_rem : RemainderOrderHypothesis) (h : lam4 = 3) :
    (fun n => MSE (S_n n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (σ ^ 2 / (16 * (n : ℝ) ^ 2)) * (12 * lam3 ^ 2 - 2 * lam6 + 37)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hSn := MSE_Sn_formula (Ω := Ω) h_rem
  rw [h] at hSn
  exact isLittleO_inv_n2_eq_right hSn (fun n => by ring)

/-- Claim 2(b): General `MSE(σ̂_n)` expansion up to `o(n⁻²)` when `lam4 = 3`. -/
theorem MSE_sigmaHat_at_kurtosis_three (h_rem : RemainderOrderHypothesis) (h : lam4 = 3) :
    (fun n => MSE (sigmaHat n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (σ ^ 2 / (16 * (n : ℝ) ^ 2)) * (12 * lam3 ^ 2 - 2 * lam6 + 37)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hSH := MSE_sigmaHat_formula (Ω := Ω) h_rem
  rw [h] at hSH
  exact isLittleO_inv_n2_eq_right hSH (fun n => by ring)

/-- Claim 2(c): General `E[S_n]` expansion up to `o(n⁻²)` when `lam4 = 3`. -/
theorem E_Sn_at_kurtosis_three (h_rem : RemainderOrderHypothesis) (h : lam4 = 3) :
    (fun n => E (S_n n) - (σ - σ / (4 * (n : ℝ)) + (σ / (32 * (n : ℝ) ^ 2)) * (2 * lam6 - 12 * lam3 ^ 2 - 37)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hESn := E_Sn_formula (Ω := Ω) h_rem
  rw [h] at hESn
  exact isLittleO_inv_n2_eq_right hESn (fun n => by ring)

/-- Claim 2(d): General `E[σ̂_n]` expansion up to `o(n⁻²)` when `lam4 = 3`. -/
theorem E_sigmaHat_at_kurtosis_three (h_rem : RemainderOrderHypothesis) (h : lam4 = 3) :
    (fun n => E (sigmaHat n) - (σ - (3 * σ) / (4 * (n : ℝ)) + (σ / (32 * (n : ℝ) ^ 2)) * (2 * lam6 - 12 * lam3 ^ 2 - 37)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hESH := E_sigmaHat_formula (Ω := Ω) h_rem
  rw [h] at hESH
  exact isLittleO_inv_n2_eq_right hESH (fun n => by ring)

/-- Claim 3(a): Normal distribution (`lam3 = 0, lam4 = 3, lam6 = 15`) expansion for `E[S_n]` up to `o(n⁻²)`. -/
theorem E_Sn_normal (h_rem : RemainderOrderHypothesis)
    (h3 : lam3 = 0) (h4 : lam4 = 3) (h6 : lam6 = 15) :
    (fun n => E (S_n n) - (σ - σ / (4 * (n : ℝ)) - (7 * σ) / (32 * (n : ℝ) ^ 2)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hESn := E_Sn_formula (Ω := Ω) h_rem
  rw [h3, h4, h6] at hESn
  exact isLittleO_inv_n2_eq_right hESn (fun n => by ring)

/-- Claim 3(b): Normal distribution (`lam3 = 0, lam4 = 3, lam6 = 15`) expansion for `E[σ̂_n]` up to `o(n⁻²)`. -/
theorem E_sigmaHat_normal (h_rem : RemainderOrderHypothesis)
    (h3 : lam3 = 0) (h4 : lam4 = 3) (h6 : lam6 = 15) :
    (fun n => E (sigmaHat n) - (σ - (3 * σ) / (4 * (n : ℝ)) - (7 * σ) / (32 * (n : ℝ) ^ 2)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hESH := E_sigmaHat_formula (Ω := Ω) h_rem
  rw [h3, h4, h6] at hESH
  exact isLittleO_inv_n2_eq_right hESH (fun n => by ring)

/-- Claim 3(c): Normal distribution (`lam3 = 0, lam4 = 3, lam6 = 15`) expansion for `MSE(S_n)` up to `o(n⁻²)`. -/
theorem MSE_Sn_normal (h_rem : RemainderOrderHypothesis)
    (h3 : lam3 = 0) (h4 : lam4 = 3) (h6 : lam6 = 15) :
    (fun n => MSE (S_n n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (7 * σ ^ 2) / (16 * (n : ℝ) ^ 2)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hSn := MSE_Sn_formula (Ω := Ω) h_rem
  rw [h3, h4, h6] at hSn
  exact isLittleO_inv_n2_eq_right hSn (fun n => by ring)

/-- Claim 3(d): Normal distribution (`lam3 = 0, lam4 = 3, lam6 = 15`) expansion for `MSE(σ̂_n)` up to `o(n⁻²)`. -/
theorem MSE_sigmaHat_normal (h_rem : RemainderOrderHypothesis)
    (h3 : lam3 = 0) (h4 : lam4 = 3) (h6 : lam6 = 15) :
    (fun n => MSE (sigmaHat n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (7 * σ ^ 2) / (16 * (n : ℝ) ^ 2)))
      =o[atTop] (fun n => 1 / (n : ℝ) ^ 2) := by
  have hSH := MSE_sigmaHat_formula (Ω := Ω) h_rem
  rw [h3, h4, h6] at hSH
  exact isLittleO_inv_n2_eq_right hSH (fun n => by ring)

/-!
## 8. Bundled Verification Certificate and Kernel Axiom Audit
-/

/-- Explicit algebraic certificate for the MSE difference as a square times `(lam4 - 3)` up to `o(n⁻²)`. -/
theorem mse_diff_sos_certificate (h_rem : RemainderOrderHypothesis) :
    (fun (n : ℕ) => (MSE (S_n n) σ - MSE (sigmaHat n) σ) - (1 / 8) * (σ / (n : ℝ)) ^ 2 * (lam4 - 3))
      =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) :=
  isLittleO_inv_n2_eq_right (MSE_diff_formula h_rem) (fun n => by ring)

/-- Explicit algebraic certificate for the shared expansion at `lam4 = 3` up to `o(n⁻²)`. -/
theorem mse_shared_at_kurtosis_three_certificate
    (h_rem : RemainderOrderHypothesis) (h : lam4 = 3) :
    (fun (n : ℕ) => MSE (S_n n) σ - MSE (sigmaHat n) σ) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
    (fun (n : ℕ) => MSE (S_n n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (σ ^ 2 / (16 * (n : ℝ) ^ 2)) * (12 * lam3 ^ 2 - 2 * lam6 + 37)))
      =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) :=
  ⟨MSE_eq_at_kurtosis_three h_rem h, MSE_Sn_at_kurtosis_three h_rem h⟩

/-- Bundled certificate theorem combining all main claims from the problem statement,
    proved from `SampleModel` and the explicit hypothesis `h_rem : RemainderOrderHypothesis`
    with zero `sorry`. -/
theorem master_verification_certificate (h_rem : RemainderOrderHypothesis) :
    -- Claim 0: Exact 4th-order Taylor expansion `taylorSqrt4`
    (∀ δ x : momAlg μ, (1 + δ) ^ 2 = 1 + x →
      1 + δ - (1 + const (1 / 2) * x - const (1 / 8) * x ^ 2 +
        const (1 / 16) * x ^ 3 - const (5 / 128) * x ^ 4) =
      (const (7 / 8) + const (7 / 8) * δ + const (5 / 16) * δ ^ 2 + const (5 / 128) * δ ^ 3) *
        δ ^ 5) ∧
    ((fun (n : ℕ) => E (Δ n) - 0) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
     (fun (n : ℕ) => E (Δ n ^ 2) - ((lam4 - 1) / (n : ℝ) + 2 / (n : ℝ) ^ 2)) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
     (fun (n : ℕ) => E (Δ n ^ 3) - ((lam6 - 3 * lam4 - 6 * lam3 ^ 2 + 2) / (n : ℝ) ^ 2)) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
     (fun (n : ℕ) => E (Δ n ^ 4) - (3 * (lam4 - 1) ^ 2 / (n : ℝ) ^ 2)) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2)) ∧
    -- Claim 1: General second-order expansions and MSE difference up to o(n⁻²)
    (fun (n : ℕ) => E (S_n n) - (σ - (σ / (8 * (n : ℝ))) * (lam4 - 1) +
        (σ / (128 * (n : ℝ) ^ 2)) * (8 * lam6 - 15 * lam4 ^ 2 + 6 * lam4 - 48 * lam3 ^ 2 - 31))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
    (fun (n : ℕ) => MSE (S_n n) σ - ((σ ^ 2 / (4 * (n : ℝ))) * (lam4 - 1) +
        (σ ^ 2 / (64 * (n : ℝ) ^ 2)) * (48 * lam3 ^ 2 + 15 * lam4 ^ 2 - 6 * lam4 - 8 * lam6 + 31))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
    (fun (n : ℕ) => MSE (sigmaHat n) σ - ((σ ^ 2 / (4 * (n : ℝ))) * (lam4 - 1) +
        (σ ^ 2 / (64 * (n : ℝ) ^ 2)) * (48 * lam3 ^ 2 + 15 * lam4 ^ 2 - 14 * lam4 - 8 * lam6 + 55))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
    (fun (n : ℕ) => (MSE (S_n n) σ - MSE (sigmaHat n) σ) - (σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
    -- Claim 2: General MSE and expectation formulas at lam4 = 3 up to o(n⁻²)
    (lam4 = 3 →
      (fun (n : ℕ) => MSE (S_n n) σ - MSE (sigmaHat n) σ) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
      (fun (n : ℕ) => MSE (S_n n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (σ ^ 2 / (16 * (n : ℝ) ^ 2)) * (12 * lam3 ^ 2 - 2 * lam6 + 37))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
      (fun (n : ℕ) => E (S_n n) - (σ - σ / (4 * (n : ℝ)) + (σ / (32 * (n : ℝ) ^ 2)) * (2 * lam6 - 12 * lam3 ^ 2 - 37))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2)) ∧
    -- Claim 3: Normal distribution special case (lam3 = 0, lam4 = 3, lam6 = 15) up to o(n⁻²)
    (lam3 = 0 → lam4 = 3 → lam6 = 15 →
      (fun (n : ℕ) => E (S_n n) - (σ - σ / (4 * (n : ℝ)) - (7 * σ) / (32 * (n : ℝ) ^ 2))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
      (fun (n : ℕ) => MSE (S_n n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (7 * σ ^ 2) / (16 * (n : ℝ) ^ 2))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2) ∧
      (fun (n : ℕ) => MSE (sigmaHat n) σ - (σ ^ 2 / (2 * (n : ℝ)) + (7 * σ ^ 2) / (16 * (n : ℝ) ^ 2))) =o[atTop] (fun (n : ℕ) => 1 / (n : ℝ) ^ 2)) := by
  rcases derived_moments (Ω := Ω) h_rem with ⟨_, _, _, _, hd1, hd2, hd3, hd4⟩
  refine ⟨taylorSqrt4,
          ⟨hd1, hd2, hd3, hd4⟩,
          E_Sn_formula h_rem,
          MSE_Sn_formula h_rem,
          MSE_sigmaHat_formula h_rem,
          MSE_diff_formula h_rem,
          fun h4 => ⟨MSE_eq_at_kurtosis_three h_rem h4,
                     MSE_Sn_at_kurtosis_three h_rem h4,
                     E_Sn_at_kurtosis_three h_rem h4⟩,
          fun h3 h4 h6 => ⟨E_Sn_normal h_rem h3 h4 h6,
                           MSE_Sn_normal h_rem h3 h4 h6,
                           MSE_sigmaHat_normal h_rem h3 h4 h6⟩⟩

/-!
## 9. Textbook Estimators and the Main Theorem (no extra hypotheses)

The sample standard deviations are defined by their textbook formulas from the raw observations
`X_i`, and the main results are stated for them using only the `SampleModel` assumptions.
-/

/-- Sample mean `X̄_n = (1/n) ∑_{i<n} X_i`. -/
def Xbar (n : ℕ) (ω : Ω) : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, SampleModel.X i ω

/-- Unadjusted sample standard deviation `σ̂_n = √((1/n) ∑_{i<n} (X_i - X̄_n)²)`. -/
def sampleSD (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2)

/-- Bessel-corrected sample standard deviation `S_n = √((1/(n-1)) ∑_{i<n} (X_i - X̄_n)²)`. -/
def besselSD (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt ((1 / ((n : ℝ) - 1)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2)

/-- Expectation `E[T] = ∫ T dμ` of a real statistic. -/
def expect [SampleModel Ω μ] (T : Ω → ℝ) : ℝ := ∫ ω, T ω ∂μ

/-- Mean squared error `MSE(T, θ) = E[(T - θ)²]` of a real statistic. -/
def mse [SampleModel Ω μ] (T : Ω → ℝ) (θ : ℝ) : ℝ := ∫ ω, (T ω - θ) ^ 2 ∂μ

/-- Real identity `1 + (1/n) ∑ (z_i² - 1) - z̄² = (1/n) ∑ (z_i - z̄)²` for `n ≥ 1`. -/
theorem sample_var_eq {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    1 + ((1 / (n : ℝ)) * ∑ i, (z i ^ 2 - 1) - ((1 / (n : ℝ)) * ∑ i, z i) ^ 2) =
      (1 / (n : ℝ)) * ∑ i, (z i - (1 / (n : ℝ)) * ∑ j, z j) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set v := (1 / (n : ℝ)) * ∑ i, z i with hv
  have hsum : ∑ i, z i = (n : ℝ) * v := by rw [hv]; field_simp
  have h1 : ∑ i, (z i - v) ^ 2 = ∑ i, z i ^ 2 - 2 * v * ∑ i, z i + (n : ℝ) * v ^ 2 := by
    have hpt : ∀ i, (z i - v) ^ 2 = z i ^ 2 - 2 * v * z i + v ^ 2 := fun i => by ring
    simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ∑ i, (z i ^ 2 - 1) = ∑ i, z i ^ 2 - (n : ℝ) := by
    simp [Finset.sum_sub_distrib]
  rw [h1, h2, hsum]; field_simp; ring

theorem coe_Zm_apply (n : ℕ) (i : Fin n) (ω : Ω) :
    ((Zm n i : momAlg μ) : Ω → ℝ) ω = (SampleModel.X i ω - mean (μ := μ)) / σ (μ := μ) := rfl

/-- `(1/n) ∑ (X_i - X̄)² = σ² (1 + D_n)` pointwise, for `n ≥ 1`. -/
theorem sum_sq_dev_eq (n : ℕ) (hn : 0 < n) (ω : Ω) :
    (1 / (n : ℝ)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2 =
      σ (μ := μ) ^ 2 * ((1 + D n : momAlg μ) : Ω → ℝ) ω := by
  have hσ0 : σ (μ := μ) ≠ 0 := (hσ (μ := μ)).ne'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hX : ∀ i : Fin n, SampleModel.X (↑i) ω =
      σ (μ := μ) * ((Zm n i : momAlg μ) : Ω → ℝ) ω + mean (μ := μ) := by
    intro i; rw [coe_Zm_apply]; field_simp; ring
  have hXbar : Xbar (μ := μ) n ω = σ (μ := μ) *
      ((1 / (n : ℝ)) * ∑ i : Fin n, ((Zm n i : momAlg μ) : Ω → ℝ) ω) + mean (μ := μ) := by
    simp only [Xbar, hX, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hD : ((1 + D n : momAlg μ) : Ω → ℝ) ω = 1 + ((1 / (n : ℝ)) *
      ∑ i : Fin n, ((((Zm n i : momAlg μ) : Ω → ℝ) ω) ^ 2 - 1) -
      ((1 / (n : ℝ)) * ∑ i : Fin n, ((Zm n i : momAlg μ) : Ω → ℝ) ω) ^ 2) := by
    have h : ((1 + D n : momAlg μ) : Ω → ℝ) ω =
        1 + (((U n : momAlg μ) : Ω → ℝ) ω - (((V n : momAlg μ) : Ω → ℝ) ω) ^ 2) := rfl
    rw [h, coe_U_apply, coe_V_apply]
  rw [hD, sample_var_eq hn (fun i => ((Zm n i : momAlg μ) : Ω → ℝ) ω), hXbar]
  generalize (1 / (n : ℝ)) * ∑ i : Fin n, ((Zm n i : momAlg μ) : Ω → ℝ) ω = zb
  have hterm : ∀ i : Fin n, (SampleModel.X (↑i) ω - (σ (μ := μ) * zb + mean (μ := μ))) ^ 2 =
      σ (μ := μ) ^ 2 * (((Zm n i : momAlg μ) : Ω → ℝ) ω - zb) ^ 2 := fun i => by rw [hX]; ring
  simp only [hterm]
  rw [← Finset.mul_sum]
  ring

theorem sampleSD_eq (n : ℕ) (hn : 0 < n) :
    sampleSD (μ := μ) n = ((sigmaHat n : momAlg μ) : Ω → ℝ) := by
  funext ω
  rw [sampleSD, sum_sq_dev_eq n hn ω, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hσ (μ := μ)).le]
  rfl

theorem besselSD_eq (n : ℕ) (hn : 2 ≤ n) :
    besselSD (μ := μ) n = ((S_n n : momAlg μ) : Ω → ℝ) := by
  funext ω
  have hn0 : (n : ℝ) ≠ 0 := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                               positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact ne_of_gt (by linarith)
  have h1 := sum_sq_dev_eq (μ := μ) n (by omega) ω
  have hΔ : ((1 + Δ n : momAlg μ) : Ω → ℝ) ω =
      ((n : ℝ) / ((n : ℝ) - 1)) * ((1 + D n : momAlg μ) : Ω → ℝ) ω := by
    change (1 : ℝ) + (((n : ℝ) / ((n : ℝ) - 1)) * ((1 + D n : momAlg μ) : Ω → ℝ) ω - 1) = _
    ring
  have h2 : (1 / ((n : ℝ) - 1)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2 =
      σ (μ := μ) ^ 2 * ((1 + Δ n : momAlg μ) : Ω → ℝ) ω := by
    rw [hΔ]
    calc (1 / ((n : ℝ) - 1)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2
        = ((n : ℝ) / ((n : ℝ) - 1)) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2) := by
          field_simp
      _ = _ := by rw [h1]; ring
  rw [besselSD, h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hσ (μ := μ)).le]
  rfl

theorem expect_coe (X : momAlg μ) : expect (μ := μ) (X : Ω → ℝ) = E X := rfl

theorem mse_coe (X : momAlg μ) (θ : ℝ) : mse (μ := μ) (X : Ω → ℝ) θ = MSE X θ := rfl

theorem ev_expect_S : ∀ᶠ n : ℕ in atTop, E (S_n n : momAlg μ) = expect (μ := μ) (besselSD n) := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [besselSD_eq n hn, expect_coe]

theorem ev_expect_σ : ∀ᶠ n : ℕ in atTop,
    E (sigmaHat n : momAlg μ) = expect (μ := μ) (sampleSD n) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sampleSD_eq n hn, expect_coe]

theorem ev_mse_S : ∀ᶠ n : ℕ in atTop,
    MSE (S_n n : momAlg μ) σ = mse (μ := μ) (besselSD n) σ := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [besselSD_eq n hn, mse_coe]

theorem ev_mse_σ : ∀ᶠ n : ℕ in atTop,
    MSE (sigmaHat n : momAlg μ) σ = mse (μ := μ) (sampleSD n) σ := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sampleSD_eq n hn, mse_coe]

/-- **Main theorem (textbook form).** For i.i.d. observations with all moments finite and positive
    variance, with `σ = √Var(X₀)` and standardized moments `λ_k = E[((X₀ - m)/σ)^k]`:
    second-order expansions of `E[S_n]`, `E[σ̂_n]`, `MSE(S_n)`, `MSE(σ̂_n)`, and their MSE
    difference, all up to `o(n⁻²)`, plus the kurtosis `λ₄ = 3` and normal special cases. -/
theorem textbook_certificate :
    (fun n : ℕ => expect (μ := μ) (besselSD n) - (σ - (σ / (8 * (n : ℝ))) * (lam4 - 1) +
        (σ / (128 * (n : ℝ) ^ 2)) * (8 * lam6 - 15 * lam4 ^ 2 + 6 * lam4 - 48 * lam3 ^ 2 - 31)))
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
    (fun n : ℕ => expect (μ := μ) (sampleSD n) - (σ - (σ / (8 * (n : ℝ))) * (lam4 + 3) +
        (σ / (128 * (n : ℝ) ^ 2)) * (8 * lam6 - 15 * lam4 ^ 2 + 14 * lam4 - 48 * lam3 ^ 2 - 55)))
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
    (fun n : ℕ => mse (μ := μ) (besselSD n) σ - ((σ ^ 2 / (4 * (n : ℝ))) * (lam4 - 1) +
        (σ ^ 2 / (64 * (n : ℝ) ^ 2)) * (48 * lam3 ^ 2 + 15 * lam4 ^ 2 - 6 * lam4 - 8 * lam6 + 31)))
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
    (fun n : ℕ => mse (μ := μ) (sampleSD n) σ - ((σ ^ 2 / (4 * (n : ℝ))) * (lam4 - 1) +
        (σ ^ 2 / (64 * (n : ℝ) ^ 2)) * (48 * lam3 ^ 2 + 15 * lam4 ^ 2 - 14 * lam4 - 8 * lam6 + 55)))
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
    (fun n : ℕ => (mse (μ := μ) (besselSD n) σ - mse (μ := μ) (sampleSD n) σ) -
        σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2))
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
    (lam4 = 3 → (fun n : ℕ => mse (μ := μ) (besselSD n) σ - mse (μ := μ) (sampleSD n) σ)
      =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) ∧
    (lam3 = 0 → lam4 = 3 → lam6 = 15 →
      (fun n : ℕ => expect (μ := μ) (besselSD n) -
          (σ - σ / (4 * (n : ℝ)) - (7 * σ) / (32 * (n : ℝ) ^ 2)))
        =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
      (fun n : ℕ => mse (μ := μ) (besselSD n) σ -
          (σ ^ 2 / (2 * (n : ℝ)) + (7 * σ ^ 2) / (16 * (n : ℝ) ^ 2)))
        =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∧
      (fun n : ℕ => mse (μ := μ) (sampleSD n) σ -
          (σ ^ 2 / (2 * (n : ℝ)) + (7 * σ ^ 2) / (16 * (n : ℝ) ^ 2)))
        =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)) := by
  have h := remainder_order (μ := μ)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun h4 => ?_, fun h3 h4 h6 => ⟨?_, ?_, ?_⟩⟩
  · refine (E_Sn_formula h).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_expect_S (μ := μ)] with n hn; rw [hn]
  · refine (E_sigmaHat_formula h).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_expect_σ (μ := μ)] with n hn; rw [hn]
  · refine (MSE_Sn_formula h).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_mse_S (μ := μ)] with n hn; rw [hn]
  · refine (MSE_sigmaHat_formula h).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_mse_σ (μ := μ)] with n hn; rw [hn]
  · refine (MSE_diff_formula h).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_mse_S (μ := μ), ev_mse_σ (μ := μ)] with n h1 h2; rw [h1, h2]
  · refine (MSE_eq_at_kurtosis_three h h4).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_mse_S (μ := μ), ev_mse_σ (μ := μ)] with n h1 h2; rw [h1, h2]
  · refine (E_Sn_normal h h3 h4 h6).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_expect_S (μ := μ)] with n hn; rw [hn]
  · refine (MSE_Sn_normal h h3 h4 h6).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_mse_S (μ := μ)] with n hn; rw [hn]
  · refine (MSE_sigmaHat_normal h h3 h4 h6).congr' ?_ EventuallyEq.rfl
    filter_upwards [ev_mse_σ (μ := μ)] with n hn; rw [hn]

-- Kernel Axiom Audit:
#print axioms textbook_certificate
#print axioms remainder_order
#print axioms master_verification_certificate
#print axioms taylorSqrt4
#print axioms MSE_leading_diff_zero_iff_kurtosis_three
#print axioms MSE_leading_diff_pos_of_kurtosis_gt_three
#print axioms MSE_leading_diff_neg_of_kurtosis_lt_three
#print axioms sampleAvg_moment1
#print axioms sampleAvg_moment2
#print axioms sampleAvg_moment3
#print axioms sampleAvg_moment4

end SampleModel
end
end SdMseLean
