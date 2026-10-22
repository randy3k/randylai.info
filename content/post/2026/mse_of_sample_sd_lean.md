---
title: MSE of sample standard deviation (Lean by AI)
date: 2026-10-21
categories: Statistics
tags: 
    - Statistics
    - Probability
    - AI
    - Lean
---

Back in 2023, I wrote a [post]({{< relref "/post/2023/mse_of_sample_sd_cont" >}}) using SymPy to compute the second order expansion of the mean squared error (MSE) of the sample standard deviation up to $O(n^{-2})$. Earlier this year, I revisited the problem in [MSE of sample standard deviation (Gen AI)]({{< relref "/post/2026/mse_of_sample_sd_gen_ai" >}}) and showed that a modern LLM can derive the entire second order expansion directly from a prompt.

When an AI produces a long asymptotic derivation with dozens of polynomial moment terms, how can we trust that every coefficient is right and that no terms of order $n^{-2}$ were dropped? To check the derivation rigorously, I formalized and verified the entire proof in [Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).

The complete Lean 4 formalization is a single file, [`SampleSdMse.lean`](https://github.com/randy3k/randylai.info/blob/master/content/post/2026/SampleSdMse.lean). It builds with Lean `v4.35.0` and Mathlib `v4.35.0` (commit `56a0058`). A [complete human readable proof]({{< relref "/post/2026/mse_of_sample_sd_lean_proof" >}}) follows the Lean formalization step by step.

### Summary of Results

Let $X_1, X_2, \ldots$ be i.i.d. with mean $\mu$, variance $\sigma^2 > 0$, and finite moments. We compare two estimators of the population standard deviation $\sigma$:

* $S_n = \sqrt{\frac{1}{n-1}\sum _ {i=1}^n (X_i - \bar X)^2}$ (Bessel corrected, using $n - 1$ in the denominator)
* $\hat \sigma_n = \sqrt{\frac{1}{n}\sum _ {i=1}^n (X_i - \bar X)^2} = \sqrt{\frac{n-1}{n}} S_n$ (unadjusted, using $n$ in the denominator)

Let $\lambda_k = \frac{E[(X - \mu)^k]}{\sigma^k}$ denote the standardized central moments, with $\lambda_3$ the skewness, $\lambda_4$ the kurtosis, and $\lambda_6$ the sixth moment. The general second order expansions are:

$$
E(S_n) = \sigma - \frac{\sigma}{8n} (\lambda_4 - 1) + \frac{\sigma}{128n^2} \left(8 \lambda_6 - 15 \lambda_4^2 + 6 \lambda_4 - 48 \lambda_3^2 - 31\right) + o(n^{-2})
$$

$$
E(\hat \sigma_n) = \sigma - \frac{\sigma}{8n} (\lambda_4 + 3) + \frac{\sigma}{128n^2} \left(8 \lambda_6 - 15 \lambda_4^2 + 14 \lambda_4 - 48 \lambda_3^2 - 55\right) + o(n^{-2})
$$

$$
MSE(S_n) = \frac{\sigma^2}{4n} (\lambda_4 - 1) + \frac{\sigma^2}{64n^2} \left(48 \lambda_3^2 + 15 \lambda_4^2 - 6 \lambda_4 - 8 \lambda_6 + 31\right) + o(n^{-2})
$$

$$
MSE(\hat \sigma_n) = \frac{\sigma^2}{4n} (\lambda_4 - 1) + \frac{\sigma^2}{64n^2} \left(48 \lambda_3^2 + 15 \lambda_4^2 - 14 \lambda_4 - 8 \lambda_6 + 55\right) + o(n^{-2})
$$

Taking the difference gives:

$$
MSE(S_n) - MSE(\hat \sigma_n) = \frac{\sigma^2 (\lambda_4 - 3)}{8n^2} + o(n^{-2})
$$

This leads to three conclusions:

1. **Threshold at $\lambda_4 = 3$:** When the kurtosis is $\lambda_4 = 3$, the $1/n^2$ leading difference term vanishes:
   $$
   MSE(S_n) - MSE(\hat \sigma_n) = o(n^{-2})
   $$
   For heavier tails ($\lambda_4 > 3$), $\hat \sigma_n$ has smaller MSE. For lighter tails ($\lambda_4 < 3$), $S_n$ has smaller MSE.

2. **Shared expansion at $\lambda_4 = 3$:**
   $$
   MSE(S_n) = MSE(\hat \sigma_n) + o(n^{-2}) = \frac{\sigma^2}{2n} + \frac{\sigma^2}{16n^2}\left(12\lambda_3^2 - 2\lambda_6 + 37\right) + o(n^{-2})
   $$
   with expected value:
   $$
   E(S_n) = \sigma - \frac{\sigma}{4n} + \frac{\sigma}{32n^2}\left(2\lambda_6 - 12\lambda_3^2 - 37\right) + o(n^{-2})
   $$

3. **Normal distribution special case ($\lambda_3 = 0, \lambda_4 = 3, \lambda_6 = 15$):**
   $$
   E(S_n) = \sigma - \frac{\sigma}{4n} - \frac{7\sigma}{32n^2} + o(n^{-2})
   $$
   $$
   MSE(S_n) = MSE(\hat \sigma_n) + o(n^{-2}) = \frac{\sigma^2}{2n} + \frac{7\sigma^2}{16n^2} + o(n^{-2})
   $$

### Formalization in Lean 4 with Mathlib

**Assumptions.** The only assumptions are the textbook i.i.d. model, stated with Mathlib's standard notions of independence (`iIndepFun`), identical distribution (`IdentDistrib`), and variance:

```lean
class SampleModel (Ω : outParam Type*) [MeasurableSpace Ω]
    (μ : outParam (Measure Ω)) [IsProbabilityMeasure μ] where
  X : ℕ → Ω → ℝ
  measurable : ∀ i, Measurable (X i)
  indep : ProbabilityTheory.iIndepFun X μ
  ident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ
  moments : ∀ k : ℕ, Integrable (fun ω => X 0 ω ^ k) μ
  var_pos : 0 < ProbabilityTheory.variance (X 0) μ
```

In words: on a probability space $(\Omega, \mu)$, the observations $X_0, X_1, \ldots$ are measurable, mutually independent, identically distributed, have all moments finite, and have positive variance. The proof only uses moments up to order 16; assuming all moments are finite keeps the formalization simple.

**Definitions.** Everything in the main theorem is a plain textbook definition. Expectation is Mathlib's Bochner integral:

```lean
def mean : ℝ := ∫ ω, SampleModel.X 0 ω ∂μ
def σ : ℝ := Real.sqrt (ProbabilityTheory.variance (SampleModel.X 0) μ)
def lam (k : ℕ) : ℝ := ∫ ω, ((SampleModel.X 0 ω - mean (μ := μ)) / σ (μ := μ)) ^ k ∂μ

def Xbar (n : ℕ) (ω : Ω) : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, SampleModel.X i ω
def sampleSD (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2)
def besselSD (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt ((1 / ((n : ℝ) - 1)) * ∑ i : Fin n, (SampleModel.X i ω - Xbar (μ := μ) n ω) ^ 2)
def expect [SampleModel Ω μ] (T : Ω → ℝ) : ℝ := ∫ ω, T ω ∂μ
def mse [SampleModel Ω μ] (T : Ω → ℝ) (θ : ℝ) : ℝ := ∫ ω, (T ω - θ) ^ 2 ∂μ
```

Here `lam k` is $\lambda_k$, `sampleSD` is $\hat \sigma_n$, and `besselSD` is $S_n$. Asymptotic statements use Mathlib's standard little $o$ notation along `atTop` for integer sample sizes. For example, the MSE difference is the following part of the main theorem `textbook_certificate`, which assumes nothing beyond `SampleModel`:

```lean
(fun n : ℕ => (mse (besselSD n) σ - mse (sampleSD n) σ) -
    σ ^ 2 * (lam4 - 3) / (8 * (n : ℝ) ^ 2))
  =o[atTop] (fun n : ℕ => 1 / (n : ℝ) ^ 2)
```

**Proof outline.** Lean checks every step of the following argument:

1. Standardize $Z_i = (X_i - \mu)/\sigma$ and write $\hat \sigma_n = \sigma \sqrt{1 + D_n}$ and $S_n = \sigma \sqrt{1 + \Delta_n}$, where $D_n = U_n - V_n^2$ with $U_n = \frac{1}{n}\sum (Z_i^2 - 1)$ and $V_n = \bar Z$, and $1 + \Delta_n = \frac{n}{n-1}(1 + D_n)$.
2. Compute the exact finite sample moments of $U_n$ and $V_n$ from independence, including the exact $1/n^3$ correction in the fourth moments.
3. Expand $\sqrt{1 + x}$ to fourth order with an exact remainder, and bound the expected remainder using $|\sqrt{1 + x} - 1| \le |x|$ and the Cauchy Schwarz inequality.
4. Prove the moment growth bound $E[T_n^m] = O(n^{m/2})$ for partial sums $T_n = \sum _ {i=1}^n W_i$ of i.i.d. mean zero $W_i$, from the recursion $E[T_{n+1}^m] = \sum_j \binom{m}{j} E[T_n^j] E[W^{m-j}]$, which holds because $T_n$ is independent of $W_{n+1}$. This gives every higher order remainder as $o(n^{-2})$ without any extra rate assumption.

### Kernel Axiom Audit

Running `lake build SdMseLean` compiles the library with no `sorry`, and `#print axioms` shows that every theorem depends only on the standard Lean 4 axioms:

```text
info: SdMseLean/SampleSdMse.lean:2511:0: 'SdMseLean.SampleModel.textbook_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SdMseLean/SampleSdMse.lean:2512:0: 'SdMseLean.SampleModel.remainder_order' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SdMseLean/SampleSdMse.lean:2514:0: 'SdMseLean.SampleModel.taylorSqrt4' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SdMseLean/SampleSdMse.lean:2518:0: 'SdMseLean.sampleAvg_moment1' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SdMseLean/SampleSdMse.lean:2519:0: 'SdMseLean.sampleAvg_moment2' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SdMseLean/SampleSdMse.lean:2520:0: 'SdMseLean.sampleAvg_moment3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: SdMseLean/SampleSdMse.lean:2521:0: 'SdMseLean.sampleAvg_moment4' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3047 jobs).
```

Lean's kernel checks every coefficient in the expansions above, under exactly the assumptions listed in `SampleModel`. What remains a human judgment is whether those Lean statements say what we mean, which is why the assumptions and definitions are kept as close to the textbook as possible.
