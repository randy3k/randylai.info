---
title: "MSE of sample standard deviation (Lean by AI): complete proof"
date: 2026-10-21
_build:
  list: never
---

This is the human-readable version of the proof that Lean checks in [`SampleSdMse.lean`](https://github.com/randy3k/randylai.info/blob/master/content/post/2026/SampleSdMse.lean), accompanying the post [MSE of sample standard deviation (Lean by AI)]({{< relref "/post/2026/mse_of_sample_sd_lean" >}}). The Lean name of each step is given in brackets.

## 0. Setting and statement

**Assumptions** [`SampleModel`]. $X_1, X_2, \ldots$ are i.i.d. real random variables on a probability space, with all moments finite and $\mathrm{Var}(X_1) > 0$. Write

$$
m = E X_1,\qquad \sigma = \sqrt{\mathrm{Var}(X_1)},\qquad Z_i = \frac{X_i - m}{\sigma},\qquad \lambda_k = E Z_1^k .
$$

Then $E Z_i = 0$ and $E Z_i^2 = 1$ [`lam_one`, `lam_two`]. The $Z_i$ are i.i.d. as measurable functions of the $X_i$ [`Zr_indep`, `Zr_ident`].

**Estimators** [`sampleSD`, `besselSD`]. With $\bar X = \frac1n \sum_{i=1}^n X_i$,

$$
\hat\sigma_n = \sqrt{\frac1n \sum_{i=1}^n (X_i - \bar X)^2},\qquad
S_n = \sqrt{\frac1{n-1} \sum_{i=1}^n (X_i - \bar X)^2}.
$$

**Theorem** [`textbook_certificate`]. As $n \to \infty$,

{{< math >}}
$$
\begin{aligned}
E(S_n) &= \sigma - \frac{\sigma}{8n}(\lambda_4 - 1) + \frac{\sigma}{128 n^2}\left(8\lambda_6 - 15\lambda_4^2 + 6\lambda_4 - 48\lambda_3^2 - 31\right) + o(n^{-2}),\\
E(\hat\sigma_n) &= \sigma - \frac{\sigma}{8n}(\lambda_4 + 3) + \frac{\sigma}{128 n^2}\left(8\lambda_6 - 15\lambda_4^2 + 14\lambda_4 - 48\lambda_3^2 - 55\right) + o(n^{-2}),\\
MSE(S_n) &= \frac{\sigma^2}{4n}(\lambda_4 - 1) + \frac{\sigma^2}{64 n^2}\left(48\lambda_3^2 + 15\lambda_4^2 - 6\lambda_4 - 8\lambda_6 + 31\right) + o(n^{-2}),\\
MSE(\hat\sigma_n) &= \frac{\sigma^2}{4n}(\lambda_4 - 1) + \frac{\sigma^2}{64 n^2}\left(48\lambda_3^2 + 15\lambda_4^2 - 14\lambda_4 - 8\lambda_6 + 55\right) + o(n^{-2}),
\end{aligned}
$$
{{< /math >}}

and therefore $MSE(S_n) - MSE(\hat\sigma_n) = \dfrac{\sigma^2(\lambda_4 - 3)}{8n^2} + o(n^{-2})$. Here $MSE(T) = E[(T - \sigma)^2]$.

**Integrability.** Every random variable below is a polynomial in finitely many $Z_i$, or is dominated by one (Step 5 shows $|\sqrt{1+x} - 1| \le |x|$). All moments of $Z_1$ are finite, so all of these are integrable and expectation is linear on them [`momAlg`, `E_lm`].

## 1. Reduction to standardized fluctuations

Define

$$
A_i = Z_i^2 - 1,\qquad U_n = \frac1n\sum_{i=1}^n A_i,\qquad V_n = \bar Z = \frac1n \sum_{i=1}^n Z_i,\qquad D_n = U_n - V_n^2 .
$$

We have $X_i - \bar X = \sigma (Z_i - \bar Z)$ and $\frac1n\sum Z_i^2 = 1 + U_n$, so for $n \ge 1$

$$
\frac1n \sum_{i=1}^n (X_i - \bar X)^2 = \sigma^2 \Big(\frac1n \sum Z_i^2 - \bar Z^2\Big) = \sigma^2 (1 + D_n)
$$

[`sum_sq_dev_eq`]

Hence $\hat\sigma_n = \sigma\sqrt{1 + D_n}$ for $n \ge 1$ [`sampleSD_eq`]. With

$$
c_n = \frac{n}{n-1},\qquad 1 + \Delta_n = c_n (1 + D_n),
$$

we get $S_n = \sigma \sqrt{1 + \Delta_n}$ for $n \ge 2$ [`besselSD_eq`]. In particular $1 + D_n \ge 0$ and $1 + \Delta_n \ge 0$ [`one_add_D_nonneg`, `one_add_Δ_nonneg`]. The identities hold for all large $n$, so it suffices to prove the expansions for $\sigma\sqrt{1 + D_n}$ and $\sigma\sqrt{1 + \Delta_n}$.

## 2. Exact finite sample moments of $U_n$ and $V_n$

Independence gives $E\big[\prod_{i\in s} f_i(Z_i)\big] = \prod_{i \in s} E f_i(Z_i)$ for distinct indices and measurable $f_i$ [`indep_E`, from Mathlib's `iIndepFun.integral_fun_prod_comp`]. With $E Z = E A = 0$, any product in which some index occurs exactly once has expectation zero. The moments needed are

$$
E A^2 = \lambda_4 - 1,\quad E A^3 = \lambda_6 - 3\lambda_4 + 2,\quad E[AZ] = \lambda_3,\quad E[AZ^2] = \lambda_4 - 1,\quad E[A^2Z^2] = \lambda_6 - 2\lambda_4 + 1,
$$

together with $E A^4 = \lambda_8 - 4\lambda_6 + 6\lambda_4 - 3$ [`E_A2`, `E_A3`, `E_AZ`, `E_AZ2`, `E_A2Z2`, `E_A4`].

Expanding the sums and keeping only index patterns with no index occurring exactly once [`cov2_of_indep`, `cov3_of_indep`, `cov4_of_indep`, `sampleAvg_moment1` to `sampleAvg_moment4`]:

| Quantity | Surviving index patterns | Value |
|---|---|---|
| $E U_n$ | none | $0$ |
| $E V_n^2$ | $i=j$ | $1/n$ |
| $E U_n^2$ | $i=j$ | $(\lambda_4 - 1)/n$ |
| $E U_n^3$ | $i=j=k$ | $(\lambda_6 - 3\lambda_4 + 2)/n^2$ |
| $E [U_n V_n^2]$ | $i=j=k$ | $(\lambda_4 - 1)/n^2$ |
| $E V_n^4$ | all equal; two distinct pairs | $3/n^2 + (\lambda_4 - 3)/n^3$ |
| $E [U_n^2 V_n^2]$ | all equal; $\lbrace i,j \rbrace, \lbrace k,l \rbrace$; two cross pairings | $(\lambda_4 - 1 + 2\lambda_3^2)/n^2 + O(n^{-3})$ |
| $E U_n^4$ | all equal; two distinct pairs | $3(\lambda_4-1)^2/n^2 + O(n^{-3})$ |

For example, $E[U_n^2V_n^2] = n^{-4}\big[\thinspace n E[A^2Z^2] + n(n-1) E A^2\thinspace  E Z^2 + 2n(n-1)(E[AZ])^2\big]$. Each $O(n^{-3})$ term is an explicit constant over $n^3$, hence $o(n^{-2})$ [`sample_mean_moments`, `o_div_n3`].

## 3. Moment growth bound (replaces any rate assumption)

**Lemma** [`moment_growth`, `sum_moment_bound`]. Let $W_1, W_2, \ldots$ be i.i.d. with all moments finite and $E W = 0$, and let $T_n = \sum_{i=1}^n W_i$. For every $m$ there is $B_m$ with

$$
|E T_n^m| \le B_m (n+1)^{\lfloor m/2 \rfloor}\qquad\text{for all } n.
$$

*Proof.* $T_n$ is a function of $W_1, \ldots, W_n$, so it is independent of $W_{n+1}$ [Mathlib `iIndepFun.indepFun_finsetSum_of_notMem`]. Write $a_m(n) = E T_n^m$ and $M_l = E W^l$, so $M_0 = 1$ and $M_1 = 0$. The binomial theorem and independence give

$$
a_m(n+1) = E\big[(T_n + W_{n+1})^m\big] = \sum_{j=0}^m \binom{m}{j} a_j(n)\thinspace  M_{m-j}.
$$

The $j = m$ term is $a_m(n)$, and the $j = m-1$ term vanishes because $M_1 = 0$. Hence

$$
a_m(n+1) - a_m(n) = \sum_{j=0}^{m-2} \binom{m}{j} a_j(n) M_{m-j}.
$$

Induct on $m$. For $m = 0$, $a_0 \equiv 1$. Suppose the bound holds for all $j < m$, with $m \ge 1$, and let $q = \lfloor m/2 \rfloor$. For $j \le m-2$ we have $\lfloor j/2 \rfloor \le q - 1$, so the increment is at most $K (n+1)^{q-1}$ in absolute value, where $K = \max_{j<m} B_j \sum_{j \le m-2}\binom{m}{j}|M_{m-j}|$. For $m = 1$ the sum is empty and $K = 0$. Since $a_m(0) = 0$,

$$
|a_m(n)| \le K \sum_{t=0}^{n-1} (t+1)^{q-1} \le K\thinspace  n\thinspace  (n+1)^{q-1} \le K (n+1)^q. \qquad\blacksquare
$$

**Consequence** [`rate_of_sum`, `remainder_order`]. Apply the lemma with $W_i = Z_i$ and with $W_i = A_i$. Since $U_n = T_n/n$ for $W = A$ and $V_n = T_n/n$ for $W = Z$, for $n \ge 1$

$$
E U_n^{2k} \le \frac{B_{2k}(n+1)^k}{n^{2k}} \le \frac{2^k B_{2k}}{n^k},
\qquad\text{so}\qquad
E U_n^{2k} = O(n^{-k}),\quad E V_n^{2k} = O(n^{-k}).
$$

In particular $E U_n^8, E V_n^8 = O(n^{-4})$ and $E V_n^{16} = O(n^{-8})$. Since $(u - v^2)^8 \le 128(u^8 + v^{16})$ [`sub_sq_pow_eight_le`], we get $E D_n^8 \le 128(E U_n^8 + E V_n^{16}) = O(n^{-4})$.

## 4. Second order moments of $D_n$ and $\Delta_n$

**Cauchy Schwarz** [`E_mul_sq_le`, `isBigO_E_mul`]. $(E[XY])^2 \le E X^2\thinspace  E Y^2$. So if $E X^2 = O(n^{-a})$ and $E Y^2 = O(n^{-b})$, then $E[XY] = O(n^{-(a+b)/2})$. With Step 3 this gives

{{< math >}}
$$
\begin{aligned}
|E[U V^4]| &\le (E U^2\thinspace  E V^8)^{1/2} = O(n^{-5/2}), & |E V^6| &\le (E V^4\thinspace  E V^8)^{1/2} = O(n^{-3}),\\
|E[U^3 V^2]| &\le (E U^6\thinspace  E V^4)^{1/2} = O(n^{-5/2}), & E[U^2 V^4] &\le (E U^4\thinspace  E V^8)^{1/2} = O(n^{-3}),\\
|E[U V^6]| &\le (E[U^2V^4]\thinspace  E V^8)^{1/2} = O(n^{-7/2}), & E V^8 &= O(n^{-4}),
\end{aligned}
$$
{{< /math >}}

so all of these are $o(n^{-2})$.

**Moments of $D_n$** [`derived_moments`]. Expanding powers of $D = U - V^2$ and using Step 2:

{{< math >}}
$$
\begin{aligned}
E D_n &= E U - E V^2 = -\tfrac1n,\\
E D_n^2 &= E U^2 - 2E[UV^2] + E V^4 = \tfrac{\lambda_4 - 1}{n} - \tfrac{2(\lambda_4 - 1)}{n^2} + \tfrac{3}{n^2} + o(n^{-2}),\\
E D_n^3 &= E U^3 - 3E[U^2V^2] + 3E[UV^4] - E V^6 = \tfrac{\lambda_6 - 6\lambda_4 - 6\lambda_3^2 + 5}{n^2} + o(n^{-2}),\\
E D_n^4 &= E U^4 - 4E[U^3V^2] + 6E[U^2V^4] - 4E[UV^6] + E V^8 = \tfrac{3(\lambda_4 - 1)^2}{n^2} + o(n^{-2}).
\end{aligned}
$$
{{< /math >}}

**Moments of $\Delta_n$** [`derived_moments`]. Since $\Delta_n = (c_n - 1) + c_n D_n$, each $E\Delta_n^k$ is an exact combination of $E D_n^j$ with coefficients polynomial in $c_n$. For $n \ge 2$, $c_n - 1 = \frac1{n-1} = \frac{c_n}{n}$ and $c_n = 1 + O(1/n)$. This gives:

* $E\Delta_n = c_n(1 + E D_n) - 1 = c_n \frac{n-1}{n} - 1 = 0$.
* $E\Delta_n^2 = (c_n-1)^2 + 2(c_n-1)c_n E D_n + c_n^2 E D_n^2 = c_n^2\big(E D_n^2 - \frac1{n^2}\big)$. With $c_n^2 = 1 + \frac2n + O(n^{-2})$ this is $\frac{\lambda_4 - 1}{n} + \frac{2}{n^2} + o(n^{-2})$.
* $E\Delta_n^3 = E D_n^3 + 3(c_n - 1) E D_n^2 + O(n^{-3}) = \frac{\lambda_6 - 3\lambda_4 - 6\lambda_3^2 + 2}{n^2} + o(n^{-2})$.
* $E\Delta_n^4 = E D_n^4 + O(n^{-3}) = \frac{3(\lambda_4 - 1)^2}{n^2} + o(n^{-2})$.

In Lean, each leftover rational error is written exactly as $c_n^k P_k(1/n)/n^3$ for an explicit polynomial $P_k$. That error is $o(n^{-2})$ because $(c_n, 1/n) \to (1, 0)$ [`bdd_cu`, `o_of_bdd_div_n3`].

**Rates** [`moment_bounds`]. $E D_n^4, E\Delta_n^4 = O(n^{-2})$ from the expansions above, $E D_n^8 = O(n^{-4})$ from Step 3, and $E\Delta_n^8 \le 128\big((c_n-1)^8 + c_n^8 E D_n^8\big) = O(n^{-4})$ because $(a+b)^8 \le 128(a^8 + b^8)$ [`add_pow_eight_le`].

## 5. Taylor expansion of the square root with exact remainder

Let $x \ge -1$ and $\delta = \sqrt{1 + x} - 1$, so $(1 + \delta)^2 = 1 + x$.

**Exact identity** [`taylorSqrt4`]. With $T_4(x) = 1 + \frac{x}{2} - \frac{x^2}{8} + \frac{x^3}{16} - \frac{5x^4}{128}$,

$$
1 + \delta - T_4(x) = \Big(\tfrac78 + \tfrac78\delta + \tfrac5{16}\delta^2 + \tfrac5{128}\delta^3\Big)\delta^5 .
$$

This follows by substituting $x = 2\delta + \delta^2$ and expanding.

**Domination** [`abs_sqrt_one_add_sub_one_le`]. With $s = \sqrt{1+x} \ge 0$, we have $|x| = |s^2 - 1| = |s - 1|(s + 1) \ge |s - 1|$, so $|\delta| \le |x|$. Hence $E\delta^{2k} \le E x^{2k}$ [`isBigO_mom_of_abs_le`].

**Remainder in expectation** [`taylor_remainder_E_small`]. Suppose $E x_n^4 = O(n^{-2})$ and $E x_n^8 = O(n^{-4})$. Then $E\delta_n^4 = O(n^{-2})$ and $E\delta_n^8 = O(n^{-4})$, and by Cauchy Schwarz

$$
E\delta^6 = O(n^{-3}),\qquad |E\delta^5| \le (E\delta^4 E\delta^6)^{1/2} = O(n^{-5/2}),\qquad |E\delta^7| \le (E\delta^6 E\delta^8)^{1/2} = O(n^{-7/2}).
$$

Taking expectations in the exact identity,

$$
E(1 + \delta_n) - E\thinspace T_4(x_n) = \tfrac78 E\delta_n^5 + \tfrac78 E\delta_n^6 + \tfrac5{16}E\delta_n^7 + \tfrac5{128}E\delta_n^8 = o(n^{-2}).
$$

By Step 4, both $x_n = D_n$ (with $\delta_n = \sqrt{1+D_n}-1$) and $x_n = \Delta_n$ (with $\delta_n = \sqrt{1+\Delta_n}-1$) satisfy the hypotheses.

## 6. Expectation and MSE of $\sigma\sqrt{1 + x_n}$

**Expectation** [`E_sqrt_expansion`]. From Step 5,

$$
E\big[\sigma\sqrt{1+x_n}\big] = \sigma\Big(1 + \tfrac12 E x_n - \tfrac18 E x_n^2 + \tfrac1{16} E x_n^3 - \tfrac5{128} E x_n^4\Big) + o(n^{-2}).
$$

**MSE** [`MSE_sqrt_expansion`]. Since $(1+\delta)^2 = 1 + x$,

$$
E\big[(\sigma(1+\delta) - \sigma)^2\big] = \sigma^2\big(E[1 + x] - 2E(1+\delta) + 1\big)
= \sigma^2\Big(\tfrac14 E x_n^2 - \tfrac18 E x_n^3 + \tfrac5{64}E x_n^4\Big) + o(n^{-2}),
$$

where the last step substitutes $E(1+\delta) = E\thinspace T_4(x) + o(n^{-2})$.

## 7. Assembling the four expansions

**$\hat\sigma_n$, with $x = D_n$** [`E_sigmaHat_formula`, `MSE_sigmaHat_formula`]. Insert the Step 4 moments of $D_n$:

* $E(\hat\sigma_n)/\sigma$: the $1/n$ term is $-\frac12 - \frac{\lambda_4 - 1}{8} = -\frac{\lambda_4 + 3}{8}$. The $1/n^2$ term, in units of $\frac1{128}$, is $16(2\lambda_4 - 5) + 8(\lambda_6 - 6\lambda_4 - 6\lambda_3^2 + 5) - 15(\lambda_4 - 1)^2 = 8\lambda_6 - 15\lambda_4^2 + 14\lambda_4 - 48\lambda_3^2 - 55$.
* $MSE(\hat\sigma_n)/\sigma^2$: the $1/n$ term is $\frac{\lambda_4 - 1}{4}$. The $1/n^2$ term, in units of $\frac1{64}$, is $16(5 - 2\lambda_4) - 8(\lambda_6 - 6\lambda_4 - 6\lambda_3^2 + 5) + 15(\lambda_4 - 1)^2 = 48\lambda_3^2 + 15\lambda_4^2 - 14\lambda_4 - 8\lambda_6 + 55$.

**$S_n$, with $x = \Delta_n$** [`E_Sn_formula`, `MSE_Sn_formula`]. Insert the Step 4 moments of $\Delta_n$; note $E\Delta_n = 0$:

* $E(S_n)/\sigma$: the $1/n$ term is $-\frac{\lambda_4 - 1}{8}$. The $1/n^2$ term, in units of $\frac1{128}$, is $-32 + 8(\lambda_6 - 3\lambda_4 - 6\lambda_3^2 + 2) - 15(\lambda_4 - 1)^2 = 8\lambda_6 - 15\lambda_4^2 + 6\lambda_4 - 48\lambda_3^2 - 31$.
* $MSE(S_n)/\sigma^2$: the $1/n$ term is $\frac{\lambda_4 - 1}{4}$. The $1/n^2$ term, in units of $\frac1{64}$, is $32 - 8(\lambda_6 - 3\lambda_4 - 6\lambda_3^2 + 2) + 15(\lambda_4 - 1)^2 = 48\lambda_3^2 + 15\lambda_4^2 - 6\lambda_4 - 8\lambda_6 + 31$.

By Step 1, these are the expansions of $E(\hat\sigma_n)$, $MSE(\hat\sigma_n)$, $E(S_n)$ and $MSE(S_n)$. $\blacksquare$

## 8. Corollaries

**MSE difference** [`MSE_diff_formula`]. Subtracting the two MSE expansions, the $1/n$ terms cancel, and the $1/n^2$ coefficients differ by $\frac{\sigma^2}{64}\big((-6\lambda_4 + 31) - (-14\lambda_4 + 55)\big) = \frac{\sigma^2}{64}(8\lambda_4 - 24)$. Therefore

$$
MSE(S_n) - MSE(\hat\sigma_n) = \frac{\sigma^2(\lambda_4 - 3)}{8n^2} + o(n^{-2}).
$$

**Threshold at $\lambda_4 = 3$** [`MSE_eq_at_kurtosis_three`, `MSE_leading_diff_pos_of_kurtosis_gt_three`, `MSE_leading_diff_neg_of_kurtosis_lt_three`]. The leading difference vanishes exactly when $\lambda_4 = 3$. It is positive for $\lambda_4 > 3$, where $\hat\sigma_n$ has smaller MSE, and negative for $\lambda_4 < 3$, where $S_n$ has smaller MSE.

**Shared expansion at $\lambda_4 = 3$** [`MSE_Sn_at_kurtosis_three`, `E_Sn_at_kurtosis_three`]. Substituting $\lambda_4 = 3$ gives

$$
MSE(S_n) = \frac{\sigma^2}{2n} + \frac{\sigma^2}{16n^2}\left(12\lambda_3^2 - 2\lambda_6 + 37\right) + o(n^{-2}),
$$

$$
E(S_n) = \sigma - \frac{\sigma}{4n} + \frac{\sigma}{32n^2}\left(2\lambda_6 - 12\lambda_3^2 - 37\right) + o(n^{-2}).
$$

**Normal case** ($\lambda_3 = 0$, $\lambda_4 = 3$, $\lambda_6 = 15$) [`E_Sn_normal`, `MSE_Sn_normal`, `MSE_sigmaHat_normal`]. This gives

$$
E(S_n) = \sigma - \frac{\sigma}{4n} - \frac{7\sigma}{32n^2} + o(n^{-2}),
\qquad
MSE(S_n),\ MSE(\hat\sigma_n) = \frac{\sigma^2}{2n} + \frac{7\sigma^2}{16n^2} + o(n^{-2}).
$$

As a check, $E(\hat\sigma_n) = \sqrt{\frac{n-1}{n}}\thinspace E(S_n) = \sigma - \frac{3\sigma}{4n} - \frac{7\sigma}{32n^2} + o(n^{-2})$, which agrees with the general $E(\hat\sigma_n)$ formula at these values.

## Remarks

* **Moments actually used.** Step 3 needs $E V_n^{16}$, so the argument uses moments of $X$ up to order 16. "All moments finite" is assumed only to keep the integrability bookkeeping simple.
* **What Lean adds.** Every identity and inequality above, including the polynomial algebra in Steps 2, 4 and 7 and the asymptotic bookkeeping, is checked by Lean's kernel. The final theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
