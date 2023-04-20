---
title: MSE of sample standard deviation
date: 2023-04-19
categories: Statistics
tags: 
    - Statistics
    - Probability
math: true
---


In a [previous]({{< ref "/post/2020/mse_of_sample_variance" >}}) post, we have discussed the MSE of sample variance. One could argue that we should compute the MSE of the sample standard deviation as sample s.d. has the same unit as the measurements.

Let $S_n$ be the sample s.d. and $\sigma$ be the true s.d., the goal is to compute

$$
MSE(S_n) = E(S_n-\sigma)^2 = E(S_n^2) - 2 \sigma E(S_n) + \sigma^2 = 2 \sigma^2 -  2 \sigma E(S_n).
$$

To compute $E(S_n)$, first, we consider Taylor's expanding $g(x) = \sqrt{x}$ about $x=\sigma^2$,
we have
$$
g(x) = \sigma + \frac{1}{2 \sigma}(x-\sigma^2) -  \frac{1}{8 \sigma^3}(x-\sigma^2)^2 + R(x),
$$
where $R(x) =- \left(\frac{1}{8 \tilde \sigma^3} - \frac{1}{8 \sigma^3}\right)(x-\sigma^2)^2$ for some  $\tilde \sigma$ between $\sqrt{x}$ and $\sigma$.



Let $\kappa = E(X - \mu)^4 / \sigma^4$ be the kurtosis.
It could be shown that $E\left[\sqrt{n}(S_n^2 - \sigma^2)\right]^2 \rightarrow \sigma^4(\kappa-1)$ and $n ER(S_n^2) \rightarrow 0$ (and the proofs are beyond the discussion of this post. One could consider the fact that $\sqrt{n}(S_n^2 - \sigma^2)$  converges to $N(0, \sigma^4(\kappa-1))$).

Thus,
$$
E(S_n) = Eg(S_n^2) =\sigma + \frac{1}{2 \sigma} E(S_n^2 - \sigma^2) - \frac{1}{8\sigma^3} E(S_n^2 - \sigma^2)^2 + o(n^{-1}).
$$
$$
 = \sigma - \frac{\sigma}{8}\left(\frac{\kappa - 1}{n}\right) + o(n^{-1}).
$$

Therefore, $MSE(S_n) = \frac{\sigma^2}{4}\left( \frac{\kappa - 1}{n}\right) + o(n^{-1})$.

Similar calculation could be done for $\hat \sigma_n = \sqrt{\frac{\sum(X_i - \bar X)^2}{n}}$,

<span>
$$
\begin{align}
MSE(\hat \sigma_n) & = E\left[ \sqrt{\frac{n-1}{n}} S_n - \sigma \right]^2 = 
E\left[\left(1 - \frac{1}{2n} + o(n^{-1})\right) S_n - \sigma\right]^2 \\
&= \frac{\sigma^2}{4}\left( \frac{\kappa - 1}{n}\right) + o(n^{-1}).
\end{align}
$$
</span>

Unfortunately, MSE of $S_n$ and $\hat \sigma_n$ match at the first order. We will need to consider higher order expansion next time.

