---
title: Variance of sample mean squared
date: 2020-08-01
categories: Statistics
tags: 
    - Statistics
    - Probability
---

It is well known that $\bar X^2$ is a biased estimator for $\mu^2$, but a little is known to its variance.

Before we start working on $Var(\bar X^2)$, let's recall that $\bar X$ is an unbiased estimator for $\mu$, i.e. $E(\bar X) = \mu$. Moreover, $Var(\bar X) = \sigma^2/n$ and $E(\bar X^2) = Var(\bar X) + E(\bar X)^2 = \frac{\sigma^2}{n} + \mu^2$.

Let $Z_i = X_i - \mu$, 

<span>
$$
\begin{align*}
E\left[(\sum X_i)^4\right] &= E\left[(n \mu + \sum Z_i)^4\right]\\
&= E\left[[n^4 \mu^4 + 4 n^3 \mu^3 \sum Z_i+ 6 n^2 \mu^2 (\sum Z_i)^2 + 4 n \mu (\sum Z_i)^3  + (\sum Z_i)^4 \right].
\end{align*}
$$
</span>

By the fact that,

<span>
$$
\begin{align*}
E\left[\sum Z_i\right] &= 0\\
E\left[(\sum Z_i)^2\right] &= E(\sum Z_i^2 + \sum_{i\ne j} Z_i Z_j) = E(\sum Z_i^2) = n\sigma^2\\
E\left[(\sum Z_i)^3\right] &= E(\sum Z_i^3 + 3 \sum_{i\ne j} Z_i^2 Z_j + \sum_{i\ne j \ne k} Z_i Z_j Z_k) = n\gamma \sigma^3\\
E\left[(\sum Z_i)^4 \right] &= E[\sum Z_i^4 + 4 \sum_{i \ne j} Z_i^3 Z_j + 3 \sum_{i \ne j} Z_i^2 Z_j^2 + 6 \sum_{i \ne j \ne k} Z_i^2 Z_j Z_k +  \sum_{i \ne j \ne k \ne l} Z_i Z_j Z_k Z_l ] \\
&= E[\sum Z_i^4 + 3 \sum_{i \ne j} Z_i^2 Z_j^2] \\
&= n \kappa \sigma^4 + 3n(n-1) \sigma^4.
\end{align*}
$$
</span>

We have,
<span>
$$
E\left[(\sum X_i)^4\right] = n^4 \mu^4 + 6n^3 \sigma^2 \mu^2 + 4n^2 \gamma \sigma^2 \mu + n(3n + \kappa - 3) \sigma^4.
$$

$$
Var[\bar X^2] = \frac{E[(\sum X_i)^4]}{n^4} - [E(\bar X^2)]^2 = \frac{4}{n} \sigma^2 \mu^2 + \frac{4\gamma}{n^2} \sigma^3 \mu + \frac{(2n+\kappa-3)}{n^3} \sigma^4.
$$
</span>
