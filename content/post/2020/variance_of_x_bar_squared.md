---
title: Variance of sample mean squared
date: 2020-08-01
categories: Statistics
tags: 
    - Statistics
    - Probability
math: true
---


It is well known that $\bar X^2$ is a biased estimator for $\mu^2$, but a little is known to its variance.

While working on [a previous post]({{< ref "mse_of_sample_variance.md" >}}), we have to compute $E[(\sum X_i)^4]$, it gives a way to find $Var(\bar X^2)$.

Before we start working on $Var(\bar X^2)$, let's recall that $\bar X$ is an unbiased estimator for $\mu$, i.e. $E(\bar X) = \mu$. Moreover, $Var(\bar X) = \sigma^2/n$ and $E(\bar X^2) = Var(\bar X) + E(\bar X)^2 = \frac{\sigma^2}{n} + \mu^2$.

Now, consider 

<span>
$$
\begin{align}
E[(\sum X_i)^4] &= E[\sum X_i^4 + 4 \sum_{i \ne j} X_i^3 X_j + 3 \sum_{i \ne j} X_i^2 X_j^2 + 6 \sum_{i \ne j \ne k} X_i^2 X_j X_k +  \sum_{i \ne j \ne k \ne l} X_i X_j X_k X_l ]\\
&= n E(X^4) + 4 n(n-1)E(X^3) E(X) + 3n(n-1) (EX^2)^2 + \\
 & \quad\quad  6 n(n-1)(n-2) E(X^2) (EX)^2 + n(n-1)(n-2)(n-3) (EX)^4\\
\end{align}
$$
</span>

By using the fact that,

<span>
$$
\begin{align}
E(X^2) &= \sigma^2 + \mu^2\\
E(X^3) &= \gamma \sigma^3 + 3 \sigma^2 \mu + \mu^3\\
E(X^4) &= \kappa \sigma^4 + 4 \gamma \sigma^3 \mu + 6 \sigma^2 \mu^2 + \mu^4
\end{align}
$$
</span>
We have
<span>
$$
E[(\sum X_i)^4] = n^4 \mu^4 + 6n^3 \sigma^2 \mu^2 + 4n^2 \gamma \sigma^3 \mu + n(3n +\kappa-3)\sigma^4
$$
<span>
and
<span>
$$
Var[\bar X^2] = \frac{E[(\sum X_i)^4]}{n^4} - [E(\bar X^2)]^2 = \frac{4}{n} \sigma^2 \mu^2 + \frac{4\gamma}{n^2} \sigma^3 \mu + \frac{(2n+\kappa-3)}{n^3} \sigma^4.
$$
<span>