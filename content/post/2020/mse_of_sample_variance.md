---
title: Why unbaised estimator?
date: 2020-08-01
categories: Statistics
tags: 
    - Statistics
    - Probability
math: true
---

In introductory statistics courses, we often focus on unbiased estimators such as the sample variance,
$$
S^2 = \frac{\sum(X_i - \bar X)^2}{n - 1}
$$
rather than a more initiative estimator
$$
\hat \sigma^2 = \frac{\sum(X_i - \bar X)^2}{n}.
$$

The common argument is that $S^2$ is unbiased whereas $\hat \sigma^2$ is biased for estimating $\sigma^2$. While it is true, this statement is over-stressed. A more statistical way to evaluate performance of estimators is to compare the mean squared error (MSE) of the estimators. 

### Normal Population

If the population is normal, using the fact that
$\sum(X_i - \bar X)^2 / \sigma^2 \sim \chi^2_{n-1}$, one could conclude that $Var[\sum(X_i - \bar X)^2] = 2(n-1) \sigma^4$ thus
$$
MSE(S^2) = \frac{2 \sigma^4}{n-1}.
$$
and
$$
MSE(\hat \sigma^2) = Var(\hat \sigma^2) + Bias(\hat \sigma^2)^2 = \frac{2 (n-1) \sigma^4}{n^2} + \left[\frac{-\sigma^2}{n}\right]^2 = \frac{(2n-1) \sigma^4}{n^2}.
$$

As $MSE(\hat \sigma^2) < MSE(S^2)$, we conclude that $\hat \sigma^2$ is a better than estimator than $S^2$ for normal data.

### How about when the population is not normal?

There are a few online resources that have already covered this case.

- https://davegiles.blogspot.com/2013/05/whats-variance-of-sample-variance.html
- https://math.stackexchange.com/a/2476662/136006
- https://mathworld.wolfram.com/SampleVarianceDistribution.html

We need $Var\left[\sum(X_i - \bar X)^2\right]$ to compute $MSE(S^2)$ and $MSE(\hat \sigma^2)$ and
$$
Var\left[\sum(X_i - \bar X)^2\right] =  E\left[\left(\sum(X_i - \bar X)^2\right)^2\right] - (n-1)^2\sigma^4.
$$ 

Let $Z_i = X_i - \mu$, $\mu = E(X_i)$, $\sigma^2 = Var(X_i)$ and the kurtosis $\kappa = E Z_i^4/\sigma^4$,

<span>
$$
\begin{align}
E\left[\left(\sum(X_i - \bar X)^2\right)^2\right] &= E\left[\left( \sum (X_i-\mu)^2 - n (\bar X - \mu)^2 \right)^2\right] \\
&= E\left[\left( \sum Z_i^2 - n (\bar Z)^2 \right)^2\right] \\
&= E\left[(\sum Z_i^2)^2\right] - \frac{2}{n} E \left[ (\sum Z_i^2) (\sum Z_i)^2\right] + \frac{1}{n^2} E\left[(\sum Z_i)^4 \right].
\end{align}
$$
</span>

The first term

<span>
$$
E\left[(\sum Z_i^2)^2\right] = E\left[\sum Z_i^4 + \sum_{i\ne j} Z_i^2 Z_j^2 \right] = n \kappa \sigma^4 + n(n-1) \sigma^4.
$$
</span>

The second term,

<span>
$$
\begin{align}
E \left[ (\sum Z_i^2) (\sum Z_i)^2\right] &= E \left[ (\sum Z_i^2) (\sum Z_i^2 + \sum_{i\ne j} Z_i Z
_j)\right] \\
&=E \left[\sum Z_i^4 + \sum_{i\ne j} Z_i^2 Z_j^2 + \sum_k \sum_{i\ne j} Z_k Z_i Z_j \right] \\
&= n \kappa \sigma^4 + n(n-1) \sigma^4.
\end{align}
$$
</span>

The third term,

<span>
$$
\begin{align}
E\left[(\sum Z_i)^4 \right] &= E[\sum Z_i^4 + 4 \sum_{i \ne j} Z_i^3 Z_j + 3 \sum_{i \ne j} Z_i^2 Z_j^2 + 6 \sum_{i \ne j \ne k} Z_i^2 Z_j Z_k +  \sum_{i \ne j \ne k \ne l} Z_i Z_j Z_k Z_l ] \\
&= E[\sum Z_i^4 + 3 \sum_{i \ne j} Z_i^2 Z_j^2] \\
&= n \kappa \sigma^4 + 3n(n-1) \sigma^4.
\end{align}
$$
</span>


Therefore,

<span>
$$
\begin{align}
E\left[\left(\sum(X_i - \bar X)^2\right)^2\right] &= \frac{\sigma^4}{n} \left[(n^2 - 2n + 1) \kappa + n^2(n-1) - 2 n(n-1) + 3(n-1) \right] \\
&= \frac{(n-1)\sigma^4}{n} \left[(n-1) \kappa + n^2 - 2n + 3)\right]
\end{align}
$$
</span>
and
<span>
$$
\begin{align}
Var\left[\left(\sum(X_i - \bar X)^2\right)^2\right] &=  \frac{(n-1)\sigma^4}{n} \left[(n-1) \kappa + n^2 - 2n + 3)\right] - (n-1)^2 \sigma^4 \\
&= \frac{(n-1)\sigma^4}{n} \left[(n-1) \kappa - n + 3 \right].
\end{align}
$$
</span>


Finally,

$$
MSE(S^2) = \frac{\sigma^4}{n(n-1)} \left[(n-1) \kappa - n + 3 \right] = \sigma^4\left[\frac{\kappa}{n} - \frac{n-3}{n(n - 1)}\right]
$$
and
$$
MSE(\hat \sigma^2) = \frac{(n-1)\sigma^4}{n^3} \left[(n-1) \kappa - n + 3 \right] + \left[\frac{-\sigma^2}{n}\right]^2 =  \sigma^4\left[ \frac{(n-1)^2}{n^3} \kappa - \frac{n^2-5n + 3}{n^3}\right].
$$

Some algebra shows that $MSE(\hat \sigma^2) < MSE(S^2)$ for all $n$ when $\kappa > 1.5$. Most common distributions have kurtosises greater than 1.5. A noticeable exception is the Bernoulli distribution with $1/3<p<2/3$. Nevertheless, in practice, we don't directly estimate the variance of the Bernoulli distribution but to estimate $p$ directly.



### Conclusion

Unbiasedness shall not be used as the prime reason to use sample variance.
