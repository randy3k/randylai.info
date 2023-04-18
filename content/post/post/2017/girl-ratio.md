---
title: Girl ratio
date: 2017-09-10
categories: Statistics
tags: 
    - Statistics
    - Probability
math: true
---

[https://stats.stackexchange.com/questions/93830/expected-number-of-ratio-of-girls-vs-boys-birth]()

> The Zorganian Republic has some very strange customs. Couples only wish to have female children as only females can inherit the family's wealth, so if they have a male child they keep having more children until they have a girl. If they have a girl, they stop having children. What is the ratio of girls to boys in Zorgania?


Let $X$ be the number of children in a family, it is geometric random variable with $p=0.5$, i.e.,
$$
P(X = x) = 0.5^x, x=1,2,3...
$$
which implies $E(X) = 2$

Suppose there are $N$ families in the country, the girl ratio is
$$
 \frac{N}{ \sum X_i}
$$

Since $\sum X_i /N \rightarrow E(X) = 2$ (law of large number), the ratio coverages to 1/2 if $N \rightarrow \infty$.


If there are only finite families, let $T$ be the total number of children of the country: $T = \sum X_i$, then $T$ has a negative binomial distribution with pmf

$$
P(T=t) = C^{t-1}_{N-1}  0.5^t, t = N, N+1...
$$

It implies
$$
E\left[ \frac{N}{\sum X_i} \right] = E\left[ \frac{N}{T} \right]  = \sum_{t=N}^{\infty} \frac{N}{t} C^{t-1}_{N-1} 0.5^t  = {_2F_1} (N, 1, N+1, -1)
$$
where $_2F_1$ is the hypergeometric function.

Therefore the expected girl ratio is ${_2F_1} (N, 1, N+1, -1)$.
