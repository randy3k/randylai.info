---
title: MSE of sample standard deviation (Gen AI)
date: 2026-01-20
categories: Statistics
tags: 
    - Statistics
    - Probability
    - AI
---

In the era of gen AI, I am trying to use LLM to compute the second order expansion of [$MSE(S)$]({{< ref "/post/2023/mse_of_sample_sd_cont" >}}) that I did in 2023.

> The standard sample s.d. is given by  S=sqrt(\sum_{i=1}^n(x_i - \bar x)^2/ (n-1)). Without assumption the underlying distribution, compute the MSE(S) of it in terms of the first few moments of x_i up. Expand the terms up to 1/n^2.

And it just nails it: https://gemini.google.com/share/fa35ab43436f
