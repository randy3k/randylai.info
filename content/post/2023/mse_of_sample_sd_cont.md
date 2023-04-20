---
title: MSE of sample standard deviation (cont')
date: 2023-04-20
categories: Statistics
tags: 
    - Statistics
    - Probability
math: true
---


Continue our [previous]({{< ref "/post/2023/mse_of_sample_sd" >}}) post of computing the MSE of sample standard deviation. We want to have higher order expansion of $E(S_n)$. The algebric computation is a bit tedious, we will use [sympy](https://www.sympy.org/) to help us.


<font style="font-size: small"><a href="/post/2023/sample_sd_bias.html" target="_blank">Open notebook in full screen.</a></font>
 <iframe
       src="/post/2023/sample_sd_bias.html"
       width="100%"
       height="1000px"
       style="border:none;">
 </iframe>

The result is quite interesting. For normal distribution, the MSE of $S_n$ and $\hat \sigma$ are the same up to the order $1/n^2$.
If the distribution has a thicker tail than normal, i.e. kurtosis > 3, then $\hat \sigma_n$ will have a smaller MSE than $S_n$. On the other hand, if the distribution has a lighter tail than normal, than $S_n$ will have a smaller MSE. 

