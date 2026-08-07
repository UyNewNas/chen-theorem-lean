# 陈氏定理证明参考 (Chen's Theorem Proof Reference)

> 本文档基于 Liu (2022) 论文 "A Corrected Simplified Proof of Chen's Theorem" (arXiv:2203.07871) 编写,
> 用于指导 Lean 形式化工作。陈氏定理断言:对充分大的偶数 $N$,存在素数 $p$ 使得 $N-p$ 至多有两个素因子
> (即 $N = p + P_2$)。

## 论文信息

- Chen, J.R. (1973), "On the representation of a large even integer as the sum of a prime and the product of at most two primes", *Sci. Sinica* 16, 157-176
- Liu, Z. (2022), "A Corrected Simplified Proof of Chen's Theorem", arXiv:2203.07871
- Pan, C.D., Wang, Y., Ding, X.X. (1975), *Sci. Sinica* 18(5), 599-610

## 证明结构概览

证明遵循以下结构:

1. **$W(N)$ 下界**(经 Jurkat-Richert 定理): $W(N) \geq 2.6408\, \mathfrak{S}(N)\, N/\log^2 N$
2. **$\Omega$ 上界**(经 Selberg 筛 + 大筛法): $\Omega \leq 3.9404\, \mathfrak{S}(N)\, N/\log^2 N$
3. **关键不等式**:

$$
W(N) - \Omega/2 \geq \left(2.6408 - \frac{3.9404}{2}\right) \mathfrak{S}(N)\, \frac{N}{\log^2 N}
= 0.6706\, \mathfrak{S}(N)\, \frac{N}{\log^2 N} > 0
$$

由于 $W(N) - \Omega/2 > 0$,故存在 $p$ 使 $N-p$ 至多有两个素因子,从而 $N = p + P_2$。

## 核心定义

### $W(N)$ — 主项计数

$W(N)$ 为满足以下条件的素数 $p$ 的个数:
- $N - p$ 没有不超过 $N^{1/10}$ 的素因子;
- $N - p$ 在区间 $(N^{1/10},\, N^{1/3}]$ 内至多有一个素因子。

形式化地,

$$
W(N) = \#\left\{ p \leq N : p \text{ 素数},\ \, N-p \text{ 的最小素因子} > N^{1/10},\ \, \omega_{(N^{1/10},\, N^{1/3}]}(N-p) \leq 1 \right\}.
$$

### $\Omega$ — 转换和 (switched sum)

$$
\Omega = \sum_{a}\, \sum_{\substack{a p_3 \leq N \\ N - a p_3 \text{ 素数}}} f(a)
$$

其中 $f(a)$ 为下文定义的特征函数。$\Omega$ 统计的是 $N - p$ 恰有两个素因子 $p_1, p_2$ 落在"危险区间"内的情形,需从 $W(N)$ 中扣除。

### $f(a)$ — 双素数乘积特征函数

$f(a)$ 是 $a = p_1 p_2$ 的特征函数,其中素因子满足

$$
N^{1/10} < p_1 \leq N^{1/3} < p_2 \leq (N/p_1)^{1/2}.
$$

即

$$
f(a) = \begin{cases}
1, & \text{若 } a = p_1 p_2,\ N^{1/10} < p_1 \leq N^{1/3} < p_2 \leq (N/p_1)^{1/2}, \\
0, & \text{其他}.
\end{cases}
$$

### 奇异级数 $\mathfrak{S}(N)$

$$
\mathfrak{S}(N) = \prod_{\substack{p \mid N \\ p > 2}} \frac{p-1}{p-2} \cdot \prod_{p > 2} \left(1 - \frac{1}{(p-1)^2}\right)
$$

当 $N$ 为偶数时 $\mathfrak{S}(N) \geq \mathfrak{S}(2) > 0$;当 $N$ 为奇数时 $\mathfrak{S}(N) = 0$。

## 关键引理

### Lemma 1 (Mertens 和的界)

**命题.** 对固定的 $0 < \alpha < \beta$,

$$
\sum_{x^\alpha < p \leq x^\beta} \frac{1}{p}
$$

有界(关于 $x$ 趋于无穷)。

**证明.** 由 Mertens 第二定理,

$$
\sum_{p \leq t} \frac{1}{p} = \log\log t + M + O(1/\log t),
$$

故

$$
\sum_{x^\alpha < p \leq x^\beta} \frac{1}{p}
= \log\log(x^\beta) - \log\log(x^\alpha) + O(1/\log x)
= \log(\beta/\alpha) + O(1/\log x).
$$

特别地,当 $\alpha, \beta$ 固定时该和趋于常数 $\log(\beta/\alpha)$。$\square$

### Lemma 2 (除数和界)

**命题.** 对 $A > 0$ 及 $n \geq 1$,

$$
\sum_{d \mid n} \frac{\mu^2(d)\, A^{\omega(d)}}{\varphi(d)} \ll (\log\log 3n)^A.
$$

若 $n$ 是互不相同的素数(均 $\leq y$)之积,则

$$
\sum_{d \mid n} \frac{\mu^2(d)\, A^{\omega(d)}}{\varphi(d)} \ll (\log y)^A.
$$

**注.** 此引理用于控制 $\sum_{d \mid Q} 3^{\omega(d)}/\varphi(d)$,其中 $Q$ 为不超过 $z'$ 的素数之积,得到 $\ll (\log N)^3$。

### Lemma 3 (Selberg 筛权重)

**命题.** 设 $Q$ 为所有满足 $p \leq z' = N^{1/4 - \varepsilon/2}$ 且 $p \nmid N$ 的素数之积。则存在 $\lambda_d$ 满足:

1. $\lambda_1 = 1$;
2. 当 $d > z'$ 或 $d \nmid Q$ 时 $\lambda_d = 0$;
3. $|\lambda_d| \leq 1$;

且

$$
\sum_{d_1, d_2} \frac{\lambda_{d_1} \lambda_{d_2}}{\varphi([d_1, d_2])} = \bigl[8 + O(\varepsilon)\bigr]\, \frac{\mathfrak{S}(N)}{\log N}.
$$

**注.** 常数 8 来自 Selberg 筛的对角项 $\sum_d \lambda_d^2 / \varphi(d) \approx 1/G(z', z')$,其中 $G$ 为筛函数,在 $s \approx 2$ 时 $1/G \approx 8$。

### Lemma 4 (数值积分界)

**命题.** 对充分大的 $N$,

$$
\sum_{a} \frac{f(a)}{a\, \log(N/a)} \leq \frac{0.49254}{\log N}.
$$

**证明.** 将求和化为二重积分。由 $f(a) \neq 0$ 知 $a = p_1 p_2$ 且

$$
N^{1/10} < p_1 \leq N^{1/3}, \qquad N^{1/3} < p_2 \leq (N/p_1)^{1/2}.
$$

令 $\alpha = \log p_1 / \log N$, $\beta = \log p_2 / \log N$,则

$$
\frac{1}{10} < \alpha \leq \frac{1}{3}, \qquad \frac{1}{3} < \beta \leq \frac{1-\alpha}{2}.
$$

由素数定理 $\sum_{N^\alpha < p \leq N^{\alpha + d\alpha}} 1/p \approx d\alpha/\alpha$,求和转化为

$$
\frac{1}{\log N} \int_{1/10}^{1/3} \frac{d\alpha}{\alpha} \int_{1/3}^{(1-\alpha)/2} \frac{d\beta}{\beta(1-\alpha-\beta)} < \frac{0.49254}{\log N}.
$$

数值积分给出上界 $0.49254$(Chen 1973, eq. 28)。$\square$

## $\Omega$ 的估计 (Section III)

$\Omega$ 的上界通过 Selberg 上界筛法得到,步骤如下:

**第 1 步.** 用与 $Q$ 的互素性截断内层计数:

$$
\Omega \leq \sum_{a} f(a) \sum_{\substack{a p \leq N \\ (N - a p,\, Q) = 1}} 1 + N^{2/3}\, z
$$

其中 $N^{2/3} z$ 为截断误差(来自 $a > N^{2/3}$ 或 $p$ 过大情形)。

**第 2 步.** 对内层和套用 Selberg 上界筛(以 $\lambda_d$ 为权重):

$$
\Omega \leq \sum_{a} f(a) \sum_{a p \leq N} \left(\sum_{d} \lambda_d\right)^2 + N^{11/12}
$$

此处 $N^{11/12}$ 为 Selberg 筛的余项(来自 $d > N^{1/2-\varepsilon}$ 的贡献,因 $z' = N^{1/4-\varepsilon/2}$, $[d_1,d_2] \leq N^{1/2-\varepsilon}$)。

**第 3 步.** 展开平方,主项与余项分离:

$$
\Omega = M + N^{11/12}, \qquad M = M_1 + R
$$

其中

$$
M_1 = \sum_{d_1, d_2} \lambda_{d_1} \lambda_{d_2} \sum_{a} f(a) \sum_{\substack{a p \leq N \\ [d_1,d_2] \mid N - a p}} 1,
$$

$$
R = \sum_{d_1, d_2} \lambda_{d_1} \lambda_{d_2} \sum_{a} f(a) \left( \pi(N; a, [d_1,d_2], N) - \text{主项} \right).
$$

**第 4 步.** 主项估计。由素数定理(在等差数列上取平均),

$$
\sum_{\substack{a p \leq N \\ [d_1,d_2] \mid N - a p}} 1 \approx \frac{\operatorname{li}(N/a)}{\varphi([d_1,d_2])},
$$

故

$$
M_1 \leq \bigl[8 + O(\varepsilon)\bigr]\, \frac{\mathfrak{S}(N)}{\log N} \cdot \sum_{a} \frac{f(a)\, \operatorname{li}(N/a)}{1}
\leq \bigl[8 + O(\varepsilon)\bigr]\, \frac{\mathfrak{S}(N)}{\log N} \cdot 0.49254\, \frac{N}{\log N}
$$

(最后一步用 Lemma 4 及 $\operatorname{li}(N/a) \approx N/(a \log(N/a))$)。因此

$$
M_1 \leq 3.94033\, \mathfrak{S}(N)\, \frac{N}{\log^2 N}.
$$

**第 5 步.** 余项形式:

$$
|R| \leq \sum_{\substack{d \mid Q \\ d \leq N^{1/2 - \varepsilon}}} 3^{\omega(d)}\, \left| \sum_{a} f(a)\, \Delta(N; a, d, N) \right|
$$

其中 $\Delta(N; a, d, N) = \pi(N; a, d, N) - \operatorname{li}(N/a)/\varphi(d)$ 为等差数列素数计数的误差。$R$ 的精细估计是 Liu 修正的核心(见下节)。

## 误差项 $R$ 的修正 (Section IV — Liu 的修正)

> **这是本文的关键创新。** Pan, Wang, Ding (1975) 错误地假设 $f(a) \neq 0$ 蕴含 $(a, d) = 1$,
> 从而认为 $R$ 可直接由 Bombieri-Vinogradov 型定理控制。Liu (2022) 指出该假设不成立
> (因 $a = p_1 p_2$ 且 $p_1$ 可能整除 $d$),并给出完整修正。

**第 1 步. 分裂 $R$。** 将 $R$ 按 $(a, d)$ 是否等于 1 分裂:

$$
R = R^{(=1)} + R_1,
$$

其中 $R^{(=1)}$ 为 $(a, d) = 1$ 部分(由 Pan 的定理/Bombieri-Vinogradov 控制,$\ll N/\log^A N$),$R_1$ 为 $(a, d) > 1$ 部分。

**第 2 步. 利用 $(a, d) > 1$ 时 $\pi$ 退化。** 由于 $(a, d) > 1$ 时等差数列 $N - a p \equiv 0 \pmod{d}$ 至多有一个素数解($p$ 唯一),

$$
R_1 \ll \sum_{d \mid Q} \frac{3^{\omega(d)}}{\varphi(d)} \cdot \max \sum_{\substack{a \\ (a, d) > 1}} f(a)\, \operatorname{li}(N/a).
$$

**第 3 步. 控制外层和(用 Lemma 2)。** 因 $Q$ 为 $\leq z' = N^{1/4 - \varepsilon/2}$ 的素数之积,

$$
\sum_{d \mid Q} \frac{3^{\omega(d)}}{\varphi(d)} \ll (\log N)^3.
$$

**第 4 步. 估计内层和。** 由 $f(a) \neq 0 \Rightarrow a \leq N^{2/3}$(因 $p_2 \leq (N/p_1)^{1/2} \leq N^{1/2}$, $p_1 \leq N^{1/3}$, 故 $a = p_1 p_2 \leq N^{5/6}$,实际更紧),且 $(a, d) > 1$ 当且仅当 $p_1 \mid d$ 或 $p_2 \mid d$。主要贡献来自 $p_1 \mid d$(因 $p_1 \leq N^{1/3} < z'$,可能整除 $d$;而 $p_2 > N^{1/3}$ 也可能):

$$
\sum_{\substack{a \\ (a, d) > 1}} \frac{f(a)}{a}
\leq \sum_{\substack{p_1 \mid d \\ p_1 > N^{1/10}}} \frac{1}{p_1} \sum_{p_2 > N^{1/3}} \frac{1}{p_2}.
$$

**第 5 步. 内层 $p_2$ 和(用 Lemma 1)。** 取 $\alpha = 1/3$, $\beta = 4/10$(或更紧的上界),

$$
\sum_{p_2 > N^{1/3}} \frac{1}{p_2} \leq \sum_{N^{1/3} < p_2 \leq N^{4/10}} \frac{1}{p_2} + O(1) \quad \text{有界}.
$$

由 Lemma 1,该和 $\ll 1$(收敛于 $\log(4/10 \div 1/3) = \log(6/5)$,尾部亦收敛)。

**第 6 步. 外层 $p_1$ 和。** 利用分部求和与 $p_1 > N^{1/10}$:

$$
\sum_{\substack{p_1 \mid d \\ p_1 > N^{1/10}}} \frac{1}{p_1}
< \frac{10\, N^{-1/10}}{\log N} \sum_{p \mid d} \log p
\ll N^{-1/10}.
$$

(此处用到 $1/p < N^{-1/10}$ 及 $\sum_{p \mid d} \log p \leq \log d \leq \log z' \ll \log N$。)

**第 7 步. 合成 $R_1$ 的界。** 综合第 2–6 步,

$$
R_1 \ll (\log N)^3 \cdot N^{-1/10} \cdot \operatorname{li}(N)
\ll N^{9/10}\, \log^2 N.
$$

**第 8 步. $\Omega$ 的完整界。** 合并主项与所有余项:

$$
\Omega \leq 3.94033\, \mathfrak{S}(N)\, \frac{N}{\log^2 N}
+ O\!\left( \frac{N}{\log^A N} + N^{9/10}\, \log^2 N + N^{11/12} \right).
$$

对充分大的 $N$,余项 $o(N/\log^2 N)$ 可吸收,故

$$
\Omega \leq 3.9404\, \mathfrak{S}(N)\, \frac{N}{\log^2 N}.
$$

结合 $W(N) \geq 2.6408\, \mathfrak{S}(N)\, N/\log^2 N$,得

$$
W(N) - \frac{\Omega}{2} \geq 0.6706\, \mathfrak{S}(N)\, \frac{N}{\log^2 N} > 0,
$$

即陈氏定理成立。$\square$

## Lean 形式化对应

下表将论文中的概念映射到 Lean 形式化中的模块与定义/定理:

| 论文概念 | Lean 模块 | Lean 定义/定理 | 状态 |
|---------|----------|--------------|------|
| $\mathfrak{S}(N)$ | `SingularSeries.lean` | `singularSeries` | 已完成 |
| $F(s), f(s)$ | `LinearSieve.lean` | `sieveFunctionF`, `sieveFunctionf` | 已完成 |
| Mertens 定理 | `MertensTheorem.lean` | `mertens_second_theorem` | sorry |
| Bombieri-Vinogradov 型逐参数接口 | `BombieriVinogradov.lean` | `bombieri_vinogradov` | 已完成（真正统一 BV 为 external） |
| $W(N)$ | `SwitchingPrinciple.lean` | `chenW` | 已完成 |
| $\Omega$ | `SwitchingPrinciple.lean` | `chenOmega` | 已完成 |
| 关键不等式 | `SwitchingPrinciple.lean` | `chen_key_inequality` | 已完成（需 `ChenAnalyticBounds`） |
| Lemma 3 (Selberg) | `SelbergUpperBound.lean` | `selberg_sieve_weights_exist` | 已完成（逐点余项接口） |
| Lemma 4 (积分) | `SelbergUpperBound.lean` | `lemma4_numerical_bound` | 已完成（逐点余项接口） |
| $M_1$ 界 | `SelbergUpperBound.lean` | `main_term_bound` | 已完成（逐点余项接口） |
| $R$ 界 | `SelbergUpperBound.lean` | `error_term_bound` | sorry |
| $\Omega$ 完整界 | `SelbergUpperBound.lean` | `chenOmega_complete_bound` | sorry |
| Lemma 1 | `MertensTheorem.lean` | `prime_reciprocal_sum_bounded` | sorry |
| Lemma 2 | `SelbergUpperBound.lean` | (待添加) | 待添加 |

## 关键数值常数

| 常数 | 值 | 含义 |
|------|---|------|
| $W(N)$ 下界系数 | $2.6408$ | 来自 Jurkat-Richert 定理($s \approx 5$) |
| $\Omega$ 上界系数 | $3.9404$ | $= 8 \times 0.49254 + \text{margin}$ |
| 主项系数 | $3.94033$ | $= 8 \times 0.49254$ |
| 数值积分界 | $0.49254$ | Chen 1973, eq. 28 |
| 关键差值 | $0.6706$ | $= 2.6408 - 3.9404/2$(为正!) |
| Selberg 对角系数 | $8$ | Selberg 筛 $s \approx 2$ 时的 $1/G$ |
| 孪生素数常数 | $C_2 \approx 0.66016$ | $\prod_{p>2}(1 - 1/(p-1)^2)$ |

**验证**: $8 \times 0.49254 = 3.94032 \approx 3.94033$;$2.6408 - 3.9404/2 = 2.6408 - 1.9702 = 0.6706 > 0$。

## 参数选择

| 参数 | 取值 | 作用 |
|------|------|------|
| $z$ | $N^{1/10}$ | 筛水平(线性筛下界) |
| $y$ | $N^{1/3}$ | 转换参数(switching principle) |
| $D$ | $N^{1/2 - \varepsilon}$ | 分布水平(来自 Bombieri-Vinogradov) |
| $s$ | $\log D / \log z \approx 5$ | 筛比 |
| $z'$ | $N^{1/4 - \varepsilon/2}$ | Selberg 筛水平 |

**参数关系说明**:

- 线性筛中取 $z = N^{1/10}$, $D = N^{1/2-\varepsilon}$,故 $s = \log D/\log z = (1/2-\varepsilon)/(1/10) = 5 - 10\varepsilon \approx 5$。
- 转换原理在 $N - p$ 于 $(N^{1/10}, N^{1/3}]$ 恰有一个素因子时,将其重写为 $a = p_1 p_2$ 的形式,$y = N^{1/3}$ 为转换阈值。
- Selberg 筛用于 $\Omega$ 的上界估计,取 $z' = N^{1/4-\varepsilon/2}$ 以保证 $[d_1, d_2] \leq (z')^2 = N^{1/2-\varepsilon} \leq D$,从而使余项可由分布水平控制。

---

*本文档随 Lean 形式化进度更新。状态列中"已完成"表示已有完整证明,"sorry"表示目标已声明但证明待补,"待添加"表示尚未声明。*
