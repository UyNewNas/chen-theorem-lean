/-
! # Q1MainTermAbsorption (chen issue #37)

## 目标

证明 q¹ 主项吸收缝 `q1MainTermAbsorption` (SwitchingPrinciple.lean:6113):

    ∃ C₁ > 0, ∃ N₁, ∀ N ≥ N₁ Even N:
      q1MainTermSum N ≤ C₁·𝔖_trunc(N, z−1)·N/log²N

其中 z = correctedChenZ N, y = correctedChenY N,
P(N) = correctedChenSiftingProduct N (奇素数 r < z, r ∤ N),
F(N) = correctedChenForbiddenProduct N (r < z, r ≤ 2 ∨ r | N),
Fodd(N) = F(N)/2 (F 的奇素因子之积).

## 数学结构 (Halberstam--Richert Ch. 10 筛法主项, Chen 1973)

对固定 q ∈ [z, y) 素数, d | P, e | F:

  q1APMainValue N (lcm(lcm q d) e)
    = if Even (lcm(lcm q d) e) then [lcm(lcm q d) e | N−2] else li(N)/φ(lcm(lcm q d) e).

因 q, d, e 两两互素 (q ≥ z, P·F 的素因子 < z, P 与 Fodd 素因子不相交) 且均奇
(q, d 奇; e 奇 ⟺ e | Fodd), 故 lcm(lcm q d) e = q·d·e 且

  q1CandidateAPMain N q
    = li(N)·Σ_{d|P} Σ_{e|Fodd} μ(d)μ(e)/φ(q·d·e)  +  (偶数模数修正, ≤ 0).

奇数部分经 Möbius 欧拉积 (mathlib `prodPrimeFactors_one_sub_of_squarefree`)
分解为

  Σ_{d|P} μ(d)/φ(d) = ∏_{p|P} (1 − 1/(p−1)) =: q1SieveProduct N,
  Σ_{e|Fodd} μ(e)/φ(e) = ∏_{p|Fodd} (1 − 1/(p−1)) =: q1ForbiddenOddProduct N,

偶数部分精确为零或负值 (Möbius 反演 Σ_{d|m} μ(d) = [m = 1]):

  EvenPart = −[q | N−2]·[gcd(P, N−2) = 1]·[gcd(Fodd, (N−2)/2) = 1] ≤ 0.

故 (偶数 N 下 p = 2 自动被 p ∤ N 排除)

  q1MainTermSum N ≤ li(N)·goldbachSieveProduct(N, z)·Σ_{q∈[z,y)} 1/φ(q).

然后:
  - goldbachSieveProduct(N, z) = primeProduct(z−1)·𝔖_trunc(N, z−1)
    (MertensTheorem.sieveProduct_identity);
  - primeProduct(z−1) ≤ a₂/log(z−1), log(z−1) ≥ (1/20)·log N  (Mertens + 初等);
  - Σ_{q∈[z,y)} 1/φ(q) ≤ 2·Σ 1/q ≤ 2·(primeReciprocalSum y − primeReciprocalSum (z−1))
    ≤ 2·(log(log y/log z) + E) ≤ 2·(log 7 + E)  (ant primeReciprocalSum_range_le,
    以及 log y/log z ≤ 7, TripleMain.hTripleMain_log_y_div_log_z_le).

装配即得 q1MainTermAbsorption, C₁ = 20·a₂·(2·(log 7 + E)).

本节所有定理零 sorry/admit/axiom; 分析输入均为已核验定理
(ant primeReciprocalSum_range_le / goldbachNu / singularSeriesTruncated,
chen MertensTheorem.primeProduct_asymptotic_order / sieveProduct_identity,
TripleMain 的 log 参数界).
-/

import MathlibNt.SieveTheory.TripleMain

/-! # 记号与定义 -/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 1000000

noncomputable section

/-- q¹ 主项的对数积分: li(N) = N/log N (ant 工作定义). -/
noncomputable abbrev q1LogarithmicIntegral (N : ℕ) : ℝ :=
  AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)

/-- 实值 Möbius 权重. -/
noncomputable def q1Mu (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- F(N) 的奇部分: F(N)/2 (当 3 ≤ z 时恰为 F 的奇素因子之积). -/
noncomputable def correctedChenForbiddenOddPart (N : ℕ) : ℕ :=
  correctedChenForbiddenProduct N / 2

/-- 筛素因子主项积: ∏_{p | P(N)} (1 − 1/(p−1)). -/
noncomputable def q1SieveProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - 1 / ((p : ℝ) - 1))

/-- 禁素因子 (奇部分) 主项积: ∏_{p | Fodd(N)} (1 − 1/(p−1)). -/
noncomputable def q1ForbiddenOddProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (correctedChenForbiddenOddPart N).primeFactors, (1 - 1 / ((p : ℝ) - 1))

/-- 偶数模数主项分支: `if Even m then [m | N−2] else 0`. -/
noncomputable def q1APMainEvenValue (N m : ℕ) : ℝ :=
  if Even m then (if m ∣ N - 2 then 1 else 0) else 0

/-- q¹ 主项的偶数模数贡献: Σ_{d|P} Σ_{e|F} μ(d)μ(e)·q1APMainEvenValue(lcm(lcm q d) e). -/
noncomputable def q1CandidateAPMainEvenPart (N q : ℕ) : ℝ :=
  ∑ d ∈ (correctedChenSiftingProduct N).divisors,
    q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
      q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e))

/-! # 1. Möbius 求和: Σ_{d|n} μ(d) = [n = 1], Σ_{d|n, d|m} μ(d) = [gcd(m,n) = 1] -/

/-- Möbius 反演 (实值): `Σ_{d | n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors_eq_if_one (n : ℕ) :
    (∑ d ∈ n.divisors, q1Mu d) = if n = 1 then (1 : ℝ) else 0 := by
  have hz : (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℝ) = (1 : ArithmeticFunction ℝ) := by
    simp
  have hzn : (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℝ) n = (1 : ArithmeticFunction ℝ) n := by
    rw [hz]
  have hsmul : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) •
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    rfl
  rw [hsmul, ArithmeticFunction.coe_zeta_smul_apply (R := ℝ)
    (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ))] at hzn
  rw [ArithmeticFunction.one_apply] at hzn
  simpa [q1Mu] using hzn

/-- `Σ_{d | P, d | m} μ(d) = [gcd(m,P) = 1]` (P ≠ 0). -/
lemma sum_moebius_if_dvd_eq_if_gcd_one {P m : ℕ} (hP0 : P ≠ 0) :
    (∑ d ∈ P.divisors, if d ∣ m then q1Mu d else 0) =
      if Nat.gcd m P = 1 then (1 : ℝ) else 0 := by
  have hdiv : P.divisors.filter (fun d => d ∣ m) = (Nat.gcd m P).divisors := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      rw [Nat.mem_divisors] at hd ⊢
      rcases hd with ⟨hdP, hdm⟩
      rcases hdP with ⟨hdd, hP0'⟩
      constructor
      · exact Nat.dvd_gcd_iff.mpr ⟨hdm, hdd⟩
      · have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
        exact ne_of_gt (Nat.gcd_pos_of_pos_right m hPpos)
    · intro hd
      rw [Nat.mem_divisors] at hd
      rw [Finset.mem_filter] at ⊢
      rw [Nat.mem_divisors] at ⊢
      rcases hd with ⟨hdg, hg0⟩
      constructor
      · exact ⟨(Nat.dvd_gcd_iff.mp hdg).2, hP0⟩
      · exact (Nat.dvd_gcd_iff.mp hdg).1
  rw [← Finset.sum_filter]
  rw [hdiv]
  exact sum_moebius_divisors_eq_if_one (Nat.gcd m P)

/-! # 2. 奇偶与互素工具 -/

/-- 偶数 e = 2·(e/2). -/
private lemma q1_even_div_two_mul {e : ℕ} (he : Even e) : e = 2 * (e / 2) := by
  have h1 : e / 2 * 2 = e := Nat.div_mul_cancel ((even_iff_two_dvd).1 he)
  calc
    e = e / 2 * 2 := h1.symm
    _ = 2 * (e / 2) := by rw [mul_comm]

/-- 奇数的 lcm 仍为奇数. -/
private lemma q1_lcm_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (Nat.lcm a b) := by
  rw [← Nat.not_even_iff_odd]
  intro hev
  have h2 : 2 ∣ Nat.lcm a b := (even_iff_two_dvd).1 hev
  have h2ab : 2 ∣ a * b := dvd_trans h2 (lcm_dvd_mul (α := ℕ) a b)
  rcases (Nat.prime_two.dvd_mul.mp h2ab) with h2a | h2b
  · exact ha.not_two_dvd_nat h2a
  · exact hb.not_two_dvd_nat h2b

/-- 两两互素的 lcm 坍缩: lcm(lcm q d) e = q·d·e. -/
private lemma q1_lcm_collapse {q d e : ℕ} (hqd : q.Coprime d) (hqe : q.Coprime e)
    (hde : d.Coprime e) : Nat.lcm (Nat.lcm q d) e = q * d * e := by
  have hqd_mul : Nat.lcm q d = q * d := Nat.Coprime.lcm_eq_mul hqd
  have hqde : (q * d).Coprime e := (Nat.coprime_mul_iff_left).mpr ⟨hqe, hde⟩
  rw [hqd_mul]
  rw [Nat.Coprime.lcm_eq_mul hqde]

/-- 两两互素的欧拉函数乘积: φ(q·d·e) = φ(q)·φ(d)·φ(e). -/
private lemma q1_phi_mul {q d e : ℕ} (hqd : q.Coprime d) (hqe : q.Coprime e)
    (hde : d.Coprime e) : Nat.totient (q * d * e) = Nat.totient q * Nat.totient d * Nat.totient e := by
  have hqde : (q * d).Coprime e := (Nat.coprime_mul_iff_left).mpr ⟨hqe, hde⟩
  rw [Nat.totient_mul hqde]
  rw [Nat.totient_mul hqd]

/-- μ(2a) = −μ(a) 当 (2, a) 互素. -/
private lemma q1Mu_two_mul {a : ℕ} (h2a : (2 : ℕ).Coprime a) : q1Mu (2 * a) = -q1Mu a := by
  have hmult : ArithmeticFunction.moebius (2 * a) =
      ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius a :=
    (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h2a)
  have hmu2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 := by
    exact ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)
  simp [q1Mu, hmult, hmu2]

/-- 2 不整除筛积 P(N): 其素因子均 > 2. -/
private theorem two_not_dvd_correctedChenSiftingProduct (N : ℕ) :
    ¬ 2 ∣ correctedChenSiftingProduct N := by
  intro h2
  have hmem : 2 ∈ (correctedChenSiftingProduct N).primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero (correctedChenSiftingProduct_ne_zero N)).mpr ⟨by norm_num, h2⟩
  rw [correctedChenSiftingProduct_primeFactors N] at hmem
  rw [Finset.mem_filter] at hmem
  exact (lt_irrefl 2) hmem.2.2.1

/-- 3 ≤ z 时 2 | F(N): 2 是 F 的素因子. -/
theorem two_dvd_correctedChenForbiddenProduct_of_three_le_z {N : ℕ} (hz3 : 3 ≤ correctedChenZ N) :
    2 ∣ correctedChenForbiddenProduct N := by
  have h2mem : 2 ∈ (correctedChenForbiddenProduct N).primeFactors := by
    rw [correctedChenForbiddenProduct_primeFactors N]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega : 2 < correctedChenZ N), ⟨by norm_num, Or.inl (by norm_num)⟩⟩
  exact Nat.dvd_of_mem_primeFactors h2mem

/-- F(N) = 2·Fodd(N) (当 2 | F). -/
theorem forbiddenProduct_eq_two_mul_oddPart (N : ℕ) (h2F : 2 ∣ correctedChenForbiddenProduct N) :
    correctedChenForbiddenProduct N = 2 * correctedChenForbiddenOddPart N := by
  unfold correctedChenForbiddenOddPart
  have h1 : correctedChenForbiddenProduct N / 2 * 2 = correctedChenForbiddenProduct N :=
    Nat.div_mul_cancel h2F
  calc
    correctedChenForbiddenProduct N = correctedChenForbiddenProduct N / 2 * 2 := h1.symm
    _ = 2 * (correctedChenForbiddenProduct N / 2) := by rw [mul_comm]

/-- e | F 且 e 奇 ⟺ e | Fodd (当 2 | F). -/
private theorem odd_divisor_forbidden_iff_mem {N e : ℕ} (h2F : 2 ∣ correctedChenForbiddenProduct N) :
    (e ∈ (correctedChenForbiddenProduct N).divisors ∧ ¬ Even e) ↔
      e ∈ (correctedChenForbiddenOddPart N).divisors := by
  unfold correctedChenForbiddenOddPart
  constructor
  · intro he
    rcases he with ⟨heF, hne⟩
    rw [Nat.mem_divisors] at heF
    rcases heF with ⟨he_dvd_F, hF0⟩
    have hF : correctedChenForbiddenProduct N = 2 * (correctedChenForbiddenProduct N / 2) :=
      forbiddenProduct_eq_two_mul_oddPart N h2F
    have hcop : e.Coprime 2 := by
      apply Nat.coprime_of_dvd'
      intro p hp hp_e hp_2
      have hp2 : p = 2 := by
        rcases (Nat.dvd_prime (by norm_num : (2 : ℕ).Prime)).mp hp_2 with h | h
        · exact False.elim (hp.ne_one h)
        · exact h
      exact False.elim (hne (by rw [even_iff_two_dvd]; rwa [← hp2]))
    have he_dvd_Fodd : e ∣ correctedChenForbiddenProduct N / 2 := by
      have he2 : e ∣ 2 * (correctedChenForbiddenProduct N / 2) := by
        rw [hF] at he_dvd_F
        exact he_dvd_F
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa [mul_comm] using he2)
    have he0 : e ≠ 0 := by
      intro hz
      subst e
      exact hF0 (by
        rcases he_dvd_F with ⟨k, hk⟩
        simpa using hk)
    have hFodd0 : correctedChenForbiddenProduct N / 2 ≠ 0 := by
      intro hz
      have : correctedChenForbiddenProduct N = 0 := by
        rw [hF]
        rw [hz]
      exact hF0 this
    exact Nat.mem_divisors.mpr ⟨he_dvd_Fodd, hFodd0⟩
  · intro he
    rw [Nat.mem_divisors] at he
    rcases he with ⟨he_dvd_Fodd, hFodd0⟩
    rw [Nat.mem_divisors]
    constructor
    · exact ⟨dvd_trans he_dvd_Fodd (Nat.div_dvd_of_dvd h2F), correctedChenForbiddenProduct_ne_zero N⟩
    · have h2_Fodd : ¬ 2 ∣ correctedChenForbiddenProduct N / 2 := by
        have hF : correctedChenForbiddenProduct N = 2 * (correctedChenForbiddenProduct N / 2) :=
          forbiddenProduct_eq_two_mul_oddPart N h2F
        have hsq2 : Squarefree (2 * (correctedChenForbiddenProduct N / 2)) := by
          rw [← hF]
          exact correctedChenForbiddenProduct_squarefree N
        have hcop : (2 : ℕ).Coprime (correctedChenForbiddenProduct N / 2) :=
          Nat.coprime_of_squarefree_mul hsq2
        intro h2d
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) (by rfl : 2 ∣ 2) h2d) hcop
      intro hev
      have h2e : 2 ∣ e := (even_iff_two_dvd).1 hev
      exact h2_Fodd (dvd_trans h2e he_dvd_Fodd)

/-- q 与筛积 P 互素 (q ≥ z, P 的素因子 < z). -/
theorem coprime_q_siftingProduct {N q : ℕ} (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    Nat.Coprime q (correctedChenSiftingProduct N) := by
  apply Nat.coprime_of_dvd'
  intro r hr hr_dvd_q hr_dvd_P
  have hr_z : r < correctedChenZ N := (prime_dvd_correctedChenSiftingProduct hr).mp hr_dvd_P |>.1
  have hr_eq_q : r = q := by
    rcases (Nat.dvd_prime hq).mp hr_dvd_q with h | h
    · exact False.elim (hr.ne_one h)
    · exact h
  subst r
  exact False.elim (by omega)

/-- q 与 Fodd 互素 (q ≥ z, Fodd 的素因子 < z). -/
theorem coprime_q_forbiddenOddPart {N q : ℕ} (hq : q.Prime) (hqz : correctedChenZ N ≤ q)
    (hz3 : 3 ≤ correctedChenZ N) : Nat.Coprime q (correctedChenForbiddenOddPart N) := by
  apply Nat.coprime_of_dvd'
  intro r hr hr_dvd_q hr_dvd_Fodd
  have h2F : 2 ∣ correctedChenForbiddenProduct N :=
    two_dvd_correctedChenForbiddenProduct_of_three_le_z hz3
  have hr_dvd_F : r ∣ correctedChenForbiddenProduct N :=
    dvd_trans hr_dvd_Fodd (Nat.div_dvd_of_dvd h2F)
  have hr_z : r < correctedChenZ N := (prime_dvd_correctedChenForbiddenProduct_iff hr).mp hr_dvd_F |>.1
  have hr_eq_q : r = q := by
    rcases (Nat.dvd_prime hq).mp hr_dvd_q with h | h
    · exact False.elim (hr.ne_one h)
    · exact h
  subst r
  exact False.elim (by omega)

/-- 筛积 P 与 Fodd 互素 (素因子集合不相交: p ∤ N 对 p | P, p | N 对 p | Fodd). -/
theorem coprime_sifting_forbiddenOddPart (N : ℕ) (hz3 : 3 ≤ correctedChenZ N) :
    Nat.Coprime (correctedChenSiftingProduct N) (correctedChenForbiddenOddPart N) := by
  apply Nat.coprime_of_dvd'
  intro r hr hr_dvd_P hr_dvd_Fodd
  have h2F : 2 ∣ correctedChenForbiddenProduct N :=
    two_dvd_correctedChenForbiddenProduct_of_three_le_z hz3
  have hr_P : r < correctedChenZ N ∧ 2 < r ∧ ¬ r ∣ N :=
    (prime_dvd_correctedChenSiftingProduct hr).mp hr_dvd_P
  have hr_dvd_F : r ∣ correctedChenForbiddenProduct N :=
    dvd_trans hr_dvd_Fodd (Nat.div_dvd_of_dvd h2F)
  have hr_F : r < correctedChenZ N ∧ (r ≤ 2 ∨ r ∣ N) :=
    (prime_dvd_correctedChenForbiddenProduct_iff hr).mp hr_dvd_F
  rcases hr_F.2 with hle2 | hN
  · exact False.elim (not_le_of_gt hr_P.2.1 hle2)
  · exact False.elim (hr_P.2.2 hN)

/-- q 与禁素因子乘积 F 互素 (F 的素因子均 < z ≤ q). -/
theorem coprime_q_forbiddenProduct {N q : ℕ} (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    Nat.Coprime q (correctedChenForbiddenProduct N) := by
  apply Nat.coprime_of_dvd'
  intro r hr hr_dvd_q hr_dvd_F
  have hr_z : r < correctedChenZ N := (prime_dvd_correctedChenForbiddenProduct_iff hr).mp hr_dvd_F |>.1
  have hr_eq_q : r = q := by
    rcases (Nat.dvd_prime hq).mp hr_dvd_q with h | h
    · exact False.elim (hr.ne_one h)
    · exact h
  subst r
  exact False.elim (by omega)

/-- 筛积 P 与禁素因子乘积 F 互素 (素因子集合不相交). -/
theorem coprime_sifting_forbiddenProduct (N : ℕ) :
    Nat.Coprime (correctedChenSiftingProduct N) (correctedChenForbiddenProduct N) := by
  apply Nat.coprime_of_dvd'
  intro r hr hr_dvd_P hr_dvd_F
  have hr_P : r < correctedChenZ N ∧ 2 < r ∧ ¬ r ∣ N :=
    (prime_dvd_correctedChenSiftingProduct hr).mp hr_dvd_P
  have hr_F : r < correctedChenZ N ∧ (r ≤ 2 ∨ r ∣ N) :=
    (prime_dvd_correctedChenForbiddenProduct_iff hr).mp hr_dvd_F
  rcases hr_F.2 with hle2 | hN
  · exact False.elim (not_le_of_gt hr_P.2.1 hle2)
  · exact False.elim (hr_P.2.2 hN)

/-! # 3. q¹ 主项的奇偶分解 -/

/-- 逐项奇偶分裂: 对奇 q, d, 主项值 = (e 偶: 精确指示) / (e 奇: li/φ(q·d·e)). -/
private lemma q1_APMainValue_split (N q d e : ℕ) (hqo : Odd q) (hdo : Odd d)
    (hqd : q.Coprime d) (hqe : q.Coprime e) (hde : d.Coprime e) :
    q1APMainValue N (Nat.lcm (Nat.lcm q d) e) =
      (if Even e then q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)
       else q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ)) := by
  by_cases he : Even e
  · have hlcm_even : Even (Nat.lcm (Nat.lcm q d) e) := by
      have h2e : 2 ∣ e := (even_iff_two_dvd).1 he
      exact (even_iff_two_dvd).2 (dvd_trans h2e (dvd_lcm_right _ _))
    unfold q1APMainValue q1APMainEvenValue
    rw [if_pos hlcm_even]
    rw [if_pos he]
    rw [if_pos hlcm_even]
  · have hodd : Odd (Nat.lcm (Nat.lcm q d) e) :=
      q1_lcm_odd (q1_lcm_odd hqo hdo) ((Nat.not_even_iff_odd).1 he)
    unfold q1APMainValue q1APMainEvenValue
    rw [if_neg ((Nat.not_even_iff_odd).2 hodd)]
    rw [if_neg he]
    rw [q1_lcm_collapse hqd hqe hde]

/-- **奇偶分解 (精确)**: `q1CandidateAPMain N q =
li(N)·Σ_{d|P}Σ_{e|Fodd} μ(d)μ(e)/φ(q·d·e) + q1CandidateAPMainEvenPart N q`. -/
theorem q1CandidateAPMain_eq_oddSum_add_evenPart (N q : ℕ) (hz3 : 3 ≤ correctedChenZ N)
    (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    q1CandidateAPMain N q =
      q1LogarithmicIntegral N *
        (∑ d ∈ (correctedChenSiftingProduct N).divisors,
          q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ)))) +
      q1CandidateAPMainEvenPart N q := by
  have hqo : Odd q := by
    have hq3 : 3 ≤ q := by omega
    rcases hq.eq_two_or_odd' with h2 | hod
    · exfalso
      omega
    · exact hod
  have hdo : ∀ d ∈ (correctedChenSiftingProduct N).divisors, Odd d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    apply (Nat.not_even_iff_odd).1
    intro hed
    have h2P : 2 ∣ correctedChenSiftingProduct N :=
      dvd_trans ((even_iff_two_dvd).1 hed) hd.1
    exact two_not_dvd_correctedChenSiftingProduct N h2P
  have h2F : 2 ∣ correctedChenForbiddenProduct N :=
    two_dvd_correctedChenForbiddenProduct_of_three_le_z hz3
  have hinner : ∀ d ∈ (correctedChenSiftingProduct N).divisors,
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          q1Mu e * q1APMainValue N (Nat.lcm (Nat.lcm q d) e)) =
        q1LogarithmicIntegral N *
          (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))) +
        (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)) := by
    intro d hd
    have hsplit : ∀ e ∈ (correctedChenForbiddenProduct N).divisors,
        q1APMainValue N (Nat.lcm (Nat.lcm q d) e) =
          (if Even e then q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)
           else q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ)) := by
      intro e he
      have hd_dvd : d ∣ correctedChenSiftingProduct N := (Nat.mem_divisors.mp hd).1
      have he_dvd : e ∣ correctedChenForbiddenProduct N := (Nat.mem_divisors.mp he).1
      have hqd : q.Coprime d := (coprime_q_siftingProduct hq hqz).coprime_dvd_right hd_dvd
      have hqe : q.Coprime e := (coprime_q_forbiddenProduct hq hqz).coprime_dvd_right he_dvd
      have hde : d.Coprime e :=
        (coprime_sifting_forbiddenProduct N).coprime_dvd_left hd_dvd |>.coprime_dvd_right he_dvd
      exact q1_APMainValue_split N q d e hqo (hdo d hd) hqd hqe hde
    calc
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          q1Mu e * q1APMainValue N (Nat.lcm (Nat.lcm q d) e))
          = (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              q1Mu e * (if Even e then q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)
                else q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ))) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [hsplit e he]
      _ = (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              if Even e then q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)
              else q1Mu e * (q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ))) := by
            apply Finset.sum_congr rfl
            intro e he
            by_cases hev : Even e <;> simp [hev]
      _ = (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              if Even e then q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e) else 0) +
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              if ¬ Even e then q1Mu e * (q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ)) else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro e he
            by_cases hev : Even e <;> simp [hev]
      _ = (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)) +
          q1LogarithmicIntegral N * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))) := by
            congr 1
            · have hoddzero : ∀ e ∈ (correctedChenForbiddenProduct N).divisors,
                ¬ Even e → q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e) = 0 := by
                intro e he hne
                have hodd : Odd (Nat.lcm (Nat.lcm q d) e) :=
                  q1_lcm_odd (q1_lcm_odd hqo (hdo d hd)) ((Nat.not_even_iff_odd).1 hne)
                unfold q1APMainEvenValue
                rw [if_neg ((Nat.not_even_iff_odd).2 hodd)]
                ring
              calc
                (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                    if Even e then q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e) else 0)
                    = (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => Even e),
                        q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)) := by
                      rw [Finset.sum_filter]
                _ = (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                      q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)) := by
                      rw [← Finset.sum_filter_add_sum_filter_not
                        (correctedChenForbiddenProduct N).divisors (fun e => Even e)
                        (fun e => q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e))]
                      have hz : (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => ¬ Even e),
                          q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)) = 0 := by
                        apply Finset.sum_eq_zero
                        intro e he
                        rw [Finset.mem_filter] at he
                        exact hoddzero e he.1 he.2
                      linarith
            · have hset : (correctedChenForbiddenProduct N).divisors.filter (fun e => ¬ Even e) =
                (correctedChenForbiddenOddPart N).divisors := by
                ext e
                rw [Finset.mem_filter]
                exact odd_divisor_forbidden_iff_mem (N := N) h2F
              calc
                (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                    if ¬ Even e then q1Mu e * (q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ)) else 0)
                    = (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => ¬ Even e),
                        q1Mu e * (q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ))) := by
                      rw [Finset.sum_filter]
                _ = (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                      q1Mu e * (q1LogarithmicIntegral N / (Nat.totient (q * d * e) : ℝ))) := by
                      rw [hset]
                _ = q1LogarithmicIntegral N * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                      q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro e he
                      ring
      _ = q1LogarithmicIntegral N * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))) +
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)) := by
            ring
  unfold q1CandidateAPMain q1CandidateAPMainEvenPart
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          q1Mu e * q1APMainValue N (Nat.lcm (Nat.lcm q d) e)))
        = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (q1LogarithmicIntegral N *
              (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))) +
              (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)))) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hinner d hd]
    _ = q1LogarithmicIntegral N *
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
              q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ)))) +
        (∑ d ∈ (correctedChenSiftingProduct N).divisors,
          q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e))) := by
          calc
            (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                q1Mu d * (q1LogarithmicIntegral N *
                  (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                    q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))) +
                  (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                    q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e))))
                = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                    ((q1LogarithmicIntegral N * (q1Mu d *
                        (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                          q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))))) +
                      (q1Mu d *
                        (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                          q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)))))) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  ring
            _ = q1LogarithmicIntegral N *
                  (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                    q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                      q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ)))) +
                (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                  q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                    q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e))) := by
                  rw [Finset.sum_add_distrib]
                  rw [← Finset.mul_sum]

/-! # 4. 偶数模数贡献的精确求值 (Möbius 反演) -/

/-- 偶数模数贡献的精确值: `−[q | N−2]·[gcd(P,N−2)=1]·[gcd(Fodd,(N−2)/2)=1]`. -/
theorem q1CandidateAPMainEvenPart_eq (N q : ℕ) (hN : Even N) (hN2 : 2 ≤ N)
    (hz3 : 3 ≤ correctedChenZ N) (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    q1CandidateAPMainEvenPart N q =
      - (if q ∣ N - 2 then
          (if Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 then
            (if Nat.gcd (correctedChenForbiddenOddPart N) ((N - 2) / 2) = 1 then (1 : ℝ) else 0)
          else 0)
        else 0) := by
  have hqo : Odd q := by
    have hq3 : 3 ≤ q := by omega
    rcases hq.eq_two_or_odd' with h2 | hod
    · exfalso
      omega
    · exact hod
  have hdo : ∀ d ∈ (correctedChenSiftingProduct N).divisors, Odd d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    apply (Nat.not_even_iff_odd).1
    intro hed
    have h2P : 2 ∣ correctedChenSiftingProduct N :=
      dvd_trans ((even_iff_two_dvd).1 hed) hd.1
    exact two_not_dvd_correctedChenSiftingProduct N h2P
  have h2F : 2 ∣ correctedChenForbiddenProduct N :=
    two_dvd_correctedChenForbiddenProduct_of_three_le_z hz3
  have h2N2 : 2 ∣ N - 2 := by
    rcases hN with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    rw [hk]
    omega
  have hval : ∀ d ∈ (correctedChenSiftingProduct N).divisors,
      ∀ e ∈ (correctedChenForbiddenProduct N).divisors,
        q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e) =
          if Even e then (if Nat.lcm (Nat.lcm q d) e ∣ N - 2 then (1 : ℝ) else 0) else 0 := by
    intro d hd e he
    unfold q1APMainEvenValue
    by_cases hev : Even e
    · have hlcm_even : Even (Nat.lcm (Nat.lcm q d) e) := by
        have h2e : 2 ∣ e := (even_iff_two_dvd).1 hev
        exact (even_iff_two_dvd).2 (dvd_trans h2e (dvd_lcm_right _ _))
      rw [if_pos hlcm_even]
      rw [if_pos hev]
    · have hodd : Odd (Nat.lcm (Nat.lcm q d) e) :=
        q1_lcm_odd (q1_lcm_odd hqo (hdo d hd)) ((Nat.not_even_iff_odd).1 hev)
      rw [if_neg ((Nat.not_even_iff_odd).2 hodd)]
      rw [if_neg hev]
  have hesum : (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0)) =
      - (if Nat.gcd (correctedChenForbiddenOddPart N) ((N - 2) / 2) = 1 then (1 : ℝ) else 0) := by
    calc
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0))
          = (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => Even e),
              q1Mu e * (if e ∣ N - 2 then (1 : ℝ) else 0)) := by
            calc
              (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                  q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0))
                  = (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                      if Even e then q1Mu e * (if e ∣ N - 2 then (1 : ℝ) else 0) else 0) := by
                    apply Finset.sum_congr rfl
                    intro e he
                    by_cases hev : Even e <;> simp [hev]
              _ = (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => Even e),
                    q1Mu e * (if e ∣ N - 2 then (1 : ℝ) else 0)) := by
                    rw [Finset.sum_filter]
      _ = (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu (2 * e2) * (if 2 * e2 ∣ N - 2 then (1 : ℝ) else 0)) := by
            apply Finset.sum_bij (fun e he => e / 2)
            · intro e he
              rw [Finset.mem_filter] at he
              rcases he with ⟨heF, hev⟩
              have he2 : e = 2 * (e / 2) := q1_even_div_two_mul hev
              have he2d : e / 2 ∣ correctedChenForbiddenOddPart N := by
                have hF : correctedChenForbiddenProduct N = 2 * correctedChenForbiddenOddPart N :=
                  forbiddenProduct_eq_two_mul_oddPart N h2F
                have heF_dvd : e ∣ correctedChenForbiddenProduct N := (Nat.mem_divisors.mp heF).1
                have heF' : e ∣ 2 * correctedChenForbiddenOddPart N := by
                  rwa [hF] at heF_dvd
                rw [he2] at heF'
                exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp heF'
              have hFodd0' : correctedChenForbiddenOddPart N ≠ 0 := by
                have hF : correctedChenForbiddenProduct N = 2 * correctedChenForbiddenOddPart N :=
                  forbiddenProduct_eq_two_mul_oddPart N h2F
                intro hz
                have : correctedChenForbiddenProduct N = 0 := by rw [hF, hz]
                exact correctedChenForbiddenProduct_ne_zero N this
              have he20 : e / 2 ≠ 0 := by
                intro hz
                have he0 : e ≠ 0 := by
                  rw [Nat.mem_divisors] at heF
                  intro hz2
                  subst e
                  rcases heF.1 with ⟨k, hk⟩
                  exact heF.2 (by simpa using hk)
                have : e = 0 := by rw [he2, hz]
                exact he0 this
              exact Nat.mem_divisors.mpr ⟨he2d, hFodd0'⟩
            · intro e1 he1 e2 he2 h
              rw [Finset.mem_filter] at he1 he2
              have he1' : e1 = 2 * (e1 / 2) := q1_even_div_two_mul he1.2
              have he2' : e2 = 2 * (e2 / 2) := q1_even_div_two_mul he2.2
              rw [he1', he2', h]
            · intro e2 he2
              refine ⟨2 * e2, ?_, ?_⟩
              · rw [Finset.mem_filter]
                constructor
                · rw [Nat.mem_divisors] at he2 ⊢
                  rcases he2 with ⟨he2d, he20⟩
                  constructor
                  · have hF : correctedChenForbiddenProduct N = 2 * correctedChenForbiddenOddPart N :=
                      forbiddenProduct_eq_two_mul_oddPart N h2F
                    rw [hF]
                    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mpr he2d
                  · exact correctedChenForbiddenProduct_ne_zero N
                · exact ⟨e2, two_mul e2⟩
              · omega
            · intro e he
              rw [Finset.mem_filter] at he
              rcases he with ⟨heF, hev⟩
              have he2 : e = 2 * (e / 2) := q1_even_div_two_mul hev
              conv_lhs => rw [he2]
      _ = (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
            -q1Mu e2 * (if e2 ∣ (N - 2) / 2 then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro e2 he2
            have hcop : (2 : ℕ).Coprime e2 := by
              have hF : correctedChenForbiddenProduct N = 2 * correctedChenForbiddenOddPart N :=
                forbiddenProduct_eq_two_mul_oddPart N h2F
              have hsq2 : Squarefree (2 * correctedChenForbiddenOddPart N) := by
                rw [← hF]
                exact correctedChenForbiddenProduct_squarefree N
              have h2Fo : (2 : ℕ).Coprime (correctedChenForbiddenOddPart N) :=
                Nat.coprime_of_squarefree_mul hsq2
              exact h2Fo.coprime_dvd_right (Nat.mem_divisors.mp he2).1
            have hmu : q1Mu (2 * e2) = -q1Mu e2 := q1Mu_two_mul hcop
            have hdvd : (2 * e2 ∣ N - 2) ↔ (e2 ∣ (N - 2) / 2) :=
              (Nat.dvd_div_iff_mul_dvd h2N2).symm
            rw [hmu]
            by_cases h : e2 ∣ (N - 2) / 2 <;> simp [h, hdvd]
      _ = - (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu e2 * (if e2 ∣ (N - 2) / 2 then (1 : ℝ) else 0)) := by
            calc
              (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
                  -q1Mu e2 * (if e2 ∣ (N - 2) / 2 then (1 : ℝ) else 0))
                  = (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
                      -(q1Mu e2 * (if e2 ∣ (N - 2) / 2 then (1 : ℝ) else 0))) := by
                    apply Finset.sum_congr rfl
                    intro e2 he2
                    ring
              _ = - (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
                      q1Mu e2 * (if e2 ∣ (N - 2) / 2 then (1 : ℝ) else 0)) := by
                    rw [Finset.sum_neg_distrib]
      _ = - (if Nat.gcd (correctedChenForbiddenOddPart N) ((N - 2) / 2) = 1 then (1 : ℝ) else 0) := by
            congr 1
            have hFodd0 : correctedChenForbiddenOddPart N ≠ 0 := by
              intro hz
              have hF : correctedChenForbiddenProduct N = 2 * correctedChenForbiddenOddPart N :=
                forbiddenProduct_eq_two_mul_oddPart N h2F
              have : correctedChenForbiddenProduct N = 0 := by rw [hF, hz]
              exact correctedChenForbiddenProduct_ne_zero N this
            calc
              (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
                  q1Mu e2 * (if e2 ∣ (N - 2) / 2 then (1 : ℝ) else 0))
                  = (∑ e2 ∈ (correctedChenForbiddenOddPart N).divisors,
                      if e2 ∣ (N - 2) / 2 then q1Mu e2 else 0) := by
                    apply Finset.sum_congr rfl
                    intro e2 he2
                    by_cases h : e2 ∣ (N - 2) / 2 <;> simp [h]
              _ = (if Nat.gcd ((N - 2) / 2) (correctedChenForbiddenOddPart N) = 1 then (1 : ℝ) else 0) := by
                    rw [sum_moebius_if_dvd_eq_if_gcd_one (P := correctedChenForbiddenOddPart N)
                      (m := (N - 2) / 2) hFodd0]
              _ = (if Nat.gcd (correctedChenForbiddenOddPart N) ((N - 2) / 2) = 1 then (1 : ℝ) else 0) := by
                    by_cases hgcd : Nat.gcd (correctedChenForbiddenOddPart N) ((N - 2) / 2) = 1
                    · have hg' : Nat.gcd ((N - 2) / 2) (correctedChenForbiddenOddPart N) = 1 := by
                        rwa [Nat.gcd_comm]
                      simp [hgcd, hg']
                    · have hg' : Nat.gcd ((N - 2) / 2) (correctedChenForbiddenOddPart N) ≠ 1 := by
                        intro h
                        apply hgcd
                        rwa [Nat.gcd_comm]
                      simp [hgcd, hg']
  unfold q1CandidateAPMainEvenPart
  -- 重写内层值, 把 [lcm(lcm q d) e | N−2] 分解为 [q|N−2]·[d|N−2]·[e|N−2]
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          q1Mu e * q1APMainEvenValue N (Nat.lcm (Nat.lcm q d) e)))
        = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              q1Mu e * (if Even e then (if Nat.lcm (Nat.lcm q d) e ∣ N - 2 then (1 : ℝ) else 0) else 0))) := by
          exact Finset.sum_congr rfl (fun d hd =>
            congrArg (fun x => q1Mu d * x)
              (Finset.sum_congr rfl (fun e he => congrArg (fun x => q1Mu e * x) (hval d hd e he))))
    _ = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
          q1Mu d * (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            q1Mu e * (if Even e then (if q ∣ N - 2 then (if d ∣ N - 2 then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0) else 0) else 0))) := by
          exact Finset.sum_congr rfl (fun d hd =>
            congrArg (fun x => q1Mu d * x)
              (Finset.sum_congr rfl (fun e he => by
                by_cases hev : Even e <;> simp [hev]
                · have hif : (if Nat.lcm (Nat.lcm q d) e ∣ N - 2 then (1 : ℝ) else 0) =
                      (if q ∣ N - 2 then (if d ∣ N - 2 then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0) else 0) := by
                    rw [show (Nat.lcm (Nat.lcm q d) e ∣ N - 2) ↔ (q ∣ N - 2 ∧ d ∣ N - 2 ∧ e ∣ N - 2) by
                      rw [lcm_dvd_iff]
                      rw [lcm_dvd_iff]
                      rw [and_assoc]]
                    by_cases hq2 : q ∣ N - 2 <;> by_cases hd2 : d ∣ N - 2 <;> by_cases he2 : e ∣ N - 2 <;> simp [hq2, hd2, he2]
                  exact congrArg (fun x => q1Mu e * x) hif)))
    _ = (if q ∣ N - 2 then
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (if d ∣ N - 2 then
              (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0)) else 0))
        else 0) := by
          by_cases hq2 : q ∣ N - 2 <;> simp [hq2]
          · apply Finset.sum_congr rfl
            intro d hd
            by_cases hd2 : d ∣ N - 2 <;> simp [hd2]
    _ = (if q ∣ N - 2 then
          (if Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 then
            (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0))
          else 0)
        else 0) := by
          by_cases hq2 : q ∣ N - 2 <;> simp [hq2]
          · have hsumP : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                q1Mu d * (if d ∣ N - 2 then
                  (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                    q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0)) else 0)) =
              (if Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 then
                (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                  q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0))
              else 0) := by
              calc
                (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                    q1Mu d * (if d ∣ N - 2 then
                      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                        q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0)) else 0))
                    = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                        (if d ∣ N - 2 then q1Mu d else 0) *
                          (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                            q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0))) := by
                      apply Finset.sum_congr rfl
                      intro d hd
                      by_cases hd2 : d ∣ N - 2 <;> simp [hd2]
                _ = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                      if d ∣ N - 2 then q1Mu d else 0) *
                      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                        q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0)) := by
                      rw [Finset.sum_mul]
                _ = (if Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 then (1 : ℝ) else 0) *
                      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                        q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0)) := by
                      rw [sum_moebius_if_dvd_eq_if_gcd_one (P := correctedChenSiftingProduct N)
                        (m := N - 2) (correctedChenSiftingProduct_ne_zero N)]
                _ = (if Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 then
                      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                        q1Mu e * (if Even e then (if e ∣ N - 2 then (1 : ℝ) else 0) else 0))
                    else 0) := by
                      by_cases hg : Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 <;> simp [hg]
            simpa using hsumP
    _ = - (if q ∣ N - 2 then
          (if Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 then
            (if Nat.gcd (correctedChenForbiddenOddPart N) ((N - 2) / 2) = 1 then (1 : ℝ) else 0)
          else 0)
        else 0) := by
          by_cases hq2 : q ∣ N - 2 <;> simp [hq2]
          · by_cases hg : Nat.gcd (correctedChenSiftingProduct N) (N - 2) = 1 <;> simp [hg]
            · rw [hesum]
              ring


/-- 偶数模数贡献非正: 精确值为 `−[...]` 三个非负指示因子之积. -/
theorem q1CandidateAPMainEvenPart_nonpos (N q : ℕ) (hN : Even N) (hN2 : 2 ≤ N)
    (hz3 : 3 ≤ correctedChenZ N) (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    q1CandidateAPMainEvenPart N q ≤ 0 := by
  rw [q1CandidateAPMainEvenPart_eq N q hN hN2 hz3 hq hqz]
  split_ifs <;> norm_num

/-! # 5. Möbius 欧拉积分解: Σ_{d|P} μ(d)/φ(d) = ∏_{p|P} (1 − 1/(p−1)) -/

/-- 筛积的 Möbius 欧拉积: `Σ_{d | P} μ(d)/φ(d) = q1SieveProduct N`. -/
theorem q1Sum_nu_sifting (N : ℕ) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (1 / (Nat.totient d : ℝ))) = q1SieveProduct N := by
  have hEP := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    correctedChenNu (AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative)
    (correctedChenSiftingProduct_squarefree N)
  have hsum : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (1 / (Nat.totient d : ℝ))) =
      (∑ d ∈ (correctedChenSiftingProduct N).divisors, q1Mu d * correctedChenNu d) := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hsq : Squarefree d
    · have hnu := AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient hsq
      unfold q1Mu correctedChenNu
      rw [← hnu]
    · have hmu : q1Mu d = 0 := by
        have hz : ArithmeticFunction.moebius d = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [q1Mu, hz]
      simp [hmu]
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (1 / (Nat.totient d : ℝ)))
        = (∑ d ∈ (correctedChenSiftingProduct N).divisors, q1Mu d * correctedChenNu d) := hsum
    _ = ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - correctedChenNu p) := by
          simpa [q1Mu] using hEP.symm
    _ = q1SieveProduct N := by
          unfold q1SieveProduct correctedChenNu
          apply Finset.prod_congr rfl
          intro p hp
          rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (Nat.prime_of_mem_primeFactors hp)]

/-- Fodd 的 Möbius 欧拉积: `Σ_{e | Fodd} μ(e)/φ(e) = q1ForbiddenOddProduct N`. -/
theorem q1Sum_nu_forbiddenOddPart (N : ℕ) (hz3 : 3 ≤ correctedChenZ N) :
    (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
        q1Mu e * (1 / (Nat.totient e : ℝ))) = q1ForbiddenOddProduct N := by
  have h2F : 2 ∣ correctedChenForbiddenProduct N :=
    two_dvd_correctedChenForbiddenProduct_of_three_le_z hz3
  have hsqFodd : Squarefree (correctedChenForbiddenOddPart N) := by
    unfold correctedChenForbiddenOddPart
    exact (correctedChenForbiddenProduct_squarefree N).squarefree_of_dvd
      (Nat.div_dvd_of_dvd h2F)
  have hEP := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    correctedChenNu (AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative) hsqFodd
  have hsum : (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
        q1Mu e * (1 / (Nat.totient e : ℝ))) =
      (∑ e ∈ (correctedChenForbiddenOddPart N).divisors, q1Mu e * correctedChenNu e) := by
    apply Finset.sum_congr rfl
    intro e he
    by_cases hsq : Squarefree e
    · have hnu := AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient hsq
      unfold q1Mu correctedChenNu
      rw [← hnu]
    · have hmu : q1Mu e = 0 := by
        have hz : ArithmeticFunction.moebius e = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [q1Mu, hz]
      simp [hmu]
  calc
    (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
        q1Mu e * (1 / (Nat.totient e : ℝ)))
        = (∑ e ∈ (correctedChenForbiddenOddPart N).divisors, q1Mu e * correctedChenNu e) := hsum
    _ = ∏ p ∈ (correctedChenForbiddenOddPart N).primeFactors, (1 - correctedChenNu p) := by
          simpa [q1Mu] using hEP.symm
    _ = q1ForbiddenOddProduct N := by
          unfold q1ForbiddenOddProduct correctedChenNu
          apply Finset.prod_congr rfl
          intro p hp
          rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (Nat.prime_of_mem_primeFactors hp)]


/-- **奇数双和分解**: `Σ_{d|P} Σ_{e|Fodd} μ(d)μ(e)/φ(q·d·e) =
(1/φ(q))·q1SieveProduct·q1ForbiddenOddProduct` (q, d, e 两两互素). -/
theorem q1OddSum_eq_products (N q : ℕ) (hz3 : 3 ≤ correctedChenZ N)
    (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
          q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ)))) =
      (1 / (Nat.totient q : ℝ)) * q1SieveProduct N * q1ForbiddenOddProduct N := by
  have hφq0 : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq.pos).ne'
  have hterm : ∀ d ∈ (correctedChenSiftingProduct N).divisors,
      ∀ e ∈ (correctedChenForbiddenOddPart N).divisors,
        (1 / (Nat.totient (q * d * e) : ℝ)) =
          (1 / (Nat.totient q : ℝ)) * (1 / (Nat.totient d : ℝ)) * (1 / (Nat.totient e : ℝ)) := by
    intro d hd e he
    have hd_dvd : d ∣ correctedChenSiftingProduct N := (Nat.mem_divisors.mp hd).1
    have he_dvd : e ∣ correctedChenForbiddenOddPart N := (Nat.mem_divisors.mp he).1
    have hqd : q.Coprime d := (coprime_q_siftingProduct hq hqz).coprime_dvd_right hd_dvd
    have hqe : q.Coprime e := (coprime_q_forbiddenOddPart hq hqz hz3).coprime_dvd_right he_dvd
    have hde : d.Coprime e :=
      (coprime_sifting_forbiddenOddPart N hz3).coprime_dvd_left hd_dvd |>.coprime_dvd_right he_dvd
    have hphi : Nat.totient (q * d * e) = Nat.totient q * Nat.totient d * Nat.totient e :=
      q1_phi_mul hqd hqe hde
    have hd0 : d ≠ 0 := by
      rw [Nat.mem_divisors] at hd
      intro hz
      subst d
      rcases hd.1 with ⟨k, hk⟩
      exact hd.2 (by simpa using hk)
    have he0 : e ≠ 0 := by
      rw [Nat.mem_divisors] at he
      intro hz
      subst e
      rcases he.1 with ⟨k, hk⟩
      exact he.2 (by simpa using hk)
    have hφd0 : (Nat.totient d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)).ne'
    have hφe0 : (Nat.totient e : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero he0)).ne'
    rw [hphi]
    field_simp [hφq0, hφd0, hφe0]
    ring
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
          q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ))))
        = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
              q1Mu e * ((1 / (Nat.totient q : ℝ)) * (1 / (Nat.totient d : ℝ)) * (1 / (Nat.totient e : ℝ))))) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          rw [hterm d hd e he]
    _ = (1 / (Nat.totient q : ℝ)) * (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (1 / (Nat.totient d : ℝ)) *
              (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                q1Mu e * (1 / (Nat.totient e : ℝ)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          ring
    _ = (1 / (Nat.totient q : ℝ)) * (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            q1Mu d * (1 / (Nat.totient d : ℝ))) *
          (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
            q1Mu e * (1 / (Nat.totient e : ℝ))) := by
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
    _ = (1 / (Nat.totient q : ℝ)) * q1SieveProduct N * q1ForbiddenOddProduct N := by
          rw [q1Sum_nu_sifting N]
          rw [q1Sum_nu_forbiddenOddPart N hz3]

/-! # 6. 逐 q 上界与主项总和的分解 -/

/-- q¹ 主项逐 q 上界: `q1CandidateAPMain N q ≤ li(N)/φ(q)·q1SieveProduct·q1ForbiddenOddProduct`. -/
theorem q1CandidateAPMain_le (N q : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hz3 : 3 ≤ correctedChenZ N)
    (hq : q.Prime) (hqz : correctedChenZ N ≤ q) :
    q1CandidateAPMain N q ≤
      q1LogarithmicIntegral N / (Nat.totient q : ℝ) *
        q1SieveProduct N * q1ForbiddenOddProduct N := by
  have hsplit := q1CandidateAPMain_eq_oddSum_add_evenPart N q hz3 hq hqz
  have hprod := q1OddSum_eq_products N q hz3 hq hqz
  have heven0 : q1CandidateAPMainEvenPart N q ≤ 0 :=
    q1CandidateAPMainEvenPart_nonpos N q hN hN2 hz3 hq hqz
  calc
    q1CandidateAPMain N q
        = q1LogarithmicIntegral N *
            (∑ d ∈ (correctedChenSiftingProduct N).divisors,
              q1Mu d * (∑ e ∈ (correctedChenForbiddenOddPart N).divisors,
                q1Mu e * (1 / (Nat.totient (q * d * e) : ℝ)))) +
            q1CandidateAPMainEvenPart N q := hsplit
    _ = q1LogarithmicIntegral N / (Nat.totient q : ℝ) *
          q1SieveProduct N * q1ForbiddenOddProduct N + q1CandidateAPMainEvenPart N q := by
          rw [hprod]
          ring_nf
    _ ≤ q1LogarithmicIntegral N / (Nat.totient q : ℝ) *
          q1SieveProduct N * q1ForbiddenOddProduct N := by
          linarith

/-- 筛积主项积非负. -/
theorem q1SieveProduct_nonneg (N : ℕ) : 0 ≤ q1SieveProduct N := by
  unfold q1SieveProduct
  apply Finset.prod_nonneg
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hpp.two_le
  have hpos : 0 < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_iff₀ hpos]
    have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    linarith
  linarith

/-- 禁素因子 (奇部分) 主项积 ≤ 1 (每个因子 ∈ (0, 1]). -/
theorem q1ForbiddenOddProduct_le_one (N : ℕ) (hz3 : 3 ≤ correctedChenZ N) :
    q1ForbiddenOddProduct N ≤ 1 := by
  unfold q1ForbiddenOddProduct
  exact Finset.prod_le_one
    (fun (p : ℕ) hp => by
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp2 : 2 ≤ p := hpp.two_le
      have hpos : 0 < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
        rw [div_le_iff₀ hpos]
        have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        linarith
      linarith)
    (fun (p : ℕ) hp => by
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp2 : 2 ≤ p := hpp.two_le
      have hpos : 0 < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (le_of_lt hpos)
      exact sub_le_self (a := (1 : ℝ)) hnonneg)


/-- 筛积主项积 = Goldbach 筛积 (偶数 N 下 p = 2 两侧都被 p ∤ N 排除). -/
theorem q1SieveProduct_eq_goldbachSieveProduct (N : ℕ) (hN : Even N) :
    q1SieveProduct N = MertensTheorem.goldbachSieveProduct N (correctedChenZ N) := by
  unfold q1SieveProduct MertensTheorem.goldbachSieveProduct
  rw [correctedChenSiftingProduct_primeFactors N]
  have hset : ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ ¬ p ∣ N)) =
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hr, hc⟩
      have hpne2 : p ≠ 2 := by
        intro hp2
        have h2dvd : 2 ∣ N := by
          rcases hN with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          rw [hk]
          ring
        exact hc.2 (by simpa [hp2] using h2dvd)
      refine Finset.mem_filter.mpr ⟨hr, ⟨hc.1, ?_⟩⟩
      rcases hc.1.eq_two_or_odd' with h | h
      · exact absurd h hpne2
      · have : 2 ≤ p := hc.1.two_le
        omega
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hr, hc⟩
      exact Finset.mem_filter.mpr ⟨hr, ⟨hc.1, hc.2.2⟩⟩
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  rfl

/-- **主项总和分解**: `q1MainTermSum N ≤ li(N)·goldbachSieveProduct(N, z)·Σ_{q∈[z,y)} 1/φ(q)`. -/
theorem q1MainTermSum_le (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hz3 : 3 ≤ correctedChenZ N) :
    q1MainTermSum N ≤
      q1LogarithmicIntegral N * MertensTheorem.goldbachSieveProduct N (correctedChenZ N) *
        (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
          1 / (Nat.totient q : ℝ)) := by
  unfold q1MainTermSum
  have hli0 : 0 ≤ q1LogarithmicIntegral N := by
    unfold q1LogarithmicIntegral AnalyticNumberTheory.Sieve.logarithmicIntegral
    have hN1r : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact div_nonneg (by positivity : 0 ≤ (N : ℝ)) (le_of_lt (Real.log_pos hN1r))
  have hgp0 : 0 ≤ MertensTheorem.goldbachSieveProduct N (correctedChenZ N) := by
    unfold MertensTheorem.goldbachSieveProduct
    apply Finset.prod_nonneg
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hc⟩
    have hpp : p.Prime := hc.1
    have hp2 : 2 ≤ p := hpp.two_le
    have hpos : 0 < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
      rw [div_le_iff₀ hpos]
      have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      linarith
    linarith
  calc
    (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
        q1CandidateAPMain N q)
        ≤ (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
            q1LogarithmicIntegral N / (Nat.totient q : ℝ) * q1SieveProduct N * q1ForbiddenOddProduct N) := by
          apply Finset.sum_le_sum
          intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqr, hqc⟩
          exact q1CandidateAPMain_le N q hN hN2 hz3 hqc.1 hqc.2
    _ ≤ (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
            q1LogarithmicIntegral N / (Nat.totient q : ℝ) * MertensTheorem.goldbachSieveProduct N (correctedChenZ N)) := by
          apply Finset.sum_le_sum
          intro q hq
          have hq0 : 0 ≤ 1 / (Nat.totient q : ℝ) := by positivity
          have hprod_le : q1SieveProduct N * q1ForbiddenOddProduct N ≤ q1SieveProduct N := by
            exact mul_le_of_le_one_right (q1SieveProduct_nonneg N) (q1ForbiddenOddProduct_le_one N hz3)
          have hsq : q1SieveProduct N = MertensTheorem.goldbachSieveProduct N (correctedChenZ N) :=
            q1SieveProduct_eq_goldbachSieveProduct N hN
          calc
            q1LogarithmicIntegral N / (Nat.totient q : ℝ) * q1SieveProduct N * q1ForbiddenOddProduct N
                = q1LogarithmicIntegral N * (1 / (Nat.totient q : ℝ)) * (q1SieveProduct N * q1ForbiddenOddProduct N) := by ring
            _ ≤ q1LogarithmicIntegral N * (1 / (Nat.totient q : ℝ)) * q1SieveProduct N := by
                  exact mul_le_mul_of_nonneg_left hprod_le (mul_nonneg hli0 hq0)
            _ = q1LogarithmicIntegral N / (Nat.totient q : ℝ) * MertensTheorem.goldbachSieveProduct N (correctedChenZ N) := by
                  rw [hsq]
                  ring
    _ = q1LogarithmicIntegral N * MertensTheorem.goldbachSieveProduct N (correctedChenZ N) *
          (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
            1 / (Nat.totient q : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring


/-! # 7. 解析装配: 素数倒数和, log(z−1) 下界, 最终吸收 -/

/-- **q 倒数和界**: 对 N > 2^110, `Σ_{q∈[z,y)} 1/φ(q) ≤ C₀` (Mertens 第二定理 + log y/log z ≤ 7). -/
theorem q1_qSum_phi_inv_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ N : ℕ, 2 ^ 110 < N →
      (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
          1 / (Nat.totient q : ℝ)) ≤ C₀ := by
  obtain ⟨E, hE0, hE⟩ := AnalyticNumberTheory.Mertens.primeReciprocalSum_range_le
  have hlog7 : 0 < log 7 := Real.log_pos (by norm_num : (1 : ℝ) < 7)
  refine ⟨2 * (log 7 + E), by positivity, ?_⟩
  intro N hNbig
  have hz3 : 3 ≤ correctedChenZ N := correctedChenZ_ge_three (by omega : 59049 ≤ N)
  have hzleY : correctedChenZ N ≤ correctedChenY N := le_of_lt (correctedChenZ_lt_Y (by omega : 9 ≤ N))
  have hz1 : (1 : ℝ) < correctedChenZ N := by exact_mod_cast (by omega : 1 < correctedChenZ N)
  have hy1 : (1 : ℝ) < correctedChenY N := by
    have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast (by omega : 8 ≤ N)
    have hpow := Real.rpow_le_rpow (by norm_num : 0 ≤ (8 : ℝ)) hN8 (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hval : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      norm_num [Real.rpow_natCast, Real.rpow_mul, Real.rpow_one]
    have h13 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by rwa [hval] at hpow
    have hle : (N : ℝ) ^ (1 / 3 : ℝ) ≤ correctedChenY N := by
      unfold correctedChenY
      exact Nat.le_ceil ((N : ℝ) ^ (1 / 3 : ℝ))
    linarith
  have hzpos : 0 < log (correctedChenZ N : ℝ) := Real.log_pos hz1
  have hypos : 0 < log (correctedChenY N : ℝ) := Real.log_pos hy1
  have hlogratio := hTripleMain_log_y_div_log_z_le N hNbig
  have hlogratio' : log (log (correctedChenY N : ℝ) / log (correctedChenZ N : ℝ)) ≤ log 7 := by
    exact Real.log_le_log (by positivity : 0 < log (correctedChenY N : ℝ) / log (correctedChenZ N : ℝ)) hlogratio
  calc
    (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
        1 / (Nat.totient q : ℝ))
        ≤ (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
            2 / (q : ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          have hqprime : q.Prime := (Finset.mem_filter.mp hq).2.1
          have hqphi : (Nat.totient q : ℝ) = (q : ℝ) - 1 := by
            rw [Nat.totient_prime hqprime]
            exact Nat.cast_sub (by omega : 1 ≤ q)
          have hq1 : (1 : ℝ) < (q : ℝ) := by
            have hzq : correctedChenZ N ≤ q := (Finset.mem_filter.mp hq).2.2
            exact_mod_cast (by omega : 1 < q)
          have hq2r : (2 : ℝ) ≤ (q : ℝ) := by
            have hzq : correctedChenZ N ≤ q := (Finset.mem_filter.mp hq).2.2
            exact_mod_cast (by omega : 2 ≤ q)
          have hle : 1 / ((q : ℝ) - 1) ≤ 2 / (q : ℝ) := by
            have hpos1 : 0 < (q : ℝ) - 1 := by linarith
            have hpos2 : 0 < (q : ℝ) := by linarith
            rw [div_le_div_iff₀ hpos1 hpos2]
            nlinarith
          rwa [hqphi] at hle
    _ = 2 * (∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q),
            1 / (q : ℝ)) := by
          rw [← Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ ≤ 2 * (∑ p ∈ (Finset.range (correctedChenY N + 1)).filter (fun p => p.Prime ∧ correctedChenZ N ≤ p),
            1 / (p : ℝ)) := by
          have hsub : (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q) ⊆
              (Finset.range (correctedChenY N + 1)).filter (fun p => p.Prime ∧ correctedChenZ N ≤ p) := by
            intro q hq
            rw [Finset.mem_filter] at hq ⊢
            exact ⟨by omega, hq.2⟩
          have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => by positivity)
          exact mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 2 * (AnalyticNumberTheory.Mertens.primeReciprocalSum (correctedChenY N) -
          AnalyticNumberTheory.Mertens.primeReciprocalSum (correctedChenZ N - 1)) := by
          exact congrArg (fun x : ℝ => 2 * x)
            (AnalyticNumberTheory.Mertens.primeReciprocalSum_range_eq (correctedChenZ N) (correctedChenY N)
              (by omega : 1 ≤ correctedChenZ N) hzleY)
    _ ≤ 2 * (log (log (correctedChenY N : ℝ) / log (correctedChenZ N : ℝ)) + E) := by
          have hb := hE (correctedChenZ N) (correctedChenY N) hz3 hzleY
          exact mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2 * (log 7 + E) := by
          exact mul_le_mul_of_nonneg_left (add_le_add_right hlogratio' E) (by norm_num)


/-- **log(z-1) 下界**: 对 N >= 2^40, (1/20)*log N <= log(z-1) (z >= N^{1/10}-1 >= N^{1/20}+1). -/
theorem q1_log_z_sub_one_lower (N : ℕ) (hN40 : 2 ^ 40 ≤ N) :
    (1 / 20 : ℝ) * log (N : ℝ) ≤ log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
  have hz3 : 3 ≤ correctedChenZ N := by
    have : 59049 ≤ N := by
      have : 59049 < 2 ^ 40 := by norm_num
      omega
    exact correctedChenZ_ge_three this
  have hz1n : 1 < correctedChenZ N - 1 := by omega
  have hlogz1pos : 0 < log ((correctedChenZ N - 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hz1n)
  have hzge : (N : ℝ) ^ (1 / 20 : ℝ) ≤ ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
    let t : ℝ := (N : ℝ) ^ (1 / 20 : ℝ)
    have hxeq : t ^ 2 = x := by
      dsimp [t, x]
      rw [← Real.rpow_mul (by positivity : 0 ≤ (N : ℝ))]
      norm_num
    have ht4 : (4 : ℝ) ≤ t := by
      dsimp [t]
      have hN40' : ((2 ^ 40 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN40
      have hpow := Real.rpow_le_rpow (by norm_num : 0 ≤ ((2 ^ 40 : ℕ) : ℝ)) hN40' (by norm_num : 0 ≤ (1 / 20 : ℝ))
      have hval : ((2 ^ 40 : ℕ) : ℝ) ^ (1 / 20 : ℝ) = 4 := by
        rw [Nat.cast_pow]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
        norm_num [Real.rpow_natCast]
      rwa [hval] at hpow
    have hfloor : x - 1 ≤ (Nat.floor x : ℝ) := by
      have hlt := Nat.lt_floor_add_one x
      linarith
    have hz : (Nat.floor x : ℝ) ≤ (correctedChenZ N : ℝ) := by
      unfold correctedChenZ
      rw [Nat.cast_max]
      exact le_max_right (2 : ℝ) ↑(Nat.floor x)
    have hz1' : x - 2 ≤ ((correctedChenZ N - 1 : ℕ) : ℝ) := by
      have : x - 1 ≤ (correctedChenZ N : ℝ) := le_trans hfloor hz
      have hcast : ((correctedChenZ N - 1 : ℕ) : ℝ) = (correctedChenZ N : ℝ) - 1 :=
        Nat.cast_sub (by omega : 1 ≤ correctedChenZ N)
      rw [hcast]
      linarith
    have hsq : 4 * t ≤ t ^ 2 := by
      have ht0 : 0 ≤ t := by positivity
      exact mul_le_mul ht4 le_rfl ht0 ht0
    have htle : t ≤ x - 2 := by
      nlinarith [hxeq, hsq, ht4]
    exact le_trans htle hz1'
  have hlog : log ((N : ℝ) ^ (1 / 20 : ℝ)) ≤ log ((correctedChenZ N - 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity : 0 < (N : ℝ) ^ (1 / 20 : ℝ)) hzge
  have hrew : log ((N : ℝ) ^ (1 / 20 : ℝ)) = (1 / 20 : ℝ) * log (N : ℝ) := by
    rw [Real.log_rpow (by positivity : 0 < (N : ℝ))]
  rwa [hrew] at hlog

/-- chen 侧截断奇异级数与 ant 侧定义相同 (局部因子体逐位一致). -/
theorem chenSingularSeriesTruncated_eq_ant (N z : ℕ) :
    SingularSeries.singularSeriesTruncated N z =
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N z := by
  unfold SingularSeries.singularSeriesTruncated AnalyticNumberTheory.Sieve.singularSeriesTruncated
  apply Finset.prod_congr rfl
  intro p hp
  unfold SingularSeries.localFactor AnalyticNumberTheory.Sieve.localFactor
  rfl


/-- **q¹ 主项吸收 (chen #37)**: 分解 + Mertens + 素数倒数和, 装配为
`C₁·𝔖_trunc·N/log²N` 形式. -/
theorem q1MainTermAbsorption_holds : q1MainTermAbsorption := by
  obtain ⟨a₁, a₂, ha₁, hPP⟩ := MertensTheorem.primeProduct_asymptotic_order
  obtain ⟨C₀, hC₀, hqsum⟩ := q1_qSum_phi_inv_bound
  have ha₂pos : 0 < a₂ := by
    have hx := hPP 2 (by norm_num : 2 ≤ 2)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h1 : a₁ / log 2 ≤ MertensTheorem.primeProduct 2 := hx.1
    have h2 : MertensTheorem.primeProduct 2 ≤ a₂ / log 2 := hx.2
    have h3 : a₁ ≤ a₂ := by
      have hle' : a₁ * log 2 ≤ a₂ * log 2 :=
        (div_le_div_iff₀ hlog2 hlog2).mp (le_trans h1 h2)
      exact le_of_mul_le_mul_right hle' (le_of_lt hlog2)
    linarith
  let C₁ : ℝ := 20 * a₂ * C₀
  refine ⟨C₁, by positivity, 2 ^ 110 + 1, ?_⟩
  intro N hN hEven
  have hNbig : 2 ^ 110 < N := by omega
  have hN40 : 2 ^ 40 ≤ N := by
    have : 2 ^ 40 < 2 ^ 110 := by norm_num
    omega
  have hN2 : 2 ≤ N := by omega
  have hz3 : 3 ≤ correctedChenZ N := correctedChenZ_ge_three (by omega : 59049 ≤ N)
  have hz2 : 2 ≤ correctedChenZ N := by omega
  have hz1 : 1 ≤ correctedChenZ N - 1 := by omega
  have hzleY : correctedChenZ N ≤ correctedChenY N := le_of_lt (correctedChenZ_lt_Y (by omega : 9 ≤ N))
  let 𝔖 : ℝ := AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
  let liN : ℝ := q1LogarithmicIntegral N
  let qsum : ℝ := ∑ q ∈ (Finset.range (correctedChenY N)).filter (fun q => q.Prime ∧ correctedChenZ N ≤ q), 1 / (Nat.totient q : ℝ)
  let pp : ℝ := MertensTheorem.primeProduct (correctedChenZ N - 1)
  have hli : liN = (N : ℝ) / log (N : ℝ) := by
    dsimp [liN, q1LogarithmicIntegral]
    rfl
  have hlogNpos : 0 < log (N : ℝ) := by
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact Real.log_pos hN1
  have hli0 : 0 ≤ liN := by
    rw [hli]
    exact div_nonneg (by positivity : 0 ≤ (N : ℝ)) (le_of_lt hlogNpos)
  have hmain : q1MainTermSum N ≤ liN * MertensTheorem.goldbachSieveProduct N (correctedChenZ N) * qsum := by
    simpa [liN, qsum] using q1MainTermSum_le N hEven hN2 hz3
  have hgp : MertensTheorem.goldbachSieveProduct N (correctedChenZ N) = pp * 𝔖 := by
    dsimp [𝔖, pp]
    rw [MertensTheorem.sieveProduct_identity N (correctedChenZ N) hz2 hEven]
    rw [chenSingularSeriesTruncated_eq_ant N (correctedChenZ N - 1)]
  have hpp : pp ≤ a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    dsimp [pp]
    exact (hPP (correctedChenZ N - 1) (by omega : 2 ≤ correctedChenZ N - 1)).2
  have hlog : (1 : ℝ) / log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ 20 / log (N : ℝ) := by
    have hlogz1pos : 0 < log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (by omega : 1 < correctedChenZ N - 1))
    rw [div_le_div_iff₀ hlogz1pos hlogNpos]
    have hzl := q1_log_z_sub_one_lower N hN40
    have : (20 : ℝ) * ((1 / 20 : ℝ) * log (N : ℝ)) ≤ 20 * log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hzl (by norm_num)
    nlinarith
  have hqsum_le : qsum ≤ C₀ := by
    simpa [qsum] using hqsum N hNbig
  have hqsum0 : 0 ≤ qsum := by dsimp [qsum]; positivity
  have h𝔖pos : 0 < 𝔖 := by
    dsimp [𝔖]
    exact AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N (correctedChenZ N - 1) hz1
  have h𝔖0 : 0 ≤ 𝔖 := le_of_lt h𝔖pos
  have hgp0 : 0 ≤ MertensTheorem.goldbachSieveProduct N (correctedChenZ N) := by
    unfold MertensTheorem.goldbachSieveProduct
    apply Finset.prod_nonneg
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hc⟩
    have hpp : p.Prime := hc.1
    have hp2 : 2 ≤ p := hpp.two_le
    have hpos : 0 < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
      rw [div_le_iff₀ hpos]
      have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      linarith
    linarith
  calc
    q1MainTermSum N ≤ liN * MertensTheorem.goldbachSieveProduct N (correctedChenZ N) * qsum := hmain
    _ = liN * (pp * 𝔖) * qsum := by rw [hgp]
    _ ≤ liN * ((a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖) * qsum := by
          have h1 : pp * 𝔖 ≤ (a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖 := by
            exact mul_le_mul_of_nonneg_right hpp h𝔖0
          have h2 : 0 ≤ liN * qsum := mul_nonneg hli0 hqsum0
          calc
            liN * (pp * 𝔖) * qsum = (liN * qsum) * (pp * 𝔖) := by ring
            _ ≤ (liN * qsum) * ((a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖) := by
                  exact mul_le_mul_of_nonneg_left h1 h2
            _ = liN * ((a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖) * qsum := by ring
    _ ≤ liN * ((a₂ * (20 / log (N : ℝ))) * 𝔖) * qsum := by
          have h1 : a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ a₂ * (20 / log (N : ℝ)) := by
            have hc20 : 0 ≤ a₂ := le_of_lt ha₂pos
            calc
              a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ) = a₂ * (1 / log ((correctedChenZ N - 1 : ℕ) : ℝ)) := by ring
              _ ≤ a₂ * (20 / log (N : ℝ)) := mul_le_mul_of_nonneg_left hlog hc20
          have h2 : 0 ≤ liN * qsum := mul_nonneg hli0 hqsum0
          have h3 : (a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖 ≤ (a₂ * (20 / log (N : ℝ))) * 𝔖 := by
            exact mul_le_mul_of_nonneg_right h1 h𝔖0
          calc
            liN * ((a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖) * qsum = (liN * qsum) * ((a₂ / log ((correctedChenZ N - 1 : ℕ) : ℝ)) * 𝔖) := by ring
            _ ≤ (liN * qsum) * ((a₂ * (20 / log (N : ℝ))) * 𝔖) := by
                  exact mul_le_mul_of_nonneg_left h3 h2
            _ = liN * ((a₂ * (20 / log (N : ℝ))) * 𝔖) * qsum := by ring
    _ = (N : ℝ) / log (N : ℝ) * (a₂ * (20 / log (N : ℝ))) * 𝔖 * qsum := by
          rw [hli]
          ring
    _ ≤ (N : ℝ) / log (N : ℝ) * (a₂ * (20 / log (N : ℝ))) * 𝔖 * C₀ := by
          have h1 : 0 ≤ (N : ℝ) / log (N : ℝ) * (a₂ * (20 / log (N : ℝ))) * 𝔖 := by
            have h1a : 0 ≤ (N : ℝ) / log (N : ℝ) :=
              div_nonneg (by positivity : 0 ≤ (N : ℝ)) (le_of_lt hlogNpos)
            have h1b : 0 ≤ a₂ * (20 / log (N : ℝ)) :=
              mul_nonneg (le_of_lt ha₂pos) (div_nonneg (by norm_num) (le_of_lt hlogNpos))
            exact mul_nonneg (mul_nonneg h1a h1b) h𝔖0
          exact mul_le_mul_of_nonneg_left hqsum_le h1
    _ = (20 * a₂ * C₀) * 𝔖 * (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          field_simp [hlogNpos.ne']
    _ = C₁ * AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
          (N : ℝ) / (log (N : ℝ)) ^ 2 := by
          dsimp [C₁, 𝔖]

end
end MathlibNt.SieveTheory.SwitchingPrinciple
