import Mathlib
import Architect

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:erdos-weight"
  (statement := /-- For a natural number $n$, the Erd\H{o}s weight is
  $\nu_0(n)=(n\log n)^{-1}$, with Lean's real logarithm convention used outside
  the range $n\geq 2$. -/)
  (title := /-- Erd\H{o}s weight -/)
  (latexEnv := "definition")]
noncomputable def erdos_weight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ))

@[blueprint "def:erdos-sum"
  (statement := /-- For a set $A\subseteq\mathbb{N}$, the Erd\H{o}s sum is
  $f(A)=\sum_{n\in A}\nu_0(n)$, represented as an unconditional sum over
  $\mathbb{N}$ by the indicator of $A$. -/)
  (title := /-- Erd\H{o}s sum -/)
  (latexEnv := "definition")]
noncomputable def erdos_sum (A : Set ℕ) : ℝ :=
  ∑' n : ℕ, A.indicator erdos_weight n

@[blueprint "def:primitive-set"
  (statement := /-- A set $A\subseteq\mathbb{N}$ is primitive if it is an
  antichain for divisibility: whenever $a,b\in A$ are distinct, $a\nmid b$. Since
  the quantification is ordered, this is equivalent to saying that no two
  distinct elements of $A$ divide one another. -/)
  (title := /-- Primitive sets -/)
  (latexEnv := "definition")]
def primitive_set (A : Set ℕ) : Prop :=
  IsAntichain (fun a b : ℕ => a ∣ b) A

@[blueprint "def:supported-above"
  (statement := /-- A set $A\subseteq\mathbb{N}$ is supported above the real
  threshold $x$ if every member $n\in A$ satisfies $x\leq n$. -/)
  (title := /-- Support above a threshold -/)
  (latexEnv := "definition")]
def supported_above (A : Set ℕ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ)

@[blueprint "def:supported-in-interval"
  (statement := /-- A set $A\subseteq\mathbb{N}$ is supported in the real
  interval $[x,X]$ if every member $n\in A$ satisfies $x\leq n\leq X$. -/)
  (title := /-- Finite interval support -/)
  (latexEnv := "definition")]
def supported_in_interval (A : Set ℕ) (x X : ℝ) : Prop :=
  ∀ n : ℕ, n ∈ A -> x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X

@[blueprint "def:mangoldt-reciprocal-partial-sum"
  (statement := /-- This is the partial reciprocal von Mangoldt sum
  $\sum_{1\leq q\leq t}\Lambda(q)/q$, expressed as an unconditional sum over
  $\mathbb{N}$. -/)
  (title := /-- Reciprocal von Mangoldt partial sum -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_reciprocal_partial_sum (t : ℝ) : ℝ :=
  ∑' q : ℕ,
    if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0

@[blueprint "def:mangoldt-dirichlet-series"
  (statement := /-- For $u>0$, this is the real Dirichlet series
  $\sum_q \Lambda(q)q^{-1-u}$ used in the proof of the non-asymptotic
  sub-invariance estimate. -/)
  (title := /-- Von Mangoldt Dirichlet series -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_dirichlet_series (u : ℝ) : ℝ :=
  ∑' q : ℕ, ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)

@[blueprint "def:mangoldt-tail-term"
  (statement := /-- For natural numbers $m$ and $q$, this is the summand
  $\Lambda(q)/(q\log^2(mq))$ appearing in the von Mangoldt tail estimates. -/)
  (title := /-- Von Mangoldt tail summand -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_tail_term (m q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q /
    ((q : ℝ) * (Real.log (((m * q : ℕ) : ℝ))) ^ 2)

@[blueprint "def:mangoldt-tail-sum"
  (statement := /-- For a natural number $m$ and a real threshold $y$, this is
  the tail $\sum_{q\geq y}\Lambda(q)/(q\log^2(mq))$. -/)
  (title := /-- Von Mangoldt tail sum -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_tail_sum (m : ℕ) (y : ℝ) : ℝ :=
  ∑' q : ℕ, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0

@[blueprint "def:tail-majorant"
  (statement := /-- For $x\geq 2$, this is the reindexed upper bound
  $\sum_{1\leq n<x} n^{-1}\sum_{q\geq\max(2,x/n)}
  \Lambda(q)/(q\log^2(nq))$ obtained after discarding the upper cutoff in the
  finite proof. -/)
  (title := /-- Reindexed tail majorant -/)
  (latexEnv := "definition")]
noncomputable def tail_majorant (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n ∧ (n : ℝ) < x then
      (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
    else 0

@[blueprint "def:cut-capacity"
  (statement := /-- For real cut parameters $x\leq X$, this is the finite cut
  capacity
  $\sum_{x\leq r\leq X}(r\log^2 r)^{-1}
  \sum_{q\mid r,\ r/q<x}\Lambda(q)$ arising from the downward von Mangoldt
  chain. -/)
  (title := /-- Finite von Mangoldt cut capacity -/)
  (latexEnv := "definition")]
noncomputable def cut_capacity (x X : ℝ) : ℝ :=
  ∑' r : ℕ,
    if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
      (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
        (∑ q ∈ r.divisors,
          if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
    else 0

@[blueprint "def:erdos1196-bound"
  (statement := /-- The explicit formal version of the asymptotic conclusion in
  Erd\H{o}s--S\'ark\"ozy--Szemer\'edi problem \#1196 with constant $C$: for every
  real $x\geq 2$ and every primitive set $A\subseteq\mathbb{N}$ supported in
  $[x,\infty)$, the series defining $f(A)$ is summable and its sum satisfies
  $f(A)\leq 1+C/\log x$. -/)
  (title := /-- Quantitative infinite-support bound -/)
  (latexEnv := "definition")]
def erdos1196_bound (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x -> ∀ A : Set ℕ,
      primitive_set A -> supported_above A x ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ 1 + C / Real.log x

@[blueprint "def:erdos1196-finite-bound"
  (statement := /-- The finite-support version of \cref{def:erdos1196-bound}:
  for every real $2\leq x\leq X$ and every primitive set $A\subseteq\mathbb{N}$
  supported in $[x,X]$, one has $f(A)\leq 1+C/\log x$. -/)
  (title := /-- Quantitative finite-support bound -/)
  (latexEnv := "definition")]
def erdos1196_finite_bound (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ x X : ℝ, 2 ≤ x -> x ≤ X -> ∀ A : Set ℕ,
      primitive_set A -> supported_in_interval A x X ->
        erdos_sum A ≤ 1 + C / Real.log x

@[blueprint "lem:von-mangoldt-divisor-sum"
  (statement := /-- For every $n\in\mathbb{N}$, the sum of the von Mangoldt
  function over the finite divisor set $\operatorname{divisors}(n)$ satisfies
  $\sum_{q\in\operatorname{divisors}(n)}\Lambda(q)=\log n$; in particular,
  the case $n=0$ uses the empty finite divisor set convention. -/)
  (proof := /-- Apply the standard divisor-sum identity for the von Mangoldt
  function in Mathlib, which states exactly that the finite sum over
  $\operatorname{divisors}(n)$ is $\log n$ for every $n\in\mathbb{N}$. -/)
  (title := /-- Divisor sum of the von Mangoldt function -/)
  (latexEnv := "lemma")]
lemma von_mangoldt_divisor_sum (n : ℕ) :
    (∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q) = Real.log (n : ℝ) := by
  simpa using (ArithmeticFunction.vonMangoldt_sum (n := n))

@[blueprint "lem:mertens-von-mangoldt-reciprocal"
  (statement := /-- There is a real constant $C\geq 0$ such that, for every
  real number $t\geq 1$, the reciprocal von Mangoldt partial sum satisfies
  $|\sum_{1\leq q\leq t}\Lambda(q)/q-\log t|\leq C$. -/)
  (proof := /-- By \cref{def:mangoldt-reciprocal-partial-sum}, the
  unconditional sum is first reduced to the finite sum over
  $1\leq q\leq\lfloor t\rfloor$. For a natural number $n\geq 1$, the
  arithmetic-function convolution identity $\Lambda*\zeta=\log$ gives
  $\sum_{m\leq n}\log m=\sum_{q\leq n}\Lambda(q)\lfloor n/q\rfloor$.
  The inequalities $\lfloor n/q\rfloor\leq n/q$ and
  $n/q-1\leq\lfloor n/q\rfloor$, together with nonnegativity of
  $\Lambda(q)$, compare this weighted divisor sum with
  $n\sum_{q\leq n}\Lambda(q)/q$ up to the Chebyshev sum
  $\sum_{q\leq n}\Lambda(q)$. Mathlib's Chebyshev bound
  $\sum_{q\leq n}\Lambda(q)\leq (\log 4+4)n$, the elementary inequality
  $\log(n!)\leq n\log n$, and the logarithmic Stirling lower bound for
  $\log(n!)$ show that
  $|\sum_{q\leq n}\Lambda(q)/q-\log n|$ is bounded uniformly in
  $n\geq 1$. Finally, for real $t\geq 1$, put
  $n=\lfloor t\rfloor$. Since $n\leq t<n+1\leq 2n$, the difference between
  $\log t$ and $\log n$ is at most $\log 2$, so enlarging the constant gives
  the stated real-variable bound. -/)
  (title := /-- Mertens estimate for reciprocal von Mangoldt sums -/)
  (latexEnv := "lemma")]
lemma mertens_von_mangoldt_reciprocal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ C := by
  classical
  let c0 : ℝ := Real.log (2 * Real.pi) / 2
  have htsum : ∀ t : ℝ, 0 ≤ t ->
      mangoldt_reciprocal_partial_sum t =
        ∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
    intro t ht
    rw [mangoldt_reciprocal_partial_sum]
    calc
      (∑' q : ℕ,
          if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0)
          = ∑ q ∈ Finset.Icc 1 ⌊t⌋₊,
              if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0 := by
            refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
              (s := Finset.Icc 1 ⌊t⌋₊)
              (f := fun q : ℕ =>
                if 1 ≤ q ∧ (q : ℝ) ≤ t then ArithmeticFunction.vonMangoldt q / (q : ℝ) else 0) ?_
            intro q hq
            by_cases hcond : 1 ≤ q ∧ (q : ℝ) ≤ t
            · exfalso
              exact hq (Finset.mem_Icc.mpr ⟨hcond.1, Nat.le_floor hcond.2⟩)
            · simp [hcond]
      _ = ∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            rcases Finset.mem_Icc.mp hq with ⟨hq1, hqfloor⟩
            have hqt : (q : ℝ) ≤ t := by
              exact (Nat.cast_le.mpr hqfloor).trans (Nat.floor_le ht)
            simp [hq1, hqt]
  have hsumlog : ∀ n : ℕ,
      (∑ m ∈ Finset.Ioc 0 n, Real.log (m : ℝ)) = Real.log (n.factorial : ℝ) := by
    intro n
    rw [← Real.log_prod]
    · congr 1
      rw [← Finset.Ico_succ_succ_eq_Ioc (0 : ℕ) n]
      simpa [Order.succ_eq_add_one] using (show (∏ x ∈ Finset.Ico 1 (n + 1), (x : ℝ)) = (n.factorial : ℝ) by
        rw [← Nat.cast_prod]
        norm_num [Finset.prod_Ico_id_eq_factorial])
    · intro m hm
      have hmpos : 0 < m := (Finset.mem_Ioc.mp hm).1
      exact_mod_cast (ne_of_gt hmpos)
  have hB : ∀ n : ℕ,
      (∑ m ∈ Finset.Ioc 0 n, Real.log (m : ℝ)) =
        ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ) := by
    intro n
    simpa [ArithmeticFunction.vonMangoldt_mul_zeta] using
      (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n)
  have hfloor_upper : ∀ n q : ℕ, ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / (q : ℝ) := by
    intro n q
    exact Nat.cast_div_le
  have hfloor_lower : ∀ n q : ℕ, (n : ℝ) / (q : ℝ) - 1 ≤ ((n / q : ℕ) : ℝ) := by
    intro n q
    by_cases hq : q = 0
    · subst q
      norm_num
    · have hlt : (n : ℝ) / (q : ℝ) < (⌊(n : ℝ) / (q : ℝ)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one ((n : ℝ) / (q : ℝ))
      rw [Nat.floor_div_natCast] at hlt
      rw [Nat.floor_natCast] at hlt
      linarith
  have hpsi_le : ∀ n : ℕ,
      (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q) ≤
        (Real.log 4 + 4) * (n : ℝ) := by
    intro n
    simpa [Chebyshev.psi, Nat.floor_natCast] using
      (Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity))
  have hlogfac_upper : ∀ n : ℕ,
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hfac : (n.factorial : ℝ) ≤ (n ^ n : ℕ) := by
        exact_mod_cast (Nat.factorial_le_pow n)
      have hpos : 0 < (n.factorial : ℝ) := by positivity
      have hlog := Real.log_le_log hpos hfac
      simpa [Nat.cast_pow, Real.log_pow] using hlog
  have hlogfac_lower : ∀ n : ℕ, 1 ≤ n ->
      (n : ℝ) * Real.log (n : ℝ) - (1 + |c0|) * (n : ℝ) ≤
        Real.log (n.factorial : ℝ) := by
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hs := Stirling.le_log_factorial_stirling (n := n) hn0
    have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn)
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    have hc : -|c0| * (n : ℝ) ≤ c0 := by
      by_cases hc0 : 0 ≤ c0
      · have hleft : -|c0| * (n : ℝ) ≤ 0 := by
          nlinarith [abs_nonneg c0, hnnonneg]
        exact hleft.trans hc0
      · have hc0lt : c0 < 0 := lt_of_not_ge hc0
        have habs : |c0| = -c0 := abs_of_neg hc0lt
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [habs]
        nlinarith
    have hc' : -|Real.log (2 * Real.pi) / 2| * (n : ℝ) ≤ Real.log (2 * Real.pi) / 2 := by
      simpa [c0] using hc
    nlinarith
  have hB_le_nA : ∀ n : ℕ,
      (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)) ≤
        (n : ℝ) * (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqpos_nat : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt q := ArithmeticFunction.vonMangoldt_nonneg
    calc
      ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)
          ≤ ArithmeticFunction.vonMangoldt q * ((n : ℝ) / (q : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (hfloor_upper n q) hΛ
      _ = (n : ℝ) * (ArithmeticFunction.vonMangoldt q / (q : ℝ)) := by
            field_simp [hqpos.ne']
  have hnA_le_B_psi : ∀ n : ℕ,
      (n : ℝ) * (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) ≤
        (∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)) +
          ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q := by
    intro n
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro q hq
    have hqpos_nat : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt q := ArithmeticFunction.vonMangoldt_nonneg
    have hdiv_le : (n : ℝ) / (q : ℝ) ≤ ((n / q : ℕ) : ℝ) + 1 := by
      linarith [hfloor_lower n q]
    calc
      (n : ℝ) * (ArithmeticFunction.vonMangoldt q / (q : ℝ))
          = ArithmeticFunction.vonMangoldt q * ((n : ℝ) / (q : ℝ)) := by
            field_simp [hqpos.ne']
      _ ≤ ArithmeticFunction.vonMangoldt q * (((n / q : ℕ) : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_left hdiv_le hΛ
      _ = ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ) +
            ArithmeticFunction.vonMangoldt q := by
            ring
  let K1 : ℝ := 1 + |c0|
  let K2 : ℝ := Real.log 4 + 4
  let Cnat : ℝ := max K1 K2
  have hK1_nonneg : 0 ≤ K1 := by
    dsimp [K1]
    positivity
  have hK2_nonneg : 0 ≤ K2 := by
    dsimp [K2]
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hCnat_nonneg : 0 ≤ Cnat := by
    exact hK1_nonneg.trans (le_max_left K1 K2)
  have hK1_le_Cnat : K1 ≤ Cnat := le_max_left K1 K2
  have hK2_le_Cnat : K2 ≤ Cnat := le_max_right K1 K2
  have hnat_ioc : ∀ n : ℕ, 1 ≤ n ->
      |(∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
        Real.log (n : ℝ)| ≤ Cnat := by
    intro n hn
    set A : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q / (q : ℝ)
    set B : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q * ((n / q : ℕ) : ℝ)
    set P : ℝ := ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q
    have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hB_eq : B = Real.log (n.factorial : ℝ) := by
      dsimp [B]
      exact (hB n).symm.trans (hsumlog n)
    have hB_le : B ≤ (n : ℝ) * A := by
      simpa [A, B] using hB_le_nA n
    have hnA_le : (n : ℝ) * A ≤ B + P := by
      simpa [A, B, P] using hnA_le_B_psi n
    have hP_le : P ≤ K2 * (n : ℝ) := by
      dsimp [P, K2]
      exact hpsi_le n
    have hA_upper : A - Real.log (n : ℝ) ≤ Cnat := by
      have hmul : (n : ℝ) * A ≤ (n : ℝ) * (Real.log (n : ℝ) + K2) := by
        have hfac := hlogfac_upper n
        rw [hB_eq] at hnA_le
        nlinarith
      have hA_le : A ≤ Real.log (n : ℝ) + K2 := le_of_mul_le_mul_left hmul hnpos
      nlinarith
    have hA_lower : -Cnat ≤ A - Real.log (n : ℝ) := by
      have hmul : (n : ℝ) * (Real.log (n : ℝ) - K1) ≤ (n : ℝ) * A := by
        have hfac := hlogfac_lower n hn
        rw [hB_eq] at hB_le
        dsimp [K1]
        nlinarith
      have hlower : Real.log (n : ℝ) - K1 ≤ A := le_of_mul_le_mul_left hmul hnpos
      nlinarith
    exact abs_le.mpr ⟨hA_lower, hA_upper⟩
  have hIoc_eq_Icc : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := by
    intro n
    ext q
    simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
  refine ⟨Cnat + Real.log 2, ?_, ?_⟩
  · have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  · intro t ht
    have ht0 : 0 ≤ t := by linarith
    let N : ℕ := ⌊t⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact (Nat.one_le_floor_iff t).mpr ht
    have hpartial := htsum t ht0
    have hnat := hnat_ioc N hN
    have hnat' :
        |(∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
          Real.log (N : ℝ)| ≤ Cnat := by
      simpa [hIoc_eq_Icc N] using hnat
    have hNpos_nat : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    have htpos : 0 < t := by linarith
    have hN_le_t : (N : ℝ) ≤ t := by
      dsimp [N]
      exact Nat.floor_le ht0
    have ht_lt_N_add_one : t < (N : ℝ) + 1 := by
      dsimp [N]
      simpa using (Nat.lt_floor_add_one t)
    have ht_le_twoN : t ≤ 2 * (N : ℝ) := by
      have hN_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlogN_le_logt : Real.log (N : ℝ) ≤ Real.log t := Real.log_le_log hNpos hN_le_t
    have hlogt_le_log2N : Real.log t ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log htpos ht_le_twoN
    have hlog2N : Real.log (2 * (N : ℝ)) = Real.log (2 : ℝ) + Real.log (N : ℝ) := by
      rw [Real.log_mul] <;> positivity
    have hlogdiff : |Real.log (N : ℝ) - Real.log t| ≤ Real.log (2 : ℝ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hlogN_le_logt), neg_sub]
      rw [hlog2N] at hlogt_le_log2N
      linarith
    rw [hpartial]
    calc
      |(∑ q ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log t|
          = |((∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log (N : ℝ)) +
              (Real.log (N : ℝ) - Real.log t)| := by
            dsimp [N]
            ring_nf
      _ ≤ |(∑ q ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log (N : ℝ)| +
            |Real.log (N : ℝ) - Real.log t| := abs_add_le _ _
      _ ≤ Cnat + Real.log (2 : ℝ) := add_le_add hnat' hlogdiff

@[blueprint "def:dirichlet-eta-real"
  (statement := /-- For a real parameter $s$, the real Dirichlet eta function is
  the real value of $(1-2^{1-s})\zeta(s)$ on the real axis.  In Lean this is
  represented as the real part of the corresponding complex expression. -/)
  (title := /-- Real Dirichlet eta function -/)
  (latexEnv := "definition")]
noncomputable def dirichlet_eta_real (s : ℝ) : ℝ :=
  (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (s : ℂ))) * riemannZeta (s : ℂ)).re

@[blueprint "lem:dirichlet-eta-positive"
  (statement := /-- For every real $s>1$, the real Dirichlet eta value
  $\eta(s)$ of \cref{def:dirichlet-eta-real} is strictly positive. -/)
  (proof := /-- Fix a real number $s$ with $1<s$.  By
  \cref{def:dirichlet-eta-real} and the real-base complex-power identity, the
  factor $2^{1-s}$ in the complex expression is the real number $2^{1-s}$.
  Since $1-s<0$ and $2>1$, one has $2^{1-s}<1$, and therefore
  $1-2^{1-s}>0$.  The standard positivity theorem for the Riemann zeta function
  on the half-line $s>1$ gives $\operatorname{Re}\zeta(s)>0$.  The complex
  power factor is real, so the real part of $(1-2^{1-s})\zeta(s)$ is
  $(1-2^{1-s})\operatorname{Re}\zeta(s)$, a product of two strictly positive
  real numbers. -/)
  (title := /-- Positivity of eta on the half-line $s>1$ -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_positive :
    ∀ s : ℝ, 1 < s -> 0 < dirichlet_eta_real s := by
  intro s hs
  unfold dirichlet_eta_real
  have hpow : (2 : ℂ) ^ ((1 : ℂ) - (s : ℂ)) = (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) := by
    symm
    simpa using (Complex.ofReal_cpow (x := (2 : ℝ)) (by norm_num) (1 - s))
  have hfactor_pos : 0 < (1 : ℝ) - (2 : ℝ) ^ (1 - s) := by
    have hlt : (2 : ℝ) ^ (1 - s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hzeta_pos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  rw [hpow]
  simpa [Complex.mul_re] using mul_pos hfactor_pos hzeta_pos

@[blueprint "lem:dirichlet-eta-mellin-transform"
  (statement := /-- For every real $s>1$, the real Dirichlet eta value of
  \cref{def:dirichlet-eta-real} is the normalized Mellin transform
  $$
    \eta(s)=\Gamma(s)^{-1}\int_0^\infty {x^{s-1}\over e^x+1}\,dx.
  $$ -/)
  (proof := /-- Fix $s>1$.  For every $x>0$, the geometric expansion
  $(e^x+1)^{-1}=\sum_{n=0}^\infty (-1)^n e^{-(n+1)x}$ is summable, and the
  exponential decay gives the summability needed to integrate the series term
  by term against $x^{s-1}\,dx$ on $(0,\infty)$.  The Mellin integral of the
  $n$th term is $(-1)^n\Gamma(s)/(n+1)^s$.  Hence the integral is
  $\Gamma(s)\sum_{n=0}^\infty (-1)^n/(n+1)^s$.  For $s>1$ this alternating
  Dirichlet series is absolutely convergent after grouping even and odd terms,
  and its value is $(1-2^{1-s})\zeta(s)$.  Dividing by $\Gamma(s)$ gives
  precisely the real value specified by \cref{def:dirichlet-eta-real}. -/)
  (title := /-- Mellin transform formula for eta -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_mellin_transform :
    ∀ s : ℝ, 1 < s ->
      dirichlet_eta_real s =
        (1 / Real.Gamma s) *
          ∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) := by
  intro s hs
  let S : ℂ := s
  have hgeom :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        HasSum (fun n : ℕ => ((-1 : ℂ) ^ n) * Real.exp (-(n + 1 : ℝ) * t))
          ((1 : ℂ) / (Real.exp t + 1)) := by
    intro t ht
    have htpos : 0 < t := ht
    have hnorm : ‖(-((Real.exp (-t) : ℝ) : ℂ))‖ < 1 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, Real.exp_neg]
      bound
    convert
      ((hasSum_geometric_of_norm_lt_one (ξ := -((Real.exp (-t) : ℝ) : ℂ)) hnorm).mul_left
        ((Real.exp (-t) : ℝ) : ℂ)) using 1
    · ext n
      rw [show -(↑n + 1) * t = -t + ↑n * (-t) by ring]
      simp [Real.exp_add, Real.exp_nat_mul, mul_comm, mul_left_comm, mul_assoc]
      rw [show -(↑t * ↑n : ℂ) = ↑n * (-↑t) by ring, Complex.exp_nat_mul]
      ring
    · rw [Real.exp_neg]
      let E : ℂ := ↑(Real.exp t)
      have hE : E ≠ 0 := by
        dsimp [E]
        exact_mod_cast Real.exp_ne_zero t
      have hE1 : E + 1 ≠ 0 := by
        dsimp [E]
        norm_cast
        positivity
      have halg : 1 / (E + 1) = E⁻¹ * (1 - -E⁻¹)⁻¹ := by
        rw [sub_neg_eq_add]
        field_simp [hE, hE1]
      simpa [E] using halg
  have hsum :
      Summable (fun n : ℕ => ‖((-1 : ℂ) ^ n)‖ / ((n + 1 : ℝ)) ^ S.re) := by
    convert (Real.summable_one_div_nat_add_rpow 1 s).2 hs using 1
    ext n
    simp [S, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have hs0 : 0 < S.re := by
    dsimp [S]
    exact lt_trans zero_lt_one hs
  have hp : ∀ n : ℕ, ((-1 : ℂ) ^ n) = 0 ∨ 0 < (n + 1 : ℝ) := by
    intro n
    right
    positivity
  have hmellin :
      HasSum
        (fun n : ℕ => Complex.Gamma S * ((-1 : ℂ) ^ n) / ((n + 1 : ℝ) : ℂ) ^ S)
        (mellin (fun t : ℝ => (1 : ℂ) / (Real.exp t + 1)) S) := by
    exact hasSum_mellin hp hs0 hgeom hsum
  have hmellin_real :
      mellin (fun t : ℝ => (1 : ℂ) / (Real.exp t + 1)) S =
        ((∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) : ℝ) : ℂ) := by
    rw [mellin]
    simp only [smul_eq_mul]
    rw [← integral_complex_ofReal]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hxpos : 0 < x := hx
    have hpow : (x : ℂ) ^ (S - 1) = ((x ^ (s - 1) : ℝ) : ℂ) := by
      dsimp [S]
      symm
      simpa using (Complex.ofReal_cpow (x := x) hxpos.le (s - 1))
    simpa [hpow, div_eq_mul_inv]
  have hcomplex :
      mellin (fun t : ℝ => (1 : ℂ) / (Real.exp t + 1)) S =
        Complex.Gamma S * (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - S)) * riemannZeta S) := by
    have hs1 : 1 < S.re := by
      simpa [S] using hs
    have hf : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) ^ S)) := by
      simpa using
        (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℂ) ^ S)) 1).2
          (Complex.summable_one_div_nat_cpow.mpr hs1)
    have hzeta_nat : riemannZeta S = ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) ^ S) := by
      simpa using zeta_eq_tsum_one_div_nat_add_one_cpow (s := S) hs1
    have hg : Summable (fun n : ℕ => ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ S)) := by
      apply Summable.of_norm
      convert hsum using 1
      ext n
      have hbase : (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by
        norm_num
      rw [hbase, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (x := ((n + 1 : ℕ) : ℝ))
        (by positivity) S]
      simp [S, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    have hinj_even : Function.Injective (fun n : ℕ => 2 * n) := by
      exact mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
    have hinj_odd : Function.Injective (fun n : ℕ => 2 * n + 1) := by
      intro a b h
      exact hinj_even (Nat.succ.inj h)
    have heven_scaled :
        (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) =
          (2 : ℂ) ^ (-S) * riemannZeta S := by
      rw [hzeta_nat]
      rw [← tsum_mul_left]
      congr 1
      ext n
      rw [show (2 * n + 2 : ℕ) = 2 * (n + 1) by ring]
      rw [show (((2 * (n + 1) : ℕ) : ℂ) ^ S) =
          (2 : ℂ) ^ S * (((n + 1 : ℕ) : ℂ) ^ S) by
        simpa using (Complex.natCast_mul_natCast_cpow 2 (n + 1) S)]
      rw [Complex.cpow_neg]
      field_simp [Complex.natCast_add_one_cpow_ne_zero 1 S,
        Complex.natCast_add_one_cpow_ne_zero n S]
    have hzeta_split :
        (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) +
          (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) = riemannZeta S := by
      rw [hzeta_nat]
      simpa [Nat.add_assoc] using
        (tsum_even_add_odd
          (f := fun k : ℕ => 1 / (((k + 1 : ℕ) : ℂ) ^ S))
          (hf.comp_injective hinj_even) (hf.comp_injective hinj_odd))
    have heta_split :
        (∑' n : ℕ, ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ S)) =
          (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) -
            (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) := by
      rw [← tsum_even_add_odd
        (f := fun k : ℕ => ((-1 : ℂ) ^ k) / (((k + 1 : ℕ) : ℂ) ^ S))
        (hg.comp_injective hinj_even) (hg.comp_injective hinj_odd)]
      rw [sub_eq_add_neg, ← tsum_neg]
      congr 1
      · apply tsum_congr
        intro n
        simp [pow_mul]
      · apply tsum_congr
        intro n
        rw [show (2 * n + 1 + 1 : ℕ) = 2 * n + 2 by ring]
        simp [pow_succ, pow_mul, div_eq_mul_inv]
    have htwo : (2 : ℂ) ^ ((1 : ℂ) - S) = 2 * (2 : ℂ) ^ (-S) := by
      rw [show ((1 : ℂ) - S) = 1 + (-S) by ring]
      rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
    have heta_tsum :
        (∑' n : ℕ, ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ S)) =
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - S)) * riemannZeta S := by
      rw [heta_split]
      rw [show (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) -
          (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) =
          ((∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℂ) ^ S)) +
            (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S))) -
            2 * (∑' n : ℕ, 1 / (((2 * n + 2 : ℕ) : ℂ) ^ S)) by ring]
      rw [hzeta_split, heven_scaled, htwo]
      ring
    rw [← hmellin.tsum_eq]
    rw [← heta_tsum]
    rw [← tsum_mul_left]
    congr 1
    ext n
    simp [div_eq_mul_inv]
    ring
  have hInt :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1)) =
        Real.Gamma s * dirichlet_eta_real s := by
    have hcomplex' :
        ((∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) : ℝ) : ℂ) =
          Complex.Gamma S * (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - S)) * riemannZeta S) := by
      exact hmellin_real.symm.trans hcomplex
    have hre := congrArg Complex.re hcomplex'
    rw [dirichlet_eta_real]
    simp [S, Complex.Gamma_ofReal, Complex.mul_re] at hre ⊢
    linarith
  have hγ : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos (lt_trans zero_lt_one hs)).ne'
  rw [hInt]
  field_simp [hγ]

@[blueprint "lem:gamma-logistic-expectation-eq-mellin-integral"
  (statement := /-- For every real $s>1$, the expectation of
  $h(x)=(1+e^{-x})^{-1}$ under `ProbabilityTheory.gammaMeasure s 1` is the
  normalized Mellin integral
  $$
    \Gamma(s)^{-1}\int_0^\infty {x^{s-1}\over e^x+1}\,dx.
  $$ -/)
  (proof := /-- Fix $s>1$.  Unfold `ProbabilityTheory.gammaMeasure` and apply
  the Bochner-integral formula for a measure defined by `withDensity`, with
  density `ProbabilityTheory.gammaPDF s 1`.  The density is measurable and
  finite because it is `ENNReal.ofReal` of the real gamma density.  Rewrite the
  right-hand side as the integral over the whole real line of the indicator of
  $(0,\infty)$ times the integrand
  $\Gamma(s)^{-1}x^{s-1}/(e^x+1)$.  It remains to compare the two integrands
  pointwise.  For $x>0$, `ProbabilityTheory.gammaPDF_of_nonneg` gives the
  density
  $\Gamma(s)^{-1}x^{s-1}e^{-x}$, and the identity
  $$
    {1\over 1+e^{-x}}\,\Gamma(s)^{-1}x^{s-1}e^{-x}
      = \Gamma(s)^{-1}{x^{s-1}\over e^x+1}
  $$
  follows by clearing the nonzero denominators, using positivity of
  $\Gamma(s)$ and of $e^x$.  For $x<0$, `ProbabilityTheory.gammaPDF_of_neg`
  gives density zero; for $x=0$, the factor $0^{s-1}$ is zero because
  $s-1>0$.  Hence the whole-line integral is exactly the indicated integral on
  $(0,\infty)$, with the constant $\Gamma(s)^{-1}$ pulled out. -/)
  (title := /-- Gamma expectation as a Mellin integral -/)
  (latexEnv := "lemma")]
lemma gamma_logistic_expectation_eq_mellin_integral :
    ∀ s : ℝ, 1 < s ->
      (∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1)) =
        (1 / Real.Gamma s) *
          ∫ x : ℝ in Set.Ioi (0 : ℝ), x ^ (s - 1) / (Real.exp x + 1) := by
  intro s hs
  rw [ProbabilityTheory.gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 < x
    · have hnonneg :
          0 ≤ 1 ^ s / Real.Gamma s * x ^ (s - 1) * Real.exp (-(1 * x)) := by
        simpa [ProbabilityTheory.gammaPDFReal, if_pos hx.le] using
          ProbabilityTheory.gammaPDFReal_nonneg (a := s) (r := 1) (by linarith) (by norm_num) x
      have hpdf :
          (ProbabilityTheory.gammaPDF s 1 x).toReal =
            1 ^ s / Real.Gamma s * x ^ (s - 1) * Real.exp (-(1 * x)) := by
        rw [ProbabilityTheory.gammaPDF_of_nonneg hx.le]
        exact ENNReal.toReal_ofReal hnonneg
      have hGamma_ne : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < s)).ne'
      rw [hpdf]
      simp [Set.mem_Ioi, hx, Real.exp_neg, div_eq_mul_inv]
      field_simp [hGamma_ne, Real.exp_ne_zero]
    · have hxle : x ≤ 0 := le_of_not_gt hx
      rcases lt_or_eq_of_le hxle with hxlt | hxeq
      · have hpdf : ProbabilityTheory.gammaPDF s 1 x = 0 := ProbabilityTheory.gammaPDF_of_neg hxlt
        simp [hpdf, Set.mem_Ioi, hx]
      · subst x
        have hsne : s - 1 ≠ 0 := by linarith
        have hnonneg :
            0 ≤ 1 ^ s / Real.Gamma s * (0 : ℝ) ^ (s - 1) * Real.exp (-(1 * 0)) := by
          simp [Real.zero_rpow hsne]
        have hpdf :
            (ProbabilityTheory.gammaPDF s 1 0).toReal =
              1 ^ s / Real.Gamma s * (0 : ℝ) ^ (s - 1) * Real.exp (-(1 * 0)) := by
          rw [ProbabilityTheory.gammaPDF_of_nonneg le_rfl]
          exact ENNReal.toReal_ofReal hnonneg
        simp [hpdf, Set.mem_Ioi, hx, Real.zero_rpow hsne]
  · simpa [ProbabilityTheory.gammaPDF] using
      ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal s 1)
  · filter_upwards with x
    simp [ProbabilityTheory.gammaPDF]

@[blueprint "lem:dirichlet-eta-gamma-expectation"
  (statement := /-- For every real $s>1$, the eta value of
  \cref{def:dirichlet-eta-real} is the expectation of
  $h(x)=(1+e^{-x})^{-1}$ against the gamma distribution of shape $s$ and
  scale $1$.  In Lean this gamma distribution is
  `ProbabilityTheory.gammaMeasure s 1`. -/)
  (proof := /-- Fix $s>1$.  By
  \cref{lem:gamma-logistic-expectation-eq-mellin-integral}, the gamma
  expectation is
  $$\Gamma(s)^{-1}\int_0^\infty {x^{s-1}\over e^x+1}\,dx.$$
  By \cref{lem:dirichlet-eta-mellin-transform}, the same normalized Mellin
  integral is the real eta value of \cref{def:dirichlet-eta-real}.  Combining
  these two identities gives the asserted gamma-expectation representation of
  $\eta(s)$. -/)
  (title := /-- Gamma-expectation representation of eta -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_gamma_expectation :
    ∀ s : ℝ, 1 < s ->
      dirichlet_eta_real s =
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1) := by
  intro s hs
  exact (dirichlet_eta_mellin_transform s hs).trans
    (gamma_logistic_expectation_eq_mellin_integral s hs).symm

@[blueprint "lem:gamma-logistic-expectation-mono-of-shape-le"
  (statement := /-- For all real numbers $a$ and $b$ with $0<a\leq b$, the
  expectation of $h(x)=(1+e^{-x})^{-1}$ under the gamma law of shape $a$ and
  scale $1$ is at most the corresponding expectation under the gamma law of
  shape $b$ and scale $1$. -/)
  (proof := /-- Fix real numbers $a$ and $b$ with $0<a\leq b$, and put
  $c=b-a$ and $K=\Gamma(a)/\Gamma(b)$.  If $b=a$, the two measures are equal.
  Otherwise $c>0$.  The gamma density formula gives
  $$
    \gamma_{b,1}=\bigl(K\max(x,0)^c\bigr)\gamma_{a,1}
  $$
  as a measure identity.  Let $w(x)=K\max(x,0)^c$ and let
  $t=(1/K)^{1/c}$, so that $w(t)=1$.  Both $w$ and
  $x\mapsto(1+e^{-x})^{-1}$ are non-decreasing, hence for every real $x$,
  $$
    \bigl((1+e^{-x})^{-1}-(1+e^{-t})^{-1}\bigr)(w(x)-1)\geq 0.
  $$
  Integrating this inequality with respect to the gamma law of shape $a$,
  expanding the product, and using the normalization
  $\int w\,d\gamma_{a,1}=1$ gives
  $$
    \int (1+e^{-x})^{-1}\,d\gamma_{a,1}
      \leq \int w(x)(1+e^{-x})^{-1}\,d\gamma_{a,1}.
  $$
  The measure identity identifies the last integral with the corresponding
  expectation under the gamma law of shape $b$, which is the desired
  inequality. -/)
  (title := /-- Pairwise gamma-shape comparison for logistic expectations -/)
  (latexEnv := "lemma")]
lemma gamma_logistic_expectation_mono_of_shape_le :
    ∀ ⦃a b : ℝ⦄, 0 < a -> a ≤ b ->
      (∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure a 1)) ≤
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure b 1) := by
  intro a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let c : ℝ := b - a
  let K : ℝ := Real.Gamma a / Real.Gamma b
  have hc : 0 ≤ c := by
    dsimp [c]
    linarith
  have hgamma_meas : AEMeasurable (ProbabilityTheory.gammaPDF a 1) MeasureTheory.volume :=
    (ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal a 1)).aemeasurable
  have hratio_meas :
      AEMeasurable (fun x : ℝ => ENNReal.ofReal (K * (max x 0) ^ c)) MeasureTheory.volume := by
    dsimp [K, c]
    fun_prop
  have htilt :
      ProbabilityTheory.gammaMeasure b 1 =
        (ProbabilityTheory.gammaMeasure a 1).withDensity
          (fun x : ℝ => ENNReal.ofReal (K * (max x 0) ^ c)) := by
    rw [ProbabilityTheory.gammaMeasure, ProbabilityTheory.gammaMeasure]
    rw [← MeasureTheory.withDensity_mul₀ hgamma_meas hratio_meas]
    apply MeasureTheory.withDensity_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with x hx0
    by_cases hx : 0 < x
    · have hxle : 0 ≤ x := hx.le
      rw [ProbabilityTheory.gammaPDF_of_nonneg hxle]
      rw [Pi.mul_apply, ProbabilityTheory.gammaPDF_of_nonneg hxle]
      dsimp [K, c]
      rw [max_eq_left hxle]
      rw [← ENNReal.ofReal_mul]
      · congr 1
        have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
        have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
        rw [Real.one_rpow, Real.one_rpow]
        field_simp [hGa, hGb]
        rw [← Real.rpow_add hx]
        congr 1
        ring
      · positivity
    · have hxlt : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      rw [ProbabilityTheory.gammaPDF_of_neg hxlt]
      rw [Pi.mul_apply, ProbabilityTheory.gammaPDF_of_neg hxlt]
      simp
  by_cases hba : b = a
  · subst b
    exact le_rfl
  have hcpos : 0 < c := by
    refine lt_of_le_of_ne' hc ?_
    intro hc0
    apply hba
    dsimp [c] at hc0
    linarith
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  let t : ℝ := (1 / K) ^ (c⁻¹)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_cross : K * (max t 0) ^ c = 1 := by
    have ht_eq : max t 0 = t := max_eq_left ht_nonneg
    rw [ht_eq]
    dsimp [t]
    rw [Real.rpow_inv_rpow]
    · field_simp [hKpos.ne']
    · positivity
    · exact hcpos.ne'
  have hpoint :
      ∀ x : ℝ,
        0 ≤ (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1) := by
    intro x
    by_cases hxt : x ≤ t
    · have hsig : Real.sigmoid x ≤ Real.sigmoid t := Real.sigmoid_monotone hxt
      have hmax : max x 0 ≤ max t 0 := max_le_max hxt le_rfl
      have hpow : (max x 0) ^ c ≤ (max t 0) ^ c := by
        exact Real.rpow_le_rpow (le_max_right x 0) hmax hc
      have hw : K * (max x 0) ^ c ≤ 1 := by
        calc
          K * (max x 0) ^ c ≤ K * (max t 0) ^ c := by gcongr
          _ = 1 := ht_cross
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hsig) (sub_nonpos.mpr hw)
    · have htx : t ≤ x := le_of_not_ge hxt
      have hsig : Real.sigmoid t ≤ Real.sigmoid x := Real.sigmoid_monotone htx
      have hmax : max t 0 ≤ max x 0 := max_le_max htx le_rfl
      have hpow : (max t 0) ^ c ≤ (max x 0) ^ c := by
        exact Real.rpow_le_rpow (le_max_right t 0) hmax hc
      have hw : 1 ≤ K * (max x 0) ^ c := by
        calc
          1 = K * (max t 0) ^ c := ht_cross.symm
          _ ≤ K * (max x 0) ^ c := by gcongr
      exact mul_nonneg (sub_nonneg.mpr hsig) (sub_nonneg.mpr hw)
  have hdens_real :
      ∀ x : ℝ, (ENNReal.ofReal (K * (max x 0) ^ c)).toReal = K * (max x 0) ^ c := by
    intro x
    rw [ENNReal.toReal_ofReal]
    positivity
  have hmass :
      ∫ x : ℝ, K * (max x 0) ^ c ∂(ProbabilityTheory.gammaMeasure a 1) = 1 := by
    calc
      ∫ x : ℝ, K * (max x 0) ^ c ∂(ProbabilityTheory.gammaMeasure a 1)
          = ∫ x : ℝ, (ENNReal.ofReal (K * (max x 0) ^ c)).toReal ∂(ProbabilityTheory.gammaMeasure a 1) := by
            simp_rw [hdens_real]
      _ = ∫ x : ℝ, (1 : ℝ) ∂((ProbabilityTheory.gammaMeasure a 1).withDensity
            (fun x : ℝ => ENNReal.ofReal (K * (max x 0) ^ c))) := by
            rw [integral_withDensity_eq_integral_toReal_smul₀ (f_meas := by fun_prop)
              (hf_lt_top := by simp) (fun _ : ℝ => (1 : ℝ))]
            simp
      _ = ∫ x : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gammaMeasure b 1) := by
            rw [← htilt]
      _ = 1 := by
            haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gammaMeasure b 1) :=
              ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb (by norm_num)
            simp
  haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gammaMeasure a 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha (by norm_num)
  have hmu_one : ∫ x : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gammaMeasure a 1) = 1 := by
    simp
  have hf_int : MeasureTheory.Integrable Real.sigmoid (ProbabilityTheory.gammaMeasure a 1) :=
    MeasureTheory.Integrable.of_mem_Icc 0 1 (by fun_prop)
      (Filter.Eventually.of_forall fun x => ⟨Real.sigmoid_nonneg x, Real.sigmoid_le_one x⟩)
  have hlintegral :
      (∫⁻ x, ENNReal.ofReal (K * (max x 0) ^ c) ∂(ProbabilityTheory.gammaMeasure a 1)) ≠
        (⊤ : ENNReal) := by
    haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gammaMeasure b 1) :=
      ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb (by norm_num)
    have hfinite : ((ProbabilityTheory.gammaMeasure b 1) Set.univ) < (⊤ : ENNReal) :=
      MeasureTheory.measure_lt_top (ProbabilityTheory.gammaMeasure b 1) Set.univ
    rw [htilt, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at hfinite
    simpa using (ne_of_lt hfinite)
  have hw_int :
      MeasureTheory.Integrable (fun x : ℝ => K * (max x 0) ^ c)
        (ProbabilityTheory.gammaMeasure a 1) := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hlintegral
    · fun_prop (disch := positivity)
    · exact Filter.Eventually.of_forall fun x => by positivity
  have hwf_int :
      MeasureTheory.Integrable (fun x : ℝ => K * (max x 0) ^ c * Real.sigmoid x)
        (ProbabilityTheory.gammaMeasure a 1) := by
    refine MeasureTheory.Integrable.mono' hw_int ?_ ?_
    · fun_prop (disch := positivity)
    · exact Filter.Eventually.of_forall fun x => by
        have hw0 : 0 ≤ K * (max x 0) ^ c := by positivity
        have hprod0 : 0 ≤ K * (max x 0) ^ c * Real.sigmoid x :=
          mul_nonneg hw0 (Real.sigmoid_nonneg x)
        rw [Real.norm_of_nonneg hprod0]
        exact mul_le_of_le_one_right hw0 (Real.sigmoid_le_one x)
  have hwt_int :
      MeasureTheory.Integrable (fun x : ℝ => Real.sigmoid t * (K * (max x 0) ^ c))
        (ProbabilityTheory.gammaMeasure a 1) :=
    hw_int.const_mul (Real.sigmoid t)
  have hconst_int :
      MeasureTheory.Integrable (fun _ : ℝ => Real.sigmoid t)
        (ProbabilityTheory.gammaMeasure a 1) := by
    fun_prop
  have hcov_nonneg :
      0 ≤ ∫ x : ℝ,
          (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1)
            ∂(ProbabilityTheory.gammaMeasure a 1) := by
    exact MeasureTheory.integral_nonneg
      (μ := ProbabilityTheory.gammaMeasure a 1)
      (f := fun x : ℝ => (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1))
      hpoint
  have hcov_eq :
      ∫ x : ℝ, (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1)
          ∂(ProbabilityTheory.gammaMeasure a 1)
        = ∫ x : ℝ, K * (max x 0) ^ c * Real.sigmoid x
            ∂(ProbabilityTheory.gammaMeasure a 1)
          - ∫ x : ℝ, Real.sigmoid x ∂(ProbabilityTheory.gammaMeasure a 1) := by
    calc
      ∫ x : ℝ, (Real.sigmoid x - Real.sigmoid t) * (K * (max x 0) ^ c - 1)
          ∂(ProbabilityTheory.gammaMeasure a 1)
          = ∫ x : ℝ,
              (K * (max x 0) ^ c * Real.sigmoid x - Real.sigmoid x) -
                (Real.sigmoid t * (K * (max x 0) ^ c) - Real.sigmoid t)
              ∂(ProbabilityTheory.gammaMeasure a 1) := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by ring
      _ = (∫ x : ℝ, K * (max x 0) ^ c * Real.sigmoid x
              ∂(ProbabilityTheory.gammaMeasure a 1) -
            ∫ x : ℝ, Real.sigmoid x ∂(ProbabilityTheory.gammaMeasure a 1)) -
          (∫ x : ℝ, Real.sigmoid t * (K * (max x 0) ^ c)
              ∂(ProbabilityTheory.gammaMeasure a 1) -
            ∫ x : ℝ, Real.sigmoid t ∂(ProbabilityTheory.gammaMeasure a 1)) := by
            rw [MeasureTheory.integral_sub]
            · rw [MeasureTheory.integral_sub hwf_int hf_int]
              rw [MeasureTheory.integral_sub hwt_int hconst_int]
            · exact hwf_int.sub hf_int
            · exact hwt_int.sub hconst_int
      _ = ∫ x : ℝ, K * (max x 0) ^ c * Real.sigmoid x
            ∂(ProbabilityTheory.gammaMeasure a 1) -
          ∫ x : ℝ, Real.sigmoid x ∂(ProbabilityTheory.gammaMeasure a 1) := by
            rw [MeasureTheory.integral_const_mul, hmass]
            simp
  simp only [one_div, ← Real.sigmoid_def]
  rw [htilt]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f_meas := by fun_prop)
    (hf_lt_top := by simp) Real.sigmoid]
  simp_rw [hdens_real, smul_eq_mul]
  have hdiff_nonneg := hcov_nonneg
  rw [hcov_eq] at hdiff_nonneg
  linarith

@[blueprint "lem:gamma-logistic-expectation-monotone"
  (statement := /-- For all real numbers $a$ and $b$ with $0<a\leq b$, the
  expectation of $h(x)=(1+e^{-x})^{-1}$ under the gamma distribution of shape
  $a$ and scale $1$ is at most the corresponding expectation under the gamma
  distribution of shape $b$ and scale $1$.  Equivalently, this expectation is
  non-decreasing on the open half-line of positive shape parameters. -/)
  (proof := /-- Let $a$ and $b$ be two elements of $(0,\infty)$ with $a\leq b$.
  The hypotheses give $0<a$, so
  \cref{lem:gamma-logistic-expectation-mono-of-shape-le} applies and compares
  the two logistic expectations at shapes $a$ and $b$.  This is exactly the
  defining pairwise condition for monotonicity on the set $(0,\infty)$. -/)
  (title := /-- Monotonicity of gamma-logistic expectations -/)
  (latexEnv := "lemma")]
lemma gamma_logistic_expectation_monotone :
    MonotoneOn
      (fun s : ℝ =>
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1))
      (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  exact gamma_logistic_expectation_mono_of_shape_le ha hab

@[blueprint "lem:dirichlet-eta-monotone"
  (statement := /-- The real Dirichlet eta function of
  \cref{def:dirichlet-eta-real} is non-decreasing on the open half-line
  $(1,\infty)$. -/)
  (proof := /-- Let $1<s\leq t$.  By
  \cref{lem:dirichlet-eta-gamma-expectation}, both $\eta(s)$ and $\eta(t)$
  are the expectations of $h(x)=(1+e^{-x})^{-1}$ against the gamma laws of
  shapes $s$ and $t$ and scale $1$.  Since $0<s\leq t$,
  \cref{lem:gamma-logistic-expectation-monotone} compares these two
  expectations and gives the expectation at shape $s$ at most the expectation
  at shape $t$.  Substituting the two eta-expectation identities gives
  $\eta(s)\leq\eta(t)$.  This is exactly monotonicity of
  \cref{def:dirichlet-eta-real} on $(1,\infty)$. -/)
  (title := /-- Monotonicity of eta on the half-line $s>1$ -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_monotone :
    MonotoneOn dirichlet_eta_real (Set.Ioi (1 : ℝ)) := by
  intro s hs t ht hst
  rw [dirichlet_eta_gamma_expectation s hs, dirichlet_eta_gamma_expectation t ht]
  exact gamma_logistic_expectation_monotone
    (show s ∈ Set.Ioi (0 : ℝ) from show (0 : ℝ) < s from lt_trans zero_lt_one hs)
    (show t ∈ Set.Ioi (0 : ℝ) from show (0 : ℝ) < t from lt_trans zero_lt_one ht)
    hst

@[blueprint "lem:dirichlet-eta-log-derivative-nonnegative"
  (statement := /-- For every real $s>1$, the logarithmic derivative of the
  real Dirichlet eta function is non-negative:
  $0\leq \eta'(s)/\eta(s)$. -/)
  (proof := /-- Fix $s>1$.  By \cref{lem:dirichlet-eta-monotone}, the function
  $\eta$ is non-decreasing on the open half-line $(1,\infty)$.  Since $s$ lies
  in this open half-line, the derivative within $(1,\infty)$ at $s$ is the
  ordinary derivative at $s$, and the standard non-negativity theorem for the
  derivative of a monotone function on a set gives $\eta'(s)\geq 0$.  By
  \cref{lem:dirichlet-eta-positive}, one has $\eta(s)>0$.  Dividing the
  non-negative derivative by this positive value gives
  $\eta'(s)/\eta(s)\geq 0$. -/)
  (title := /-- Non-negativity of the eta logarithmic derivative -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_log_derivative_nonnegative :
    ∀ s : ℝ, 1 < s -> 0 ≤ deriv dirichlet_eta_real s / dirichlet_eta_real s := by
  intro s hs
  refine div_nonneg ?_ (le_of_lt (dirichlet_eta_positive s hs))
  simpa [derivWithin_of_isOpen isOpen_Ioi (show s ∈ Set.Ioi (1 : ℝ) from hs)] using
    (dirichlet_eta_monotone.derivWithin_nonneg (x := s))

@[blueprint "lem:dirichlet-eta-zeta-log-derivative"
  (statement := /-- For every real number $u$ with $u>0$, the logarithmic
  derivative of the real Dirichlet eta function at $1+u$ is the real part of
  the logarithmic derivative of the Riemann zeta function at $1+u$, plus the
  eta-factor term:
  $$ {\eta'(1+u)\over\eta(1+u)}
    = \operatorname{Re}{\zeta'(1+u)\over\zeta(1+u)}
      + {\log 2\over 2^u-1}. $$ -/)
  (proof := /-- By \cref{def:dirichlet-eta-real},
  $\eta(s)$ is the real part of $(1-2^{1-s})\zeta(s)$ on the real axis.  Fix
  $u>0$ and put $s=1+u$.  The factor $1-2^{1-z}$ and the Riemann zeta function
  are differentiable and non-zero at $z=s$, so the complex logarithmic
  derivative of their product is the sum of their logarithmic derivatives.  The
  factor derivative is
  $\frac{d}{dz}(1-2^{1-z})=(\log 2)2^{1-z}$, hence at $s=1+u$ its logarithmic
  derivative is $(\log 2)/(2^u-1)$.  Since the factor and $\zeta(s)$ are real
  at this real point, taking real parts identifies the complex product
  logarithmic derivative with the real logarithmic derivative of
  \cref{def:dirichlet-eta-real}.  This gives the displayed identity. -/)
  (title := /-- Eta-zeta logarithmic derivative identity -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_zeta_log_derivative :
    ∀ u : ℝ, 0 < u ->
      deriv dirichlet_eta_real (1 + u) / dirichlet_eta_real (1 + u) =
        ((deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re +
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := by
  intro u hu
  have hfactor_deriv :
      deriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
          ((1 + u : ℝ) : ℂ) =
        (2 : ℂ) ^ (-(u : ℂ)) * Complex.log (2 : ℂ) := by
    have hinner :
        HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1 : ℂ) ((1 + u : ℝ) : ℂ) := by
      simpa using
        (hasDerivAt_const ((1 + u : ℝ) : ℂ) (1 : ℂ)).sub
          (hasDerivAt_id ((1 + u : ℝ) : ℂ))
    have hpow :
        HasDerivAt (fun z : ℂ => (2 : ℂ) ^ ((1 : ℂ) - z))
          ((2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ))) *
            Complex.log (2 : ℂ) * (-1 : ℂ)) ((1 + u : ℝ) : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hinner.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    have hfactor :
        HasDerivAt (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
          (-((2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ))) *
            Complex.log (2 : ℂ) * (-1 : ℂ))) ((1 + u : ℝ) : ℂ) := by
      simpa using (hasDerivAt_const ((1 + u : ℝ) : ℂ) (1 : ℂ)).sub hpow
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfactor.deriv
  have hfactor_log :
      (logDeriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
          ((1 + u : ℝ) : ℂ)).re =
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
    have hfactor_deriv_real :
        deriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
            ((1 + u : ℝ) : ℂ) =
          ((Real.rpow (2 : ℝ) (-u) * Real.log (2 : ℝ) : ℝ) : ℂ) := by
      simpa [Complex.ofReal_cpow, mul_comm, mul_left_comm, mul_assoc] using hfactor_deriv
    have hpow_gt_one : 1 < Real.rpow (2 : ℝ) u := by
      exact (Real.one_lt_rpow_iff (by norm_num : 0 ≤ (2 : ℝ))).2
        (Or.inl ⟨by norm_num, hu⟩)
    have hden_ne : Real.rpow (2 : ℝ) u - 1 ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hpow_gt_one)
    have hfactor_val :
        ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) =
          ((1 - Real.rpow (2 : ℝ) (-u) : ℝ) : ℂ) := by
      simp [Complex.ofReal_cpow]
    rw [logDeriv]
    change (deriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
        ((1 + u : ℝ) : ℂ) /
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ))))).re =
      Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)
    rw [hfactor_deriv_real, hfactor_val]
    rw [← Complex.ofReal_div]
    norm_cast
    rw [show Real.rpow (2 : ℝ) (-u) = (Real.rpow (2 : ℝ) u)⁻¹ by
      exact Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) u]
    field_simp [hden_ne]
  have hpow_lt : Real.rpow (2 : ℝ) (-u) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hfactor_ne :
      ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) ≠ 0 := by
    have hpow_ne : (2 : ℂ) ^ (-(u : ℂ)) ≠ 1 := by
      simpa [Complex.ofReal_cpow] using
        (show ((Real.rpow (2 : ℝ) (-u) : ℝ) : ℂ) ≠ 1 by
          exact_mod_cast hpow_lt.ne)
    simpa using sub_ne_zero.mpr (Ne.symm hpow_ne)
  have hz_ne : riemannZeta ((1 + u : ℝ) : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hf_diff :
      DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
        ((1 + u : ℝ) : ℂ) := by
    fun_prop
  have hz_diff : DifferentiableAt ℂ riemannZeta ((1 + u : ℝ) : ℂ) :=
    differentiableAt_riemannZeta (by norm_num [Complex.ext_iff]; linarith)
  have hprod_log :
      (logDeriv (fun z : ℂ =>
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
          ((1 + u : ℝ) : ℂ)).re =
        (deriv riemannZeta ((1 + u : ℝ) : ℂ) /
            riemannZeta ((1 + u : ℝ) : ℂ)).re +
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
    have h := logDeriv_mul
      (f := fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
      (g := riemannZeta) ((1 + u : ℝ) : ℂ) hfactor_ne hz_ne hf_diff hz_diff
    calc
      (logDeriv (fun z : ℂ =>
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
          ((1 + u : ℝ) : ℂ)).re
          = (logDeriv (fun z : ℂ => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z))
              ((1 + u : ℝ) : ℂ) + logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re := by
            rw [h]
      _ = Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) +
            (logDeriv riemannZeta ((1 + u : ℝ) : ℂ)).re := by
            rw [Complex.add_re]
            rw [hfactor_log]
      _ = Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) +
            (deriv riemannZeta ((1 + u : ℝ) : ℂ) /
              riemannZeta ((1 + u : ℝ) : ℂ)).re := by
            simp [logDeriv]
      _ = (deriv riemannZeta ((1 + u : ℝ) : ℂ) /
            riemannZeta ((1 + u : ℝ) : ℂ)).re +
          Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
            ring
  have hE_diff :
      DifferentiableAt ℂ (fun z : ℂ =>
        ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
        ((1 + u : ℝ) : ℂ) :=
    hf_diff.mul hz_diff
  have hderiv_eta :
      deriv dirichlet_eta_real (1 + u) =
        (deriv (fun z : ℂ =>
          ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z)
          ((1 + u : ℝ) : ℂ)).re := by
    change deriv (fun x : ℝ =>
      ((((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (x : ℂ))) *
        riemannZeta (x : ℂ)).re)) (1 + u) = _
    exact hE_diff.hasDerivAt.real_of_complex.deriv
  have hfactor_val2 :
      ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) =
        ((1 - Real.rpow (2 : ℝ) (-u) : ℝ) : ℂ) := by
    simp [Complex.ofReal_cpow]
  have hz_im : (riemannZeta ((1 + u : ℝ) : ℂ)).im = 0 := by
    simpa using riemannZeta_im_eq_zero_of_one_lt (by linarith : 1 < 1 + u)
  have hE_im :
      (((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) *
        riemannZeta ((1 + u : ℝ) : ℂ)).im = 0 := by
    rw [hfactor_val2]
    have hz_im' : (riemannZeta (1 + (u : ℂ))).im = 0 := by
      simpa [add_comm] using hz_im
    simp [hz_im']
  rw [← hprod_log]
  rw [logDeriv, hderiv_eta]
  unfold dirichlet_eta_real
  let A : ℂ := deriv (fun z : ℂ =>
    ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - z)) * riemannZeta z) ((1 + u : ℝ) : ℂ)
  let B : ℂ :=
    ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 + u : ℝ) : ℂ)))) *
      riemannZeta ((1 + u : ℝ) : ℂ)
  have hB_im : B.im = 0 := by
    simpa [B] using hE_im
  have hB_ne : B ≠ 0 := by
    dsimp [B]
    exact mul_ne_zero hfactor_ne hz_ne
  have hB_re_ne : B.re ≠ 0 := by
    intro hB_re
    apply hB_ne
    exact Complex.ext hB_re hB_im
  change A.re / B.re = (A / B).re
  rw [Complex.div_re]
  simp [hB_im]
  field_simp [Complex.normSq, hB_im, hB_re_ne]
  rw [Complex.normSq_apply, hB_im]
  ring

@[blueprint "lem:eta-log-derivative-nonnegative"
  (statement := /-- For every real number $u>0$, the sum of the real part of
  the logarithmic derivative of the Riemann zeta function at the complex point
  $1+u$ and the eta-factor term is non-negative:
  $$0\leq \operatorname{Re}\frac{\zeta'(1+u)}{\zeta(1+u)}+
  \frac{\log 2}{2^u-1}.$$ -/)
  (proof := /-- Fix $u>0$ and put $s=1+u$, so $s>1$.  By
  \cref{lem:dirichlet-eta-log-derivative-nonnegative},
  $0\leq \eta'(s)/\eta(s)$.  By
  \cref{lem:dirichlet-eta-zeta-log-derivative}, this logarithmic derivative is
  exactly
  $$\operatorname{Re}\frac{\zeta'(1+u)}{\zeta(1+u)}
    +\frac{\log 2}{2^u-1}.$$
  Substituting this identity into the preceding non-negativity inequality gives
  the asserted bound. -/)
  (title := /-- Eta logarithmic-derivative nonnegativity -/)
  (latexEnv := "lemma")]
lemma eta_log_derivative_nonnegative :
    ∀ u : ℝ, 0 < u ->
      0 ≤ ((deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re +
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1)) := by
  intro u hu
  rw [← dirichlet_eta_zeta_log_derivative u hu]
  exact dirichlet_eta_log_derivative_nonnegative (1 + u) (by linarith)

@[blueprint "lem:zeta-log-derivative-geometric-bound"
  (statement := /-- For every real number $u>0$, the real part of the negative
  logarithmic derivative of the Riemann zeta function at the complex point
  $1+u$ satisfies
  $$\operatorname{Re}\left(-\frac{\zeta'(1+u)}{\zeta(1+u)}\right)
  \leq \frac{\log 2}{2^u-1}.$$ -/)
  (proof := /-- Fix $u>0$.  By
  \cref{lem:eta-log-derivative-nonnegative},
  $$0\leq \operatorname{Re}\frac{\zeta'(1+u)}{\zeta(1+u)}+
  \frac{\log 2}{2^u-1}.$$
  Since real part is additive and commutes with negation, this inequality is
  equivalent to
  $$\operatorname{Re}\left(-\frac{\zeta'(1+u)}{\zeta(1+u)}\right)
  \leq \frac{\log 2}{2^u-1},$$
  which is the desired comparison. -/)
  (title := /-- Zeta logarithmic-derivative comparison -/)
  (latexEnv := "lemma")]
lemma zeta_log_derivative_geometric_bound :
    ∀ u : ℝ, 0 < u ->
      ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) ≤
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
  intro u hu
  simpa [neg_div] using
    (show - ((deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) ≤
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) from by
      have h := eta_log_derivative_nonnegative u hu
      linarith)

@[blueprint "lem:mangoldt-dirichlet-series-eq-zeta-log-derivative"
  (statement := /-- For every real number $u$ with $u>0$, the complex number
  obtained from the real von Mangoldt Dirichlet series equals the negative
  logarithmic derivative of the Riemann zeta function at $1+u$:
  $$
    \sum_{q\in\mathbb{N}} \Lambda(q)q^{-1-u}
      =-\frac{\zeta'(1+u)}{\zeta(1+u)}.
  $$ -/)
  (proof := /-- Fix $u>0$ and put $s=1+u$, so that $\operatorname{Re}s>1$.
  The Mathlib von Mangoldt L-series identity identifies the complex L-series
  with $-\zeta'(s)/\zeta(s)$.  It remains only to expand
  \cref{def:mangoldt-dirichlet-series}: after coercing the real infinite sum
  to $\mathbb{C}$, each term is the corresponding L-series term, because for
  every natural number $q$ the complex power of the non-negative real $q$ agrees
  with the real power coerced to $\mathbb{C}$. -/)
  (title := /-- Von Mangoldt series as a zeta logarithmic derivative -/)
  (latexEnv := "lemma")]
lemma mangoldt_dirichlet_series_eq_zeta_log_derivative :
    ∀ u : ℝ, 0 < u ->
      (mangoldt_dirichlet_series u : ℂ) =
        - deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ) := by
  intro u hu
  have hs : 1 < (((1 + u : ℝ) : ℂ).re) := by
    simp
    linarith
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := ((1 + u : ℝ) : ℂ)) hs]
  change (mangoldt_dirichlet_series u : ℂ) =
    LSeries (fun q : ℕ => (ArithmeticFunction.vonMangoldt q : ℂ)) ((1 + u : ℝ) : ℂ)
  rw [mangoldt_dirichlet_series, LSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro q
  by_cases hq : q = 0
  · subst q
    simp [Real.zero_rpow (by linarith : (1 : ℝ) + u ≠ 0)]
  · rw [LSeries.term_of_ne_zero hq]
    rw [Complex.ofReal_div]
    congr 1
    exact Complex.ofReal_cpow (Nat.cast_nonneg q) (1 + u)

@[blueprint "lem:zeta-geometric-bound-le-inv"
  (statement := /-- For every real number $u$ with $u>0$, the elementary
  geometric factor satisfies
  $$
    \frac{\log 2}{2^u-1}\leq \frac{1}{u}.
  $$ -/)
  (proof := /-- Fix $u>0$.  The denominator $2^u-1$ is positive.  Applying
  the inequality $x+1\leq e^x$ to $x=(\log 2)u$ and rewriting
  $e^{(\log 2)u}$ as $2^u$ gives $(\log 2)u\leq 2^u-1$.  Since both $u$ and
  $2^u-1$ are positive, cross-multiplication gives the displayed inequality. -/)
  (title := /-- Geometric factor bounded by $1/u$ -/)
  (latexEnv := "lemma")]
lemma zeta_geometric_bound_le_inv :
    ∀ u : ℝ, 0 < u ->
      Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) ≤ 1 / u := by
  intro u hu
  have hpow_gt_one : 1 < Real.rpow (2 : ℝ) u := by
    exact (Real.one_lt_rpow_iff (by norm_num : 0 ≤ (2 : ℝ))).2
      (Or.inl ⟨by norm_num, hu⟩)
  have hden_pos : 0 < Real.rpow (2 : ℝ) u - 1 := by
    linarith
  have hmul : Real.log (2 : ℝ) * u ≤ Real.rpow (2 : ℝ) u - 1 := by
    have h := Real.add_one_le_exp (Real.log (2 : ℝ) * u)
    have h' : Real.log (2 : ℝ) * u + 1 ≤ Real.rpow (2 : ℝ) u := by
      simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) u] using h
    linarith
  rw [div_le_div_iff₀ hden_pos hu]
  simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul

@[blueprint "lem:von-mangoldt-dirichlet-series-upper-bound"
  (statement := /-- For every real number $u$ with $u>0$, the von Mangoldt
  Dirichlet series
  $\sum_{q\in\mathbb{N}} \Lambda(q)q^{-1-u}$ is at most $1/u$. -/)
  (proof := /-- Fix a real number $u>0$.  By
  \cref{lem:mangoldt-dirichlet-series-eq-zeta-log-derivative}, the real
  Dirichlet series is the real part of
  $-\zeta'(1+u)/\zeta(1+u)$.  The comparison
  \cref{lem:zeta-log-derivative-geometric-bound} bounds this real part by
  $\log 2/(2^u-1)$, and
  \cref{lem:zeta-geometric-bound-le-inv} bounds the latter quantity by $1/u$.
  Chaining these two inequalities gives the result. -/)
  (title := /-- Dirichlet-series upper bound -/)
  (latexEnv := "lemma")]
lemma von_mangoldt_dirichlet_series_upper_bound :
    ∀ u : ℝ, 0 < u -> mangoldt_dirichlet_series u ≤ 1 / u := by
  intro u hu
  have hseries :
      mangoldt_dirichlet_series u =
        ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := by
    simpa using congrArg Complex.re
      (mangoldt_dirichlet_series_eq_zeta_log_derivative u hu)
  calc
    mangoldt_dirichlet_series u
        = ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) := hseries
    _ ≤ Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) :=
      zeta_log_derivative_geometric_bound u hu
    _ ≤ 1 / u := zeta_geometric_bound_le_inv u hu

@[blueprint "lem:mangoldt-tail-range-eq-ico"
  (statement := /-- For every natural cutoff $N$, natural parameter $m$, and
  real threshold $y$, the thresholded range sum of the von Mangoldt tail
  summand is the same as the contiguous sum over
  $\lceil y\rceil\leq q<N$. -/)
  (proof := /-- Rewrite the thresholded range sum as a filtered range sum and
  use the defining universal property of the natural ceiling to identify the
  filter with the interval $[\lceil y\rceil,N)$. -/)
  (title := /-- Thresholded range sums as interval sums -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_range_eq_ico (m N : ℕ) (y : ℝ) :
    (∑ q ∈ Finset.range N,
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) =
      ∑ q ∈ Finset.Ico ⌈y⌉₊ N, mangoldt_tail_term m q := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext q
    simp [Nat.ceil_le, and_comm]
  · intro q hq
    rfl

@[blueprint "lem:mangoldt-reciprocal-partial-sum-nat"
  (statement := /-- At a natural cutoff $n$, the real-variable reciprocal von
  Mangoldt partial sum is exactly the finite sum
  $\sum_{1\leq q\leq n}\Lambda(q)/q$. -/)
  (proof := /-- Expand \cref{def:mangoldt-reciprocal-partial-sum}. The
  unconditional sum has support contained in the finite interval
  $1\leq q\leq n$, and on that interval the indicator condition is true. -/)
  (title := /-- Natural cutoffs for reciprocal Mangoldt sums -/)
  (latexEnv := "lemma")]
lemma mangoldt_reciprocal_partial_sum_nat (n : ℕ) :
    mangoldt_reciprocal_partial_sum (n : ℝ) =
      ∑ q ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
  rw [mangoldt_reciprocal_partial_sum]
  calc
    (∑' q : ℕ,
        if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
          ArithmeticFunction.vonMangoldt q / (q : ℝ)
        else 0) =
        ∑ q ∈ Finset.Icc 1 n,
          if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / (q : ℝ)
          else 0 := by
      refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
        (s := Finset.Icc 1 n)
        (f := fun q : ℕ =>
          if 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ) then
            ArithmeticFunction.vonMangoldt q / (q : ℝ)
          else 0) ?_
      intro q hq
      by_cases hcond : 1 ≤ q ∧ (q : ℝ) ≤ (n : ℝ)
      · exfalso
        exact hq (Finset.mem_Icc.mpr ⟨hcond.1, Nat.cast_le.mp hcond.2⟩)
      · exact if_neg hcond
    _ = ∑ q ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      rcases Finset.mem_Icc.mp hq with ⟨hq1, hqn⟩
      have hqr : (q : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hqn
      simp [hq1, hqr]

@[blueprint "lem:real-sub-div-square-le-inv-sub-inv"
  (statement := /-- If $0<a\leq b$, then
  $(b-a)/b^2\leq 1/a-1/b$. -/)
  (proof := /-- Clear the positive denominators $a$ and $b$; the resulting
  polynomial inequality is immediate from $a\leq b$. -/)
  (title := /-- A reciprocal-difference algebra inequality -/)
  (latexEnv := "lemma")]
lemma real_sub_div_square_le_inv_sub_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ^ 2 ≤ 1 / a - 1 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  field_simp [ha.ne', hb.ne']
  nlinarith

@[blueprint "lem:mangoldt-log-increment-pointwise-le"
  (statement := /-- If $m\geq 1$ and $r\geq 2$, then the weighted logarithmic
  increment from $r$ to $r+1$ is bounded by the corresponding telescoping
  reciprocal-log difference. -/)
  (proof := /-- Use \cref{lem:real-sub-div-square-le-inv-sub-inv} with
  $a=\log(mr)$ and $b=\log(m(r+1))$.  Positivity and monotonicity of the
  logarithm apply because $mr\geq 2$ and $m(r+1)\geq mr$. -/)
  (title := /-- Pointwise logarithmic-increment comparison -/)
  (latexEnv := "lemma")]
lemma mangoldt_log_increment_pointwise_le (m r : ℕ) (hm : 1 ≤ m) (hr : 2 ≤ r) :
    (Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)) /
        (Real.log (((m * (r + 1) : ℕ) : ℝ))) ^ 2 ≤
      1 / Real.log (((m * r : ℕ) : ℝ)) -
        1 / Real.log (((m * (r + 1) : ℕ) : ℝ)) := by
  have hmr_two : 2 ≤ m * r := by
    exact Nat.mul_le_mul hm hr
  have hmr_pos_log : 0 < Real.log (((m * r : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hmr_two)
  have hmr_le : (m * r : ℕ) ≤ m * (r + 1) := by
    exact Nat.mul_le_mul_left m (Nat.le_succ r)
  have hlog_le : Real.log (((m * r : ℕ) : ℝ)) ≤
      Real.log (((m * (r + 1) : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hmr_two)
    · exact_mod_cast hmr_le
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hr)
  have hr_succ_pos : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hlogdiff :
      Real.log (((m * (r + 1) : ℕ) : ℝ)) - Real.log (((m * r : ℕ) : ℝ)) =
        Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [Real.log_mul hm_pos.ne' hr_succ_pos.ne', Real.log_mul hm_pos.ne' hr_pos.ne']
    ring
  have hcore := real_sub_div_square_le_inv_sub_inv hmr_pos_log hlog_le
  rw [hlogdiff] at hcore
  simpa [Nat.cast_mul] using hcore

@[blueprint "lem:log-increment-sum-ico-two"
  (statement := /-- For every natural $r\geq 1$, the logarithmic increments
  from $2$ through $r$ telescope:
  $\sum_{2\leq q<r+1}(\log q-\log(q-1))=\log r$. -/)
  (proof := /-- Reindex by $q=i+1$ and apply the standard telescoping identity
  for $\sum_{1\leq i<r}(\log(i+1)-\log i)$, using $\log 1=0$. -/)
  (title := /-- Telescoping logarithmic increments -/)
  (latexEnv := "lemma")]
lemma log_increment_sum_ico_two (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Ico 2 (r + 1),
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) = Real.log (r : ℝ) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl]
  rw [← Finset.sum_Ico_add
    (f := fun q : ℕ => Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
    (a := 1) (b := r) (c := 1)]
  have hsum := Finset.sum_Ico_sub (m := 1) (n := r)
    (f := fun i : ℕ => Real.log (i : ℝ)) hr
  simpa [Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel, Real.log_one] using hsum

@[blueprint "lem:mangoldt-reciprocal-sum-ico-two"
  (statement := /-- For every natural $r\geq 1$, the sum of
  $\Lambda(q)/q$ over $2\leq q<r+1$ is the reciprocal von Mangoldt partial sum
  at the natural cutoff $r$. -/)
  (proof := /-- Use \cref{lem:mangoldt-reciprocal-partial-sum-nat}.  The
  interval $2\leq q<r+1$ is $1<q\leq r$, and the omitted $q=1$ term is zero
  because $\Lambda(1)=0$. -/)
  (title := /-- Reciprocal Mangoldt sums from two -/)
  (latexEnv := "lemma")]
lemma mangoldt_reciprocal_sum_ico_two (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Ico 2 (r + 1), ArithmeticFunction.vonMangoldt q / (q : ℝ)) =
      mangoldt_reciprocal_partial_sum (r : ℝ) := by
  rw [mangoldt_reciprocal_partial_sum_nat]
  have hI : Finset.Ico 2 (r + 1) = Finset.Ioc 1 r := by
    simpa [Nat.succ_eq_add_one] using (Finset.Ico_succ_succ_eq_Ioc (1 : ℕ) r)
  rw [hI]
  rw [Finset.Icc_eq_cons_Ioc hr]
  simp

@[blueprint "lem:mangoldt-mertens-error-partial-bound"
  (statement := /-- Assume the reciprocal von Mangoldt Mertens error is bounded
  by $D$.  Then for every interval $n\leq q<k$ with $n\geq 2$, the partial sum
  of
  $\Lambda(q)/q-(\log q-\log(q-1))$ has absolute value at most $2D$. -/)
  (proof := /-- The interval sum is the difference of the two endpoint errors
  $\sum_{q\leq r}\Lambda(q)/q-\log r$ at $r=k-1$ and $r=n-1$.  Use
  \cref{lem:mangoldt-reciprocal-sum-ico-two} and
  \cref{lem:log-increment-sum-ico-two} to identify these endpoint errors with
  the real-variable reciprocal partial sums minus $\log r$, then apply the
  assumed Mertens bound and the triangle inequality. -/)
  (title := /-- Bounded partial sums of the Mertens error -/)
  (latexEnv := "lemma")]
lemma mangoldt_mertens_error_partial_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D)
    (n k : ℕ) (hn : 2 ≤ n) :
    |∑ q ∈ Finset.Ico n k,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))| ≤ 2 * D := by
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  have hendpoint : ∀ r : ℕ, 1 ≤ r -> |∑ q ∈ Finset.Ico 2 (r + 1), e q| ≤ D := by
    intro r hr
    have hrec := mangoldt_reciprocal_sum_ico_two r hr
    have hlog := log_increment_sum_ico_two r hr
    have hsum : (∑ q ∈ Finset.Ico 2 (r + 1), e q) =
        mangoldt_reciprocal_partial_sum (r : ℝ) - Real.log (r : ℝ) := by
      dsimp [e]
      rw [Finset.sum_sub_distrib]
      rw [hrec, hlog]
    rw [hsum]
    exact hD (r : ℝ) (by exact_mod_cast hr)
  by_cases hkn : k ≤ n
  · rw [Finset.Ico_eq_empty_of_le hkn]
    simp
    nlinarith
  · have hnk : n < k := not_le.mp hkn
    have hk_pred_one : 1 ≤ k - 1 := by omega
    have hn_pred_one : 1 ≤ n - 1 := by omega
    have hk_sum := hendpoint (k - 1) hk_pred_one
    have hn_sum := hendpoint (n - 1) hn_pred_one
    have hk_sum' : |∑ q ∈ Finset.Ico 2 k, e q| ≤ D := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hk_sum
    have hn_sum' : |∑ q ∈ Finset.Ico 2 n, e q| ≤ D := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hn_sum
    have hconsec := Finset.sum_Ico_consecutive (f := e) (m := 2) (n := n) (k := k) hn hnk.le
    have hinterval : (∑ q ∈ Finset.Ico n k, e q) =
        (∑ q ∈ Finset.Ico 2 k, e q) - (∑ q ∈ Finset.Ico 2 n, e q) := by
      linarith
    rw [show (∑ q ∈ Finset.Ico n k,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)))) =
        ∑ q ∈ Finset.Ico n k, e q by rfl]
    rw [hinterval]
    calc
      |(∑ q ∈ Finset.Ico 2 k, e q) - (∑ q ∈ Finset.Ico 2 n, e q)| ≤
          |∑ q ∈ Finset.Ico 2 k, e q| + |∑ q ∈ Finset.Ico 2 n, e q| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (∑ q ∈ Finset.Ico 2 k, e q) (-(∑ q ∈ Finset.Ico 2 n, e q))
      _ ≤ D + D := by linarith
      _ = 2 * D := by ring

@[blueprint "lem:mangoldt-mertens-error-weighted-bound"
  (statement := /-- Assume the reciprocal von Mangoldt Mertens error is bounded
  by $D$.  Then, for every $m\geq 1$, $y\geq 2$, and cutoff $N$, the weighted
  interval sum of the Mertens error over $\lceil y\rceil\leq q<N$ is at most
  $4D/\log^2(my)$. -/)
  (proof := /-- Apply summation by parts to the error sequence with weight
  $\log^{-2}(mq)$.  The partial sums are bounded by
  \cref{lem:mangoldt-mertens-error-partial-bound}; the weight is nonnegative
  and decreasing on the interval because $mq\geq my\geq 2$.  The resulting
  endpoint and variation terms are each bounded by $2D/\log^2(my)$. -/)
  (title := /-- Weighted Mertens-error bound -/)
  (latexEnv := "lemma")]
lemma mangoldt_mertens_error_weighted_bound (D : ℝ) (hD_nonneg : 0 ≤ D)
    (hD : ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ D)
    (m N : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y) :
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
      (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
      4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
  let n : ℕ := ⌈y⌉₊
  let e : ℕ → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q / (q : ℝ) -
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
  let w : ℕ → ℝ := fun q => 1 / (Real.log (((m * q : ℕ) : ℝ))) ^ 2
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  have hyn : y ≤ (n : ℝ) := by
    simpa [n] using Nat.le_ceil y
  have hn : 2 ≤ n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  rw [show ⌈y⌉₊ = n by rfl]
  by_cases hN : n < N
  · let g : ℕ → ℝ := fun q => if n ≤ q then e q else 0
    have hG_eq : ∀ k : ℕ, (∑ q ∈ Finset.range k, g q) = ∑ q ∈ Finset.Ico n k, e q := by
      intro k
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext q
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
      · intro q hq
        simp [g, (Finset.mem_Ico.mp hq).1]
    have hG_bound : ∀ k : ℕ, |∑ q ∈ Finset.range k, g q| ≤ 2 * D := by
      intro k
      rw [hG_eq k]
      exact mangoldt_mertens_error_partial_bound D hD_nonneg hD n k hn
    have htarget :
        (∑ q ∈ Finset.Ico n N,
          (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
            (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
              (Real.log (((m * q : ℕ) : ℝ))) ^ 2) =
          ∑ q ∈ Finset.range N, w q * g q := by
      symm
      dsimp [g]
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext q
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
      · intro q hq
        dsimp [w, e]
        ring
    rw [htarget]
    have hbp := Finset.sum_range_by_parts (f := w) (g := g) (n := N)
    have hbp' : ∑ i ∈ Finset.range N, w i * g i =
        w (N - 1) * (∑ i ∈ Finset.range N, g i) -
          ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) := by
      simpa only [smul_eq_mul] using hbp
    rw [hbp']
    have hLsq_pos : 0 < (Real.log ((m : ℝ) * y)) ^ 2 := sq_pos_of_pos hLpos
    have htwoD_nonneg : 0 ≤ 2 * D := by positivity
    have hfourD_nonneg : 0 ≤ 4 * D := by positivity
    have hN_pred_ge : n ≤ N - 1 := Nat.le_pred_of_lt hN
    have hN_pred_two : 2 ≤ N - 1 := hn.trans hN_pred_ge
    have hw_le_L : ∀ q : ℕ, n ≤ q -> w q ≤ 1 / (Real.log ((m : ℝ) * y)) ^ 2 := by
      intro q hnq
      have hq_real : y ≤ (q : ℝ) := hyn.trans (by exact_mod_cast hnq)
      have harg : (m : ℝ) * y ≤ (((m * q : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hq_real (by positivity)
      have hlog : Real.log ((m : ℝ) * y) ≤ Real.log (((m * q : ℕ) : ℝ)) :=
        Real.log_le_log (by linarith) harg
      dsimp [w]
      gcongr
    have hw_nonneg : ∀ q : ℕ, n ≤ q -> 0 ≤ w q := by
      intro q hnq
      dsimp [w]
      positivity
    have hboundary : w (N - 1) * (∑ i ∈ Finset.range N, g i) ≤
        2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      have hG_le : (∑ i ∈ Finset.range N, g i) ≤ 2 * D :=
        (le_abs_self _).trans (hG_bound N)
      have hwN_nonneg : 0 ≤ w (N - 1) := hw_nonneg (N - 1) hN_pred_ge
      have hwN_le := hw_le_L (N - 1) hN_pred_ge
      calc
        w (N - 1) * (∑ i ∈ Finset.range N, g i) ≤ w (N - 1) * (2 * D) := by
          exact mul_le_mul_of_nonneg_left hG_le hwN_nonneg
        _ ≤ (1 / (Real.log ((m : ℝ) * y)) ^ 2) * (2 * D) := by
          exact mul_le_mul_of_nonneg_right hwN_le htwoD_nonneg
        _ = 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
    have hvar_point : ∀ i ∈ Finset.range (N - 1),
        -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) ≤
          2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by
      intro i hi
      by_cases hni : n ≤ i
      · have hi_tail : n ≤ i + 1 := hni.trans (Nat.le_succ i)
        have hG_le : (∑ j ∈ Finset.range (i + 1), g j) ≤ 2 * D :=
          (le_abs_self _).trans (hG_bound (i + 1))
        have hw_mono : w (i + 1) ≤ w i := by
          have harg : (((m * i : ℕ) : ℝ)) ≤ (((m * (i + 1) : ℕ) : ℝ)) := by
            exact_mod_cast Nat.mul_le_mul_left m (Nat.le_succ i)
          have hi_two : 2 ≤ i := hn.trans hni
          have hlog_pos_i : 0 < Real.log (((m * i : ℕ) : ℝ)) := by
            have htwo : 2 ≤ m * i := Nat.mul_le_mul hm hi_two
            apply Real.log_pos
            exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo)
          have hlog_le : Real.log (((m * i : ℕ) : ℝ)) ≤
              Real.log (((m * (i + 1) : ℕ) : ℝ)) :=
            Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (Nat.mul_le_mul hm hi_two))) harg
          dsimp [w]
          gcongr
        have hdiff_nonneg : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr hw_mono
        calc
          -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) =
              (w i - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), g j) := by ring
          _ ≤ (w i - w (i + 1)) * (2 * D) := by
            exact mul_le_mul_of_nonneg_left hG_le hdiff_nonneg
          _ = 2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by simp [hni, mul_comm, mul_left_comm, mul_assoc]
      · have hG_zero : (∑ j ∈ Finset.range (i + 1), g j) = 0 := by
          rw [hG_eq (i + 1)]
          rw [Finset.Ico_eq_empty_of_le]
          · simp
          · omega
        simp [hni, hG_zero]
    have hvariation :
        -∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) ≤
          2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      calc
        -∑ i ∈ Finset.range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) =
            ∑ i ∈ Finset.range (N - 1),
              -((w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j)) := by
          rw [Finset.sum_neg_distrib]
        _ ≤ ∑ i ∈ Finset.range (N - 1),
              2 * D * (if n ≤ i then w i - w (i + 1) else 0) := by
          exact Finset.sum_le_sum hvar_point
        _ = 2 * D * (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext i
            simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
          · intro i hi
            simp [(Finset.mem_Ico.mp hi).1]
        _ = 2 * D * (w n - w (N - 1)) := by
          have hsum := Finset.sum_Ico_sub (m := n) (n := N - 1) (f := w) hN_pred_ge
          have hsum' : (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) = w n - w (N - 1) := by
            calc
              (∑ i ∈ Finset.Ico n (N - 1), (w i - w (i + 1))) =
                  - (∑ i ∈ Finset.Ico n (N - 1), (w (i + 1) - w i)) := by
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              _ = -(w (N - 1) - w n) := by rw [hsum]
              _ = w n - w (N - 1) := by ring
          rw [hsum']
        _ ≤ 2 * D * w n := by
          have hwN_nonneg : 0 ≤ w (N - 1) := hw_nonneg (N - 1) hN_pred_ge
          nlinarith [htwoD_nonneg]
        _ ≤ 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
          have hwn_le := hw_le_L n le_rfl
          calc
            2 * D * w n ≤ 2 * D * (1 / (Real.log ((m : ℝ) * y)) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hwn_le htwoD_nonneg
            _ = 2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
    calc
      w (N - 1) * (∑ i ∈ Finset.range N, g i) -
          ∑ i ∈ Finset.range (N - 1),
            (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), g j) ≤
          2 * D / (Real.log ((m : ℝ) * y)) ^ 2 +
            2 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
        linarith
      _ = 4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by ring
  · rw [Finset.Ico_eq_empty_of_le (not_lt.mp hN)]
    simp
    positivity

@[blueprint "lem:mangoldt-log-increment-weighted-bound"
  (statement := /-- Let $m\geq 1$, $y\geq 2$, and $N$ be natural.  With
  $n=\lceil y\rceil$, the weighted logarithmic-increment sum over
  $n\leq q<N$ is bounded by
  $1/\log(my)+\log(2)/\log^2(my)$. -/)
  (proof := /-- The first increment is at most $\log 2$ times the initial
  weight.  For later increments, apply
  \cref{lem:mangoldt-log-increment-pointwise-le} to compare
  $(\log q-\log(q-1))/\log^2(mq)$ with the telescoping difference
  $1/\log(m(q-1))-1/\log(mq)$.  Since $\lceil y\rceil\geq y$, the endpoint
  discrepancy is absorbed by the displayed $\log 2$ error term. -/)
  (title := /-- Weighted logarithmic increments -/)
  (latexEnv := "lemma")]
lemma mangoldt_log_increment_weighted_bound (m N : ℕ) (hm : 1 ≤ m) (y : ℝ)
    (hy : 2 ≤ y) :
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
      (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
        (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
      1 / Real.log ((m : ℝ) * y) +
        Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
  let n : ℕ := ⌈y⌉₊
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  have hyn : y ≤ (n : ℝ) := by
    simpa [n] using Nat.le_ceil y
  have hn : 2 ≤ n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  by_cases hN : n < N
  · rw [show ⌈y⌉₊ = n by rfl]
    rw [← Finset.add_sum_Ioo_eq_sum_Ico
      (f := fun q : ℕ =>
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) hN]
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hnum : Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log 2 := by
      have hnpos : 0 < n := by omega
      have hn1pos : 0 < n - 1 := by omega
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hnpos)
      have hn1_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hn1pos)
      rw [← Real.log_div hn_ne hn1_ne]
      apply Real.log_le_log
      · positivity
      · field_simp [hn1_ne]
        rw [Nat.cast_sub (by omega : 1 ≤ n)] at *
        norm_num at *
        nlinarith
    have hlog_mn : Real.log ((m : ℝ) * y) ≤ Real.log (((m * n : ℕ) : ℝ)) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      have harg : (m : ℝ) * y ≤ (((m * n : ℕ) : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hyn hm_nonneg
      exact Real.log_le_log (by linarith) harg
    have hlog_mn_pos : 0 < Real.log (((m * n : ℕ) : ℝ)) := hLpos.trans_le hlog_mn
    have hfirst :
        (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
            (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
          Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
      have hstep₁ :
          (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) /
              (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
            Real.log 2 / (Real.log (((m * n : ℕ) : ℝ))) ^ 2 := by
        gcongr
      have hstep₂ :
          Real.log 2 / (Real.log (((m * n : ℕ) : ℝ))) ^ 2 ≤
            Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2 := by
        gcongr
      exact hstep₁.trans hstep₂
    let F : ℕ → ℝ := fun r => 1 / Real.log (((m * r : ℕ) : ℝ))
    have htel :
        (∑ x ∈ Finset.Ioo n N, (F (x - 1) - F x)) = F n - F (N - 1) := by
      rw [← Finset.Ico_succ_left_eq_Ioo]
      rw [show Order.succ n = n + 1 by rfl]
      rw [show N = N - 1 + 1 by omega]
      rw [← Finset.sum_Ico_add
        (f := fun x : ℕ => F (x - 1) - F x) (a := n) (b := N - 1) (c := 1)]
      have hsum := Finset.sum_Ico_sub (m := n) (n := N - 1) (f := F)
        (Nat.le_pred_of_lt hN)
      have hsum' :
          (∑ i ∈ Finset.Ico n (N - 1), (F i - F (i + 1))) = F n - F (N - 1) := by
        calc
          (∑ i ∈ Finset.Ico n (N - 1), (F i - F (i + 1))) =
              - (∑ i ∈ Finset.Ico n (N - 1), (F (i + 1) - F i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = -(F (N - 1) - F n) := by rw [hsum]
          _ = F n - F (N - 1) := by ring
      simpa [Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel] using hsum'
    have htail_point : ∀ x ∈ Finset.Ioo n N,
        (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2 ≤ F (x - 1) - F x := by
      intro x hx
      have hx_left : n < x := (Finset.mem_Ioo.mp hx).1
      have hx_pred_ge : 2 ≤ x - 1 := by omega
      have hx_one_le : 1 ≤ x := by omega
      have h := mangoldt_log_increment_pointwise_le m (x - 1) hm hx_pred_ge
      dsimp [F]
      simpa [Nat.sub_add_cancel hx_one_le] using h
    have htail_le :
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤ F n - F (N - 1) := by
      calc
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤
            ∑ x ∈ Finset.Ioo n N, (F (x - 1) - F x) := by
          exact Finset.sum_le_sum htail_point
        _ = F n - F (N - 1) := htel
    have hN_pred_ge : n ≤ N - 1 := Nat.le_pred_of_lt hN
    have hN_pred_two : 2 ≤ N - 1 := hn.trans hN_pred_ge
    have hlog_N_pred_pos : 0 < Real.log (((m * (N - 1) : ℕ) : ℝ)) := by
      have htwo : 2 ≤ m * (N - 1) := Nat.mul_le_mul hm hN_pred_two
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two htwo)
    have hF_N_nonneg : 0 ≤ F (N - 1) := by
      dsimp [F]
      positivity
    have htail :
        (∑ x ∈ Finset.Ioo n N,
          (Real.log (x : ℝ) - Real.log ((x - 1 : ℕ) : ℝ)) /
            (Real.log (((m * x : ℕ) : ℝ))) ^ 2) ≤
          1 / Real.log ((m : ℝ) * y) := by
      have hFn : F n ≤ 1 / Real.log ((m : ℝ) * y) := by
        dsimp [F]
        gcongr
      linarith
    linarith
  · rw [show ⌈y⌉₊ = n by rfl]
    rw [Finset.Ico_eq_empty_of_le (not_lt.mp hN)]
    simp
    positivity

@[blueprint "lem:mangoldt-tail-range-sum-bound"
  (statement := /-- There is a real constant $C\geq 0$ such that, for every
  natural $m\geq 1$, every real $y\geq 2$, and every natural cutoff $N$, the
  finite thresholded range sum of the von Mangoldt tail summand up to $N$ is at
  most $1/\log(my)+C/\log^2(my)$. -/)
  (proof := /-- Rewrite the thresholded range sum using
  \cref{lem:mangoldt-tail-range-eq-ico}.  Decompose $\Lambda(q)/q$ into the
  logarithmic increment $\log q-\log(q-1)$ plus the reciprocal-Mertens error.
  The logarithmic-increment contribution is bounded by
  \cref{lem:mangoldt-log-increment-weighted-bound}.  Choose the Mertens
  constant from \cref{lem:mertens-von-mangoldt-reciprocal} and apply
  \cref{lem:mangoldt-mertens-error-weighted-bound} to the error contribution.
  Adding the two estimates gives the stated finite range bound after taking the
  constant $\log 2+4D$. -/)
  (title := /-- Finite range form of the Mangoldt tail bound -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_range_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y -> ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
        1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  obtain ⟨D, hD_nonneg, hD⟩ := mertens_von_mangoldt_reciprocal
  refine ⟨Real.log 2 + 4 * D, by positivity, ?_⟩
  intro m hm y hy N
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hy_nonneg : 0 ≤ y := by linarith
  have hmy_two : (2 : ℝ) ≤ (m : ℝ) * y := by
    calc
      (2 : ℝ) ≤ 1 * y := by simpa using hy
      _ ≤ (m : ℝ) * y := by
        exact mul_le_mul_of_nonneg_right hm_real hy_nonneg
  have hLpos : 0 < Real.log ((m : ℝ) * y) := by
    exact Real.log_pos (by linarith)
  rw [mangoldt_tail_range_eq_ico]
  let n : ℕ := ⌈y⌉₊
  have hn : 2 ≤ n := by
    have hyn : y ≤ (n : ℝ) := by
      simpa [n] using Nat.le_ceil y
    have h2n : (2 : ℝ) ≤ (n : ℝ) := hy.trans hyn
    exact_mod_cast h2n
  have hsplit :
      (∑ q ∈ Finset.Ico ⌈y⌉₊ N, mangoldt_tail_term m q) =
        (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
            (Real.log (((m * q : ℕ) : ℝ))) ^ 2) +
        (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
          (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
            (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
              (Real.log (((m * q : ℕ) : ℝ))) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [mangoldt_tail_term]
    ring
  have hmain := mangoldt_log_increment_weighted_bound m N hm y hy
  have herror := mangoldt_mertens_error_weighted_bound D hD_nonneg hD m N hm y hy
  rw [hsplit]
  calc
    (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
        (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) /
          (Real.log (((m * q : ℕ) : ℝ))) ^ 2) +
      (∑ q ∈ Finset.Ico ⌈y⌉₊ N,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ) -
          (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))) /
            (Real.log (((m * q : ℕ) : ℝ))) ^ 2) ≤
        (1 / Real.log ((m : ℝ) * y) +
          Real.log 2 / (Real.log ((m : ℝ) * y)) ^ 2) +
          4 * D / (Real.log ((m : ℝ) * y)) ^ 2 := by
      exact add_le_add hmain herror
    _ = 1 / Real.log ((m : ℝ) * y) +
        (Real.log 2 + 4 * D) / (Real.log ((m : ℝ) * y)) ^ 2 := by
      ring

@[blueprint "lem:mangoldt-tail-upper-bound"
  (statement := /-- There is a real constant $C\geq 0$, independent of $m$ and
  $y$, such that, for every natural $m\geq 1$ and every real $y\geq 2$, the von
  Mangoldt tail series is summable and
  $\sum_{q\geq y}\Lambda(q)/(q\log^2(mq))\leq
  1/\log(my)+C/\log^2(my)$. -/)
  (proof := /-- Choose the constant supplied by
  \cref{lem:mangoldt-tail-range-sum-bound}.  For fixed $m\geq 1$ and
  $y\geq 2$, the tail summands are non-negative, so the uniform finite-range
  bound implies summability of the corresponding series.  The standard
  comparison of a non-negative real series with its bounded partial sums then
  gives the same bound for the t-sum defining the von Mangoldt tail. -/)
  (title := /-- Upper von Mangoldt tail estimate -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_upper_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y ->
      Summable (fun q : ℕ => if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ∧
        mangoldt_tail_sum m y ≤
          1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := mangoldt_tail_range_sum_bound
  refine ⟨C, hC, ?_⟩
  intro m hm y hy
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  have hsumm : Summable (fun q : ℕ =>
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) :=
    summable_of_sum_range_le hnonneg (hbound m hm y hy)
  refine ⟨hsumm, ?_⟩
  simpa [mangoldt_tail_sum] using
    hsumm.tsum_le_of_sum_range_le (hbound m hm y hy)

@[blueprint "lem:mangoldt-tail-finite-sum-le"
  (statement := /-- Let $m$ be a natural number with $m\geq 1$, let $y$ be a
  real number with $y\geq 2$, and let $S$ be a finite set of natural numbers.
  Then
  $\sum_{q\in S}1_{y\leq q}\Lambda(q)/(q\log^2(mq))\leq
  \sum_{q\geq y}\Lambda(q)/(q\log^2(mq))$. -/)
  (proof := /-- By \cref{lem:mangoldt-tail-upper-bound}, the series defining
  \cref{def:mangoldt-tail-sum} is summable for the stated values of $m$ and
  $y$.  The summand in \cref{def:mangoldt-tail-term} is non-negative whenever
  it is selected: the von Mangoldt function is non-negative and the denominator
  is non-negative; the unselected summands are zero.  The standard comparison of
  a finite sum with the t-sum of a summable real series whose omitted terms are
  non-negative gives the asserted bound for the finite set $S$. -/)
  (title := /-- Finite tails are bounded by the full von Mangoldt tail -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_finite_sum_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y)
    (s : Finset ℕ) :
    (∑ q ∈ s, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
      mangoldt_tail_sum m y := by
  obtain ⟨_, _, hbound⟩ := mangoldt_tail_upper_bound
  have hsumm : Summable (fun q : ℕ =>
      if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) :=
    (hbound m hm y hy).1
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  simpa [mangoldt_tail_sum] using hsumm.sum_le_tsum s (fun q _ => hnonneg q)

@[blueprint "lem:mangoldt-dirichlet-series-summable-local"
  (statement := /-- For every real number $u>0$, the real von Mangoldt
  Dirichlet series defining $\sum_q\Lambda(q)q^{-1-u}$ is summable. -/)
  (proof := /-- This is the real form of the Mathlib absolute convergence of
  the von Mangoldt $L$-series in the half-plane $\operatorname{Re}s>1$,
  specialized to $s=1+u$ and then transported along the coercion
  $\mathbb{R}\to\mathbb{C}$. -/)
  (title := /-- Summability of the real von Mangoldt Dirichlet series -/)
  (latexEnv := "lemma")]
lemma mangoldt_dirichlet_series_summable_local :
    ∀ u : ℝ, 0 < u ->
      Summable (fun q : ℕ =>
        ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)) := by
  intro u hu
  have hs : 1 < (((1 + u : ℝ) : ℂ).re) := by
    simp
    linarith
  have hcomplex := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := ((1 + u : ℝ) : ℂ)) hs
  rw [LSeriesSummable] at hcomplex
  have hcomplex' : Summable (fun q : ℕ =>
      ((ArithmeticFunction.vonMangoldt q /
        Real.rpow (q : ℝ) (1 + u) : ℝ) : ℂ)) := by
    refine hcomplex.congr ?_
    intro q
    by_cases hq : q = 0
    · subst q
      simp [LSeries.term_def, Real.zero_rpow (by linarith : (1 : ℝ) + u ≠ 0)]
    · rw [LSeries.term_of_ne_zero hq]
      rw [Complex.ofReal_div]
      congr 1
      exact (Complex.ofReal_cpow (Nat.cast_nonneg q) (1 + u)).symm
  exact Complex.summable_ofReal.mp hcomplex'

@[blueprint "lem:mangoldt-dirichlet-series-finite-threshold-bound-local"
  (statement := /-- For every real number $u>0$ and every natural cutoff $N$,
  the finite sum of $\Lambda(q)q^{-1-u}$ over natural $q<N$ with $q\geq 2$ is
  at most $1/u$. -/)
  (proof := /-- By
  \cref{lem:mangoldt-dirichlet-series-summable-local}, the full real
  von Mangoldt Dirichlet series is summable.  Its summands are non-negative, so
  the finite thresholded sum is at most the full t-sum.  The latter is bounded
  by $1/u$ by \cref{lem:von-mangoldt-dirichlet-series-upper-bound}. -/)
  (title := /-- Finite thresholded Dirichlet sums -/)
  (latexEnv := "lemma")]
lemma mangoldt_dirichlet_series_finite_threshold_bound_local :
    ∀ u : ℝ, 0 < u -> ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)
        else 0) ≤ 1 / u := by
  intro u hu N
  have hsumm := mangoldt_dirichlet_series_summable_local u hu
  have hnonneg : ∀ q : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) := by
    intro q
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg q) (1 + u))
  calc
    (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u)
        else 0) ≤
        ∑ q ∈ Finset.range N,
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + u) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      split_ifs
      · rfl
      · exact hnonneg q
    _ ≤ mangoldt_dirichlet_series u := by
      simpa [mangoldt_dirichlet_series] using
        hsumm.sum_le_tsum (Finset.range N) (fun q _ => hnonneg q)
    _ ≤ 1 / u := von_mangoldt_dirichlet_series_upper_bound u hu

@[blueprint "lem:log-square-integral-kernel-local"
  (statement := /-- For every real number $r>0$,
  $\int_0^\infty t e^{-rt}\,dt=1/r^2$. -/)
  (proof := /-- This is the specialization of the Gamma-integral identity to
  exponent $2$, together with the value $\Gamma(2)=1$. -/)
  (title := /-- The logarithmic square integral kernel -/)
  (latexEnv := "lemma")]
lemma log_square_integral_kernel_local (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t))) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := r) (by norm_num) hr
  calc
    (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      norm_num [Real.rpow_one]
    _ = (1 / r) ^ (2 : ℝ) * Real.Gamma 2 := h
    _ = 1 / r ^ 2 := by
      rw [Real.Gamma_two, Real.rpow_two]
      field_simp [hr.ne']

@[blueprint "lem:log-square-integral-kernel-integrable-local"
  (statement := /-- For every real number $r>0$, the function
  $t\mapsto t e^{-rt}$ is integrable on $(0,\infty)$. -/)
  (proof := /-- Apply the standard exponential-polynomial integrability
  criterion with exponent $v=-r$ and perturbation $r/2$.  The two required
  exponential functions have negative rates on $(0,\infty)$, hence are
  integrable there. -/)
  (title := /-- Integrability of the logarithmic square kernel -/)
  (latexEnv := "lemma")]
lemma log_square_integral_kernel_integrable_local (r : ℝ) (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-(r * t)))
      (Set.Ioi 0) := by
  have hhalf_ne : r / 2 ≠ 0 := by positivity
  have hrate_pos : -r + r / 2 < 0 := by linarith
  have hrate_neg : -r - r / 2 < 0 := by linarith
  have hint_pos : MeasureTheory.Integrable
      (fun t : ℝ => Real.exp ((-r + r / 2) * t))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_Ioi hrate_pos 0
  have hint_neg : MeasureTheory.Integrable
      (fun t : ℝ => Real.exp ((-r - r / 2) * t))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_Ioi hrate_neg 0
  have h := ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
    (X := fun t : ℝ => t) (v := -r) (t := r / 2)
    hhalf_ne hint_pos hint_neg 1
  simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h

@[blueprint "lem:mangoldt-tail-term-integral-local"
  (statement := /-- If $m\geq 1$ and $q\geq 2$, then the von Mangoldt tail
  summand is the integral of the Laplace kernel
  $(\Lambda(q)/q)t(mq)^{-t}$ over $t>0$. -/)
  (proof := /-- Since $mq\geq 2$, the logarithm of $mq$ is positive.  Apply
  \cref{lem:log-square-integral-kernel-local} with
  $r=\log(mq)$ and rewrite $(mq)^{-t}$ as $e^{-t\log(mq)}$.  Multiplying the
  resulting identity by $\Lambda(q)/q$ gives the defining tail summand. -/)
  (title := /-- Integral form of one von Mangoldt tail summand -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_term_integral_local (m q : ℕ) (hm : 1 ≤ m) (hq : 2 ≤ q) :
    mangoldt_tail_term m q =
      ∫ t : ℝ in Set.Ioi 0,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) := by
  have hmq_two : 2 ≤ m * q := Nat.mul_le_mul hm hq
  have hmq_pos : 0 < (((m * q : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hmq_two)
  have hlog_pos : 0 < Real.log (((m * q : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hmq_two)
  have hkernel :
      (∫ t : ℝ in Set.Ioi 0,
        t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) =
        1 / Real.log (((m * q : ℕ) : ℝ)) ^ 2 := by
    have hfun : (fun t : ℝ => t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) =
        fun t : ℝ => t * Real.exp (-(Real.log (((m * q : ℕ) : ℝ)) * t)) := by
      funext t
      change t * (((m * q : ℕ) : ℝ) ^ (-t)) =
        t * Real.exp (-(Real.log (((m * q : ℕ) : ℝ)) * t))
      rw [Real.rpow_def_of_pos hmq_pos]
      ring_nf
    rw [hfun]
    exact log_square_integral_kernel_local
      (Real.log (((m * q : ℕ) : ℝ))) hlog_pos
  calc
    mangoldt_tail_term m q =
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (1 / Real.log (((m * q : ℕ) : ℝ)) ^ 2) := by
      rw [mangoldt_tail_term]
      ring
    _ = (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
        (∫ t : ℝ in Set.Ioi 0,
          t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) := by
      rw [hkernel]
    _ = ∫ t : ℝ in Set.Ioi 0,
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((m * q : ℕ) : ℝ)) (-t)) := by
      rw [MeasureTheory.integral_const_mul]

@[blueprint "lem:mangoldt-tail-integrand-factor-local"
  (statement := /-- Let $n\geq 2$, let $N$ be a natural cutoff, and let $t$ be
  real.  The finite integral-side von Mangoldt tail integrand factors as
  $t n^{-t}$ times the corresponding finite Dirichlet sum with exponent
  $1+t$. -/)
  (proof := /-- Distribute the common factor $t n^{-t}$ across the finite sum.
  For each selected $q\geq 2$, use $(nq)^{-t}=n^{-t}q^{-t}$ and
  $q^{1+t}=q q^t$; unselected terms are both zero. -/)
  (title := /-- Factoring the finite tail integrand -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_integrand_factor_local (n N : ℕ) (t : ℝ) (hn : 2 ≤ n) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
      else 0) =
      t * Real.rpow (n : ℝ) (-t) *
        (∑ q ∈ Finset.range N,
          if (2 : ℝ) ≤ (q : ℝ) then
            ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + t)
          else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
  · have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
    have hq_nat : 2 ≤ q := by
      exact_mod_cast hqcond
    have hq_pos : 0 < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq_nat)
    simp [hqcond]
    rw [Real.mul_rpow hn_pos.le hq_pos.le]
    rw [Real.rpow_add hq_pos (1 : ℝ) t, Real.rpow_one]
    rw [Real.rpow_neg hq_pos.le t]
    field_simp [hq_pos.ne', (Real.rpow_pos_of_pos hq_pos t).ne']
  · simp [hqcond]

@[blueprint "lem:mangoldt-tail-range-subinvariant-local"
  (statement := /-- For every natural number $n\geq 2$ and every natural
  cutoff $N$, the finite thresholded von Mangoldt tail sum up to $N$ is at most
  $1/\log n$. -/)
  (proof := /-- Rewrite each selected summand by
  \cref{lem:mangoldt-tail-term-integral-local}; the integrability needed to
  exchange the finite sum with the integral follows from
  \cref{lem:log-square-integral-kernel-integrable-local}.  By
  \cref{lem:mangoldt-tail-integrand-factor-local}, the
  resulting integrand is $t n^{-t}$ times a finite Dirichlet sum.  The finite
  Dirichlet sum is at most $1/t$ for $t>0$ by
  \cref{lem:mangoldt-dirichlet-series-finite-threshold-bound-local}.  The
  integrand is therefore bounded by $n^{-t}$, whose integral over $t>0$ is
  $1/\log n$. -/)
  (title := /-- Finite sub-invariance bound for the von Mangoldt tail -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_range_subinvariant_local (n N : ℕ) (hn : 2 ≤ n) :
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) ≤
      1 / Real.log (n : ℝ) := by
  have hm : 1 ≤ n := by omega
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  let F : ℝ → ℝ := fun t =>
    ∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then
        (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
          (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
      else 0
  have hterm_int : ∀ q ∈ Finset.range N,
      MeasureTheory.Integrable
        (fun t : ℝ =>
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
          else 0)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro q hq
    by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
    · have hq_nat : 2 ≤ q := by
        exact_mod_cast hqcond
      have hnq_two : 2 ≤ n * q := Nat.mul_le_mul hm hq_nat
      have hnq_pos : 0 < (((n * q : ℕ) : ℝ)) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hnq_two)
      have hlog_nq_pos : 0 < Real.log (((n * q : ℕ) : ℝ)) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hnq_two)
      have hbase_int : MeasureTheory.IntegrableOn
          (fun t : ℝ => t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
          (Set.Ioi 0) := by
        have h := log_square_integral_kernel_integrable_local
          (Real.log (((n * q : ℕ) : ℝ))) hlog_nq_pos
        have hfun : (fun t : ℝ => t * Real.rpow (((n * q : ℕ) : ℝ)) (-t)) =
            fun t : ℝ => t * Real.exp (-(Real.log (((n * q : ℕ) : ℝ)) * t)) := by
          funext t
          change t * (((n * q : ℕ) : ℝ) ^ (-t)) =
            t * Real.exp (-(Real.log (((n * q : ℕ) : ℝ)) * t))
          rw [Real.rpow_def_of_pos hnq_pos]
          ring_nf
        rw [hfun]
        exact h
      simpa [hqcond] using
        hbase_int.const_mul (ArithmeticFunction.vonMangoldt q / (q : ℝ))
    · simpa [hqcond]
  have hF_int : MeasureTheory.IntegrableOn F (Set.Ioi 0) := by
    have hF_int' : MeasureTheory.Integrable
        (∑ q ∈ Finset.range N, fun t : ℝ =>
          if (2 : ℝ) ≤ (q : ℝ) then
            (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
              (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
          else 0)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      MeasureTheory.integrable_finset_sum' (Finset.range N) hterm_int
    dsimp [F, MeasureTheory.IntegrableOn]
    convert hF_int' using 1
    funext t
    simp [Finset.sum_apply]
  have hG_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-(Real.log (n : ℝ) * t))) (Set.Ioi 0) := by
    have hrate : -Real.log (n : ℝ) < 0 := by linarith
    convert integrableOn_exp_mul_Ioi hrate 0 using 1
    funext t
    ring_nf
  have hsum_integral :
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) =
        ∫ t : ℝ in Set.Ioi 0, F t := by
    calc
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) =
          ∑ q ∈ Finset.range N,
            ∫ t : ℝ in Set.Ioi 0,
              if (2 : ℝ) ≤ (q : ℝ) then
                (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
                  (t * Real.rpow (((n * q : ℕ) : ℝ)) (-t))
              else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hqcond : (2 : ℝ) ≤ (q : ℝ)
        · have hq_nat : 2 ≤ q := by
            exact_mod_cast hqcond
          simp [hqcond, mangoldt_tail_term_integral_local n q hm hq_nat]
        · simp [hqcond]
      _ = ∫ t : ℝ in Set.Ioi 0, F t := by
        symm
        dsimp [F]
        exact MeasureTheory.integral_finset_sum (Finset.range N) hterm_int
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      F t ≤ Real.exp (-(Real.log (n : ℝ) * t)) := by
    intro t ht
    have htpos : 0 < t := ht
    have hdir := mangoldt_dirichlet_series_finite_threshold_bound_local t htpos N
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (-t) :=
      Real.rpow_nonneg hn_pos.le (-t)
    have hcoef_nonneg : 0 ≤ t * Real.rpow (n : ℝ) (-t) := by positivity
    calc
      F t = t * Real.rpow (n : ℝ) (-t) *
          (∑ q ∈ Finset.range N,
            if (2 : ℝ) ≤ (q : ℝ) then
              ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + t)
            else 0) := by
        simpa [F] using mangoldt_tail_integrand_factor_local n N t hn
      _ ≤ t * Real.rpow (n : ℝ) (-t) * (1 / t) := by
        exact mul_le_mul_of_nonneg_left hdir hcoef_nonneg
      _ = Real.rpow (n : ℝ) (-t) := by
        field_simp [htpos.ne']
      _ = Real.exp (-(Real.log (n : ℝ) * t)) := by
        change ((n : ℝ) ^ (-t)) = Real.exp (-(Real.log (n : ℝ) * t))
        rw [Real.rpow_def_of_pos hn_pos]
        ring_nf
  have hintegral_le :
      (∫ t : ℝ in Set.Ioi 0, F t) ≤
        ∫ t : ℝ in Set.Ioi 0, Real.exp (-(Real.log (n : ℝ) * t)) := by
    exact MeasureTheory.setIntegral_mono_on hF_int hG_int measurableSet_Ioi hpoint
  have hG_integral :
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-(Real.log (n : ℝ) * t))) =
        1 / Real.log (n : ℝ) := by
    have hrate : -Real.log (n : ℝ) < 0 := by linarith
    have h := integral_exp_mul_Ioi (a := -Real.log (n : ℝ)) hrate 0
    simpa [hlog_pos.ne'] using h
  calc
    (∑ q ∈ Finset.range N,
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) =
        ∫ t : ℝ in Set.Ioi 0, F t := hsum_integral
    _ ≤ ∫ t : ℝ in Set.Ioi 0, Real.exp (-(Real.log (n : ℝ) * t)) := hintegral_le
    _ = 1 / Real.log (n : ℝ) := hG_integral

@[blueprint "lem:mangoldt-subinvariant-bound"
  (statement := /-- For every natural number $n$ with $n\geq 2$,
  $\log n\sum_{q\in\mathbb{N},\ q\geq 2}
  \Lambda(q)/(q\log^2(nq))\leq 1$. -/)
  (proof := /-- Fix a natural number $n\geq 2$.  By
  \cref{lem:mangoldt-tail-range-subinvariant-local}, every finite partial sum
  of the non-negative tail summands is at most $1/\log n$.  Therefore the
  corresponding real series is summable and its t-sum, which is
  \cref{def:mangoldt-tail-sum} with threshold $2$, is also at most
  $1/\log n$.  Since $\log n>0$, multiplying this inequality by $\log n$ gives
  the asserted bound. -/)
  (title := /-- Non-asymptotic sub-invariance estimate -/)
  (latexEnv := "lemma")]
lemma mangoldt_subinvariant_bound :
    ∀ n : ℕ, 2 ≤ n -> Real.log (n : ℝ) * mangoldt_tail_sum n 2 ≤ 1 := by
  intro n hn
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hnonneg : ∀ q : ℕ, 0 ≤
      (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
    intro q
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · norm_num
  have hbound : ∀ N : ℕ,
      (∑ q ∈ Finset.range N,
        if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) ≤
        1 / Real.log (n : ℝ) := by
    intro N
    exact mangoldt_tail_range_subinvariant_local n N hn
  have hsumm : Summable (fun q : ℕ =>
      if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) :=
    summable_of_sum_range_le hnonneg hbound
  have htail : mangoldt_tail_sum n 2 ≤ 1 / Real.log (n : ℝ) := by
    simpa [mangoldt_tail_sum] using hsumm.tsum_le_of_sum_range_le hbound
  calc
    Real.log (n : ℝ) * mangoldt_tail_sum n 2 ≤
        Real.log (n : ℝ) * (1 / Real.log (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htail hlog_pos.le
    _ = 1 := by
      field_simp [hlog_pos.ne']

@[blueprint "def:finite-chain-initial-mass"
  (statement := /-- For real parameters $x$ and $X$, and for a natural number
  $n$, this is the finite initial mass
  $b_{x,X}(n)$ used in the truncated von Mangoldt downward chain. It is zero
  outside the real interval $[x,X]$, while on that interval it is
  $\nu_0(n)$ minus the total incoming von Mangoldt mass from states $nq\leq X$,
  namely
  $\sum_{q\geq2,\ nq\leq X}\nu_0(nq)\Lambda(q)/\log(nq)$. -/)
  (title := /-- Finite von Mangoldt initial mass -/)
  (latexEnv := "definition")]
noncomputable def finite_chain_initial_mass (x X : ℝ) (n : ℕ) : ℝ :=
  if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then
    erdos_weight n -
      ∑' q : ℕ,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0
  else 0

@[blueprint "lem:finite-chain-erdos-le-initial-mass"
  (statement := /-- Let $x\geq2$, let $X$ be real, and let $A\subseteq\mathbb N$
  be primitive and supported in $[x,X]$. Then the Erd\H{o}s sum of $A$ is at
  most the total finite initial mass $\sum_n b_{x,X}(n)$ from
  \cref{def:finite-chain-initial-mass}. -/)
  (proof := /-- Put $b(n)=b_{x,X}(n)$ as in
  \cref{def:finite-chain-initial-mass}. First prove $b(n)\geq0$ for every
  $n$. If $x\leq n\leq X$, then $n\geq2$; the finite incoming sum over $q$ with
  $nq\leq X$ is bounded by $n^{-1}$ times the full tail at threshold $2$, using
  \cref{lem:mangoldt-tail-finite-sum-le}, and
  \cref{lem:mangoldt-subinvariant-bound} bounds this by
  $(n\log n)^{-1}=\nu_0(n)$. Outside $[x,X]$ the mass is zero.
  It remains to bound each finite partial sum of \cref{def:erdos-sum}. Fix a
  finite set of indices $s$ and restrict to the finite interval
  $R=\{n:x\leq n\leq X\}$. Let $H(n)$ be the indicator that $n$ is divisible by
  some element of $A\cap s$. For each $r\in R$, the contribution of
  $A\cap s$ at $r$ plus the $H$-weighted incoming contribution from factor pairs
  $nq=r$ is at most $H(r)\nu_0(r)$. If $r\in A\cap s$, the incoming term
  vanishes by \cref{def:primitive-set}; if $H(r)=0$, it vanishes by definition;
  otherwise it is bounded by the full von Mangoldt divisor sum, which is
  $\log r$ by \cref{lem:von-mangoldt-divisor-sum}. Summing these inequalities
  over $r\in R$ and reindexing the fibers $(n,q)$ gives the partial-sum bound
  by $\sum_{n\in R}H(n)b(n)$. Since $0\leq H(n)\leq1$ and $b(n)\geq0$, this is
  at most $\sum_{n\in R}b(n)$, which is the stated t-sum because
  \cref{def:supported-in-interval,def:finite-chain-initial-mass} gives finite
  support. -/)
  (title := /-- Hitting mass bounds the finite Erd\H{o}s sum -/)
  (latexEnv := "lemma")]
lemma finite_chain_erdos_le_initial_mass (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ ∑' n : ℕ, finite_chain_initial_mass x X n := by
  classical
  have hmass_nonneg : ∀ n : ℕ, 0 ≤ finite_chain_initial_mass x X n := by
    intro n
    rw [finite_chain_initial_mass]
    by_cases hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X
    · rw [if_pos hnint]
      have hn_two : 2 ≤ n := by exact_mod_cast (le_trans hx hnint.1)
      have hn_one : 1 ≤ n := by omega
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn_two)
      have hinner_le :
          (∑' q : ℕ,
            if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
              erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                Real.log ((n * q : ℕ) : ℝ)
            else 0) ≤ (1 / (n : ℝ)) * mangoldt_tail_sum n 2 := by
        apply tsum_le_of_sum_le'
        · apply mul_nonneg
          · positivity
          · rw [mangoldt_tail_sum]
            apply tsum_nonneg
            intro q
            split_ifs
            · rw [mangoldt_tail_term]
              exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
            · norm_num
        · intro s
          have hpoint : ∀ q : ℕ,
              (if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                  Real.log ((n * q : ℕ) : ℝ)
              else 0) ≤
                (1 / (n : ℝ)) *
                  (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
            intro q
            by_cases hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
            · rw [if_pos hqcond]
              have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqcond.1
              rw [if_pos hqreal]
              rw [erdos_weight, mangoldt_tail_term]
              rw [Nat.cast_mul]
              ring_nf
              exact le_rfl
            · rw [if_neg hqcond]
              apply mul_nonneg
              · positivity
              · split_ifs
                · rw [mangoldt_tail_term]
                  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
                · norm_num
          calc
            (∑ q ∈ s,
              if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                  Real.log ((n * q : ℕ) : ℝ)
              else 0) ≤
                ∑ q ∈ s,
                  (1 / (n : ℝ)) *
                    (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
                apply Finset.sum_le_sum
                intro q _
                exact hpoint q
            _ = (1 / (n : ℝ)) *
                  ∑ q ∈ s,
                    (if (2 : ℝ) ≤ (q : ℝ) then mangoldt_tail_term n q else 0) := by
                rw [Finset.mul_sum]
            _ ≤ (1 / (n : ℝ)) * mangoldt_tail_sum n 2 := by
                exact mul_le_mul_of_nonneg_left
                  (mangoldt_tail_finite_sum_le n hn_one 2 (by norm_num) s) (by positivity)
      have htail_le : mangoldt_tail_sum n 2 ≤ 1 / Real.log (n : ℝ) := by
        rw [le_div_iff₀ hlog_pos]
        simpa [mul_comm] using mangoldt_subinvariant_bound n hn_two
      have hscaled_le : (1 / (n : ℝ)) * mangoldt_tail_sum n 2 ≤ erdos_weight n := by
        calc
          (1 / (n : ℝ)) * mangoldt_tail_sum n 2 ≤
              (1 / (n : ℝ)) * (1 / Real.log (n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left htail_le (by positivity)
          _ = erdos_weight n := by
              rw [erdos_weight]
              ring_nf
      linarith
    · rw [if_neg hnint]
  rw [erdos_sum]
  apply tsum_le_of_sum_le'
  · exact tsum_nonneg hmass_nonneg
  · intro s
    let M : ℕ := ⌈X⌉₊ + 1
    let R : Finset ℕ := (Finset.range M).filter (fun n => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    have hb_tsum_eq :
        (∑' n : ℕ, finite_chain_initial_mass x X n) =
          ∑ n ∈ R, finite_chain_initial_mass x X n := by
      exact tsum_eq_sum (s := R) (fun n hn => by
        have hnnot : ¬ (x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) := by
          intro hnx
          apply hn
          have hn_le_ceil : n ≤ ⌈X⌉₊ := by
            exact_mod_cast (le_trans hnx.2 (Nat.le_ceil X))
          have hn_lt_M : n < M := by
            dsimp [M]
            omega
          simp [R, hn_lt_M, hnx]
        rw [finite_chain_initial_mass, if_neg hnnot])
    have hleft_eq :
        (∑ i ∈ s, A.indicator erdos_weight i) =
          ∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0 := by
      have hs_eq :
          (∑ i ∈ s, A.indicator erdos_weight i) =
            ∑ i ∈ s.filter (fun i => i ∈ A), erdos_weight i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hiA : i ∈ A
        · simp [Set.indicator_of_mem hiA, hiA]
        · simp [Set.indicator_of_notMem hiA, hiA]
      have hR_eq :
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) =
            ∑ n ∈ R.filter (fun n => n ∈ s ∧ n ∈ A), erdos_weight n := by
        exact (Finset.sum_filter (s := R)
          (p := fun n => n ∈ s ∧ n ∈ A) (f := erdos_weight)).symm
      rw [hs_eq, hR_eq]
      symm
      apply Finset.sum_bij (fun n hn => n)
      · intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.2.1, hn.2.2⟩
      · intro a ha b hb h
        exact h
      · intro b hb
        simp only [Finset.mem_filter] at hb
        have hB := hsupp b hb.2
        have hb_le_ceil : b ≤ ⌈X⌉₊ := by
          exact_mod_cast (le_trans hB.2 (Nat.le_ceil X))
        have hb_lt_M : b < M := by
          dsimp [M]
          omega
        refine ⟨b, ?_, rfl⟩
        simp [R, hb_lt_M, hB, hb]
      · intro n hn
        rfl
    have hmass_finite (n : ℕ) (hnR : n ∈ R) :
        finite_chain_initial_mass x X n = erdos_weight n -
          ∑ q ∈ Finset.range M,
            if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
              erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                Real.log ((n * q : ℕ) : ℝ)
            else 0 := by
      have hnR' : n < M ∧ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
        simpa [R] using hnR
      have hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := hnR'.2
      rw [finite_chain_initial_mass, if_pos hnint]
      congr 1
      exact tsum_eq_sum (s := Finset.range M) (fun q hq => by
        have hqnot : ¬ (2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X) := by
          intro hcond
          apply hq
          have hq_le_prod : q ≤ n * q := by
            have hn_one : 1 ≤ n := by
              have hn_two : 2 ≤ n := by exact_mod_cast (le_trans hx hnint.1)
              omega
            exact Nat.le_mul_of_pos_left q hn_one
          have hq_le_X : (q : ℝ) ≤ X := by
            have : ((q : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by
              exact_mod_cast hq_le_prod
            exact le_trans this hcond.2
          have hq_le_ceil : q ≤ ⌈X⌉₊ := by
            exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
          have hq_lt_M : q < M := by
            dsimp [M]
            omega
          exact Finset.mem_range.mpr hq_lt_M
        rw [if_neg hqnot])
    have hfinite :
        (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) ≤
          ∑ n ∈ R, finite_chain_initial_mass x X n := by
      let shadow : ℕ → ℝ := fun n =>
        if ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ n then 1 else 0
      let pairs : Finset (ℕ × ℕ) := R.product (Finset.range M)
      let pairTerm : ℕ × ℕ → ℝ := fun p =>
        if 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) then
          shadow p.1 * (erdos_weight (p.1 * p.2) *
            ArithmeticFunction.vonMangoldt p.2 / Real.log ((p.1 * p.2 : ℕ) : ℝ))
        else 0
      have hshadow_le_one : ∀ n, shadow n ≤ 1 := by
        intro n
        dsimp [shadow]
        split_ifs <;> norm_num
      have hfiber_bound : ∀ r ∈ R,
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p ≤ erdos_weight r := by
        intro r hr
        have hrR : r < M ∧ x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X := by
          simpa [R] using hr
        have hr_two : 2 ≤ r := by exact_mod_cast (le_trans hx hrR.2.1)
        have hr_ne : r ≠ 0 := by omega
        have hlog_pos : 0 < Real.log (r : ℝ) := by
          apply Real.log_pos
          exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hr_two)
        let F : Finset (ℕ × ℕ) := pairs.filter (fun p => p.1 * p.2 = r)
        let boundTerm : ℕ → ℝ := fun q =>
          erdos_weight r * ArithmeticFunction.vonMangoldt q / Real.log (r : ℝ)
        have hbound_nonneg : ∀ q, 0 ≤ boundTerm q := by
          intro q
          dsimp [boundTerm]
          have hw : 0 ≤ erdos_weight r := by
            rw [erdos_weight]
            positivity
          exact div_nonneg (mul_nonneg hw ArithmeticFunction.vonMangoldt_nonneg) hlog_pos.le
        have hpoint : ∀ p ∈ F, pairTerm p ≤ boundTerm p.2 := by
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hprod : p.1 * p.2 = r := hp'.2
          dsimp [pairTerm, boundTerm]
          by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
          · rw [if_pos hcond, hprod]
            simpa using
              mul_le_mul_of_nonneg_right (hshadow_le_one p.1) (hbound_nonneg p.2)
          · rw [if_neg hcond]
            exact hbound_nonneg p.2
        have hsum_le : (∑ p ∈ F, pairTerm p) ≤ ∑ p ∈ F, boundTerm p.2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hpoint p hp
        have hsum_image : (∑ p ∈ F, boundTerm p.2) =
            ∑ q ∈ F.image Prod.snd, boundTerm q := by
          symm
          rw [Finset.sum_image]
          intro a ha b hb hab
          have ha' := Finset.mem_filter.mp ha
          have hb' := Finset.mem_filter.mp hb
          have hpa : a.1 * a.2 = r := ha'.2
          have hpb : b.1 * b.2 = r := hb'.2
          have ha2_pos : 0 < a.2 := by
            by_contra hnot
            have ha2z : a.2 = 0 := Nat.eq_zero_of_not_pos hnot
            rw [ha2z] at hpa
            simp at hpa
            exact hr_ne hpa.symm
          have hfst : a.1 = b.1 := by
            apply Nat.mul_right_cancel ha2_pos
            rw [hpa, hab, hpb]
          exact Prod.ext hfst hab
        have himage_subset : F.image Prod.snd ⊆ r.divisors := by
          intro q hq
          rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
          have hp' := Finset.mem_filter.mp hp
          have hprod : p.1 * p.2 = r := hp'.2
          have hqdiv : p.2 ∣ r := by
            refine ⟨p.1, ?_⟩
            rw [mul_comm, hprod]
          exact Nat.mem_divisors.mpr ⟨hqdiv, hr_ne⟩
        have himage_le : (∑ q ∈ F.image Prod.snd, boundTerm q) ≤
            ∑ q ∈ r.divisors, boundTerm q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact himage_subset
          · intro q hq hqnot
            exact hbound_nonneg q
        have hdiv_eq : (∑ q ∈ r.divisors, boundTerm q) = erdos_weight r := by
          dsimp [boundTerm]
          calc
            (∑ q ∈ r.divisors,
              erdos_weight r * ArithmeticFunction.vonMangoldt q / Real.log (r : ℝ)) =
                (erdos_weight r / Real.log (r : ℝ)) *
                  ∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q hq
                ring
            _ = (erdos_weight r / Real.log (r : ℝ)) * Real.log (r : ℝ) := by
                rw [von_mangoldt_divisor_sum]
            _ = erdos_weight r := by
                field_simp [hlog_pos.ne']
        calc
          (∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p) =
              ∑ p ∈ F, pairTerm p := rfl
          _ ≤ ∑ p ∈ F, boundTerm p.2 := hsum_le
          _ = ∑ q ∈ F.image Prod.snd, boundTerm q := hsum_image
          _ ≤ ∑ q ∈ r.divisors, boundTerm q := himage_le
          _ = erdos_weight r := hdiv_eq
      have hfiber_zero_active : ∀ r ∈ R, r ∈ s ∧ r ∈ A ->
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p = 0 := by
        intro r hr hactive
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprod : p.1 * p.2 = r := hp'.2
        dsimp [pairTerm]
        by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
        · rw [if_pos hcond]
          have hshadow_p1 : shadow p.1 = 0 := by
            dsimp [shadow]
            rw [if_neg]
            intro hex
            rcases hex with ⟨a, has, haA, hadiv⟩
            have hadivr : a ∣ r := by
              rcases hadiv with ⟨k, hk⟩
              refine ⟨k * p.2, ?_⟩
              rw [← hprod, hk, Nat.mul_assoc]
            have har : a = r := hprim.eq haA hactive.2 hadivr
            subst a
            have hrR : r < M ∧ x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X := by
              simpa [R] using hr
            have hp2_gt_one : 1 < p.2 := by omega
            have hp1_pos : 0 < p.1 := by
              by_contra hp10
              have hp1z : p.1 = 0 := Nat.eq_zero_of_not_pos hp10
              rw [hp1z] at hprod
              simp at hprod
              have hr_two : 2 ≤ r := by exact_mod_cast (le_trans hx hrR.2.1)
              omega
            have hp1_lt_r : p.1 < r := by
              rw [← hprod]
              exact lt_mul_of_one_lt_right hp1_pos hp2_gt_one
            exact not_le_of_gt hp1_lt_r (Nat.le_of_dvd hp1_pos hadiv)
          rw [hshadow_p1]
          ring
        · rw [if_neg hcond]
      have hshadow_factor_zero : ∀ r ∈ R, shadow r = 0 ->
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p = 0 := by
        intro r hr hsr
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hprod : p.1 * p.2 = r := hp'.2
        dsimp [pairTerm]
        by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
        · rw [if_pos hcond]
          have hshadow_p1 : shadow p.1 = 0 := by
            dsimp [shadow] at hsr ⊢
            by_cases hex : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ p.1
            · exfalso
              have hexr : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ r := by
                rcases hex with ⟨a, has, haA, hadiv⟩
                refine ⟨a, has, haA, ?_⟩
                rcases hadiv with ⟨k, hk⟩
                refine ⟨k * p.2, ?_⟩
                rw [← hprod, hk, Nat.mul_assoc]
              rw [if_pos hexr] at hsr
              norm_num at hsr
            · rw [if_neg hex]
          rw [hshadow_p1]
          ring
        · rw [if_neg hcond]
      have hfiber : ∀ r ∈ R,
          (if r ∈ s ∧ r ∈ A then erdos_weight r else 0) +
            ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p ≤
              shadow r * erdos_weight r := by
        intro r hr
        by_cases hactive : r ∈ s ∧ r ∈ A
        · have hsh : shadow r = 1 := by
            dsimp [shadow]
            rw [if_pos]
            exact ⟨r, hactive.1, hactive.2, dvd_rfl⟩
          rw [if_pos hactive, hfiber_zero_active r hr hactive, hsh]
          linarith
        · rw [if_neg hactive]
          by_cases hshadow : shadow r = 0
          · rw [hshadow_factor_zero r hr hshadow, hshadow]
            norm_num
          · have hsh : shadow r = 1 := by
              dsimp [shadow] at hshadow ⊢
              by_cases hex : ∃ a : ℕ, a ∈ s ∧ a ∈ A ∧ a ∣ r
              · rw [if_pos hex]
              · rw [if_neg hex] at hshadow
                exfalso
                exact hshadow rfl
            rw [hsh]
            simpa using hfiber_bound r hr
      have hsum_fiber :
          (∑ r ∈ R, ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p) =
            ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p := by
        exact Finset.sum_fiberwise_eq_sum_filter pairs R
          (fun p : ℕ × ℕ => p.1 * p.2) pairTerm
      have hupper :
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p ≤
            ∑ n ∈ R, shadow n * erdos_weight n := by
        calc
          (∑ n ∈ R, if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p =
                ∑ n ∈ R,
                  ((if n ∈ s ∧ n ∈ A then erdos_weight n else 0) +
                    ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = n), pairTerm p) := by
                rw [Finset.sum_add_distrib, hsum_fiber]
          _ ≤ ∑ n ∈ R, shadow n * erdos_weight n := by
                apply Finset.sum_le_sum
                intro n hn
                exact hfiber n hn
      have hpair_all_eq :
          (∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p) =
            ∑ p ∈ pairs, pairTerm p := by
        apply Finset.sum_subset
        · intro p hp
          exact (Finset.mem_filter.mp hp).1
        · intro p hpairs hpnot
          have hprod_not : p.1 * p.2 ∉ R := by
            intro hpR
            apply hpnot
            simp [hpairs, hpR]
          have hp : p.1 ∈ R ∧ p.2 ∈ Finset.range M := by
            simpa [pairs] using hpairs
          dsimp [pairTerm]
          by_cases hcond : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
          · exfalso
            apply hprod_not
            have hp1R : p.1 < M ∧ x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X := by
              simpa [R] using hp.1
            have hp2one : 1 ≤ p.2 := by omega
            have hp1_le_prod : p.1 ≤ p.1 * p.2 :=
              Nat.le_mul_of_pos_right p.1 hp2one
            have hxprod : x ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
              have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by
                exact_mod_cast hp1_le_prod
              exact le_trans hp1R.2.1 this
            have hprod_le_ceil : p.1 * p.2 ≤ ⌈X⌉₊ := by
              exact_mod_cast (le_trans hcond.2 (Nat.le_ceil X))
            have hprod_lt_M : p.1 * p.2 < M := by
              dsimp [M]
              omega
            simp only [R, Finset.mem_filter, Finset.mem_range]
            exact ⟨hprod_lt_M, by simpa [Nat.cast_mul] using hxprod,
              by simpa [Nat.cast_mul] using hcond.2⟩
          · rw [if_neg hcond]
      have hpair_product :
          (∑ p ∈ pairs, pairTerm p) =
            ∑ n ∈ R, shadow n *
              ∑ q ∈ Finset.range M,
                if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                  erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                    Real.log ((n * q : ℕ) : ℝ)
                else 0 := by
        dsimp [pairs, pairTerm]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Prod.fst, Prod.snd]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
        · simp [hcond]
        · simp [hcond]
      have hshadow_bound :
          (∑ n ∈ R, shadow n * erdos_weight n) ≤
            (∑ n ∈ R, finite_chain_initial_mass x X n) +
              ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ R), pairTerm p := by
        rw [hpair_all_eq, hpair_product]
        calc
          (∑ n ∈ R, shadow n * erdos_weight n) =
              ∑ n ∈ R, shadow n *
                (finite_chain_initial_mass x X n +
                  ∑ q ∈ Finset.range M,
                    if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                      erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                        Real.log ((n * q : ℕ) : ℝ)
                    else 0) := by
                apply Finset.sum_congr rfl
                intro n hn
                rw [hmass_finite n hn]
                ring
          _ = (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) +
              ∑ n ∈ R, shadow n *
                ∑ q ∈ Finset.range M,
                  if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                    erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                      Real.log ((n * q : ℕ) : ℝ)
                  else 0 := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro n hn
                ring
          _ ≤ (∑ n ∈ R, finite_chain_initial_mass x X n) +
              ∑ n ∈ R, shadow n *
                ∑ q ∈ Finset.range M,
                  if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
                    erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
                      Real.log ((n * q : ℕ) : ℝ)
                  else 0 := by
                have hsum_le :
                    (∑ n ∈ R, shadow n * finite_chain_initial_mass x X n) ≤
                      ∑ n ∈ R, finite_chain_initial_mass x X n := by
                  apply Finset.sum_le_sum
                  intro n hn
                  simpa using
                    mul_le_mul_of_nonneg_right (hshadow_le_one n) (hmass_nonneg n)
                linarith
      linarith
    rw [hb_tsum_eq, hleft_eq]
    exact hfinite

@[blueprint "lem:finite-chain-initial-mass-sum-eq-cut-capacity"
  (statement := /-- For every $x\geq2$ and every real $X$, the total finite
  initial mass $\sum_n b_{x,X}(n)$ from
  \cref{def:finite-chain-initial-mass} is exactly the finite cut capacity
  \cref{def:cut-capacity}. -/)
  (proof := /-- Expand \cref{def:finite-chain-initial-mass}.  The first part of
  the total mass is
  $\sum_{x\leq r\leq X}\nu_0(r)$; by
  \cref{lem:von-mangoldt-divisor-sum} and \cref{def:erdos-weight}, this is
  $\sum_{x\leq r\leq X}(r\log^2 r)^{-1}\sum_{q\mid r}\Lambda(q)$, with
  $x\geq2$ excluding the singular cases $r=0,1$.  The second part is a finite
  double sum over pairs $(n,q)$ with $x\leq n\leq X$, $q\geq2$, and $nq\leq X$.
  Relabeling $r=nq$ identifies this double sum with
  $\sum_{x\leq r\leq X}(r\log^2 r)^{-1}
  \sum_{q\mid r,\ r/q\geq x}\Lambda(q)$.  Subtracting the latter divisor sum
  from the former leaves exactly those divisors $q\mid r$ for which
  $r/q<x$, which is the summand in \cref{def:cut-capacity}. -/)
  (title := /-- Total initial mass equals cut capacity -/)
  (latexEnv := "lemma")]
lemma finite_chain_initial_mass_sum_eq_cut_capacity (x X : ℝ) (hx : 2 ≤ x) :
    (∑' n : ℕ, finite_chain_initial_mass x X n) = cut_capacity x X := by
  classical
  let s : Finset ℕ := Finset.range (⌈X⌉₊ + 1)
  let coeff : ℕ → ℝ := fun r => 1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2)
  let pairTerm : ℕ × ℕ → ℝ := fun p =>
    if x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X then
      if 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) then
        coeff (p.1 * p.2) * ArithmeticFunction.vonMangoldt p.2
      else 0
    else 0
  have hincoming_point (n q : ℕ)
      (hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
      (hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X) :
      erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
          Real.log ((n * q : ℕ) : ℝ) =
        coeff (n * q) * ArithmeticFunction.vonMangoldt q := by
    have hprod_gt_one : (1 : ℝ) < ((n * q : ℕ) : ℝ) := by
      have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := le_trans hx hnint.1
      have hq_ge_two_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqcond.1
      rw [Nat.cast_mul]
      nlinarith
    have hlog_ne : Real.log ((n * q : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos hprod_gt_one).ne'
    rw [erdos_weight]
    dsimp [coeff]
    field_simp [hlog_ne]
  have hleft : (∑' n : ℕ, finite_chain_initial_mass x X n) =
      ∑ n ∈ s, finite_chain_initial_mass x X n := by
    exact tsum_eq_sum (s := s) (fun n hn => by
      rw [finite_chain_initial_mass]
      rw [if_neg]
      intro hnx
      apply hn
      simp only [s, Finset.mem_range]
      have hnleceil : n ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hnx.2 (Nat.le_ceil X))
      omega)
  have hinner (n : ℕ) (hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) :
      (∑' q : ℕ,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0) =
      ∑ q ∈ s,
        if 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X then
          erdos_weight (n * q) * ArithmeticFunction.vonMangoldt q /
            Real.log ((n * q : ℕ) : ℝ)
        else 0 := by
    refine tsum_eq_sum (s := s) ?_
    intro q hq
    rw [if_neg]
    intro hcond
    apply hq
    simp only [s, Finset.mem_range]
    have hn_ge_one : 1 ≤ n := by
      have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := le_trans hx hnint.1
      exact_mod_cast (show (1 : ℝ) ≤ (n : ℝ) by linarith)
    have hq_le_prod : q ≤ n * q := Nat.le_mul_of_pos_left q hn_ge_one
    have hq_le_X : (q : ℝ) ≤ X := by
      have : ((q : ℕ) : ℝ) ≤ ((n * q : ℕ) : ℝ) := by exact_mod_cast hq_le_prod
      exact le_trans this hcond.2
    have hq_le_ceil : q ≤ ⌈X⌉₊ := by
      exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
    omega
  have hleft_expand :
      (∑' n : ℕ, finite_chain_initial_mass x X n) =
        (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
          ∑ p ∈ s.product s, pairTerm p := by
    rw [hleft]
    calc
      (∑ n ∈ s, finite_chain_initial_mass x X n)
          = ∑ n ∈ s,
              ((if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
                ∑ q ∈ s, pairTerm (n, q)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [finite_chain_initial_mass]
            by_cases hnint : x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X
            · rw [if_pos hnint, hinner n hnint]
              simp only [if_pos hnint]
              congr 1
              apply Finset.sum_congr rfl
              intro q hq
              by_cases hqcond : 2 ≤ q ∧ ((n * q : ℕ) : ℝ) ≤ X
              · rw [if_pos hqcond, hincoming_point n q hnint hqcond]
                have hqcond' : 2 ≤ q ∧ (n : ℝ) * (q : ℝ) ≤ X := by
                  exact ⟨hqcond.1, by simpa [Nat.cast_mul] using hqcond.2⟩
                simp [pairTerm, hnint, hqcond, hqcond', Nat.cast_mul]
              · rw [if_neg hqcond]
                have hqcond' : ¬(2 ≤ q ∧ (n : ℝ) * (q : ℝ) ≤ X) := by
                  intro h
                  apply hqcond
                  exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
                simp [pairTerm, hnint, hqcond, hqcond', Nat.cast_mul]
            · rw [if_neg hnint]
              simp [pairTerm, hnint]
      _ = (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
            ∑ n ∈ s, ∑ q ∈ s, pairTerm (n, q) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) -
            ∑ p ∈ s.product s, pairTerm p := by
          simpa using congrArg
            (fun z => (∑ n ∈ s,
              if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) - z)
            (Finset.sum_product (s := s) (t := s)
              (f := fun p : ℕ × ℕ => pairTerm p)).symm
  have hright : cut_capacity x X =
      ∑ r ∈ s,
        if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          coeff r * (∑ q ∈ r.divisors,
            if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
        else 0 := by
    rw [cut_capacity]
    calc
      (∑' r : ℕ,
        if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
            (∑ q ∈ r.divisors,
              if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
        else 0)
          = ∑ r ∈ s,
              if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
                (1 / ((r : ℝ) * (Real.log (r : ℝ)) ^ 2)) *
                  (∑ q ∈ r.divisors,
                    if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
              else 0 := by
            exact tsum_eq_sum (s := s) (fun r hr => by
              rw [if_neg]
              intro hrx
              apply hr
              simp only [s, Finset.mem_range]
              have hrleceil : r ≤ ⌈X⌉₊ := by
                exact_mod_cast (le_trans hrx.2 (Nat.le_ceil X))
              omega)
      _ = ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if (((r / q : ℕ) : ℝ) < x) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
            · simp [coeff, hrint]
            · simp [hrint]
  have hbase_point (r : ℕ) (hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      erdos_weight r = coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) := by
    have hr_gt_one : (1 : ℝ) < (r : ℝ) := by linarith [le_trans hx hr.1]
    have hlog_ne : Real.log (r : ℝ) ≠ 0 := (Real.log_pos hr_gt_one).ne'
    rw [von_mangoldt_divisor_sum, erdos_weight]
    dsimp [coeff]
    field_simp [hlog_ne]
  have hbase_sum :
      (∑ n ∈ s, if x ≤ (n : ℝ) ∧ (n : ℝ) ≤ X then erdos_weight n else 0) =
        ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q)
          else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
    · rw [if_pos hrint, if_pos hrint, hbase_point r hrint]
    · simp [hrint]
  have hpair_fiber (r : ℕ) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)
      (p : ℕ × ℕ) (hp : p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)) :
      pairTerm p =
        if 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ) then coeff r * ArithmeticFunction.vonMangoldt p.2 else 0 := by
    have hprod : p.1 * p.2 = r := (Finset.mem_filter.mp hp).2
    by_cases hcond : 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)
    · have hp2_ge_one : 1 ≤ p.2 := by omega
      have hp1_le_prod : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2_ge_one
      have hp1_le_X : (p.1 : ℝ) ≤ X := by
        have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hp1_le_prod
        rw [hprod] at this
        exact le_trans this hrint.2
      have hprod_le_X : (((p.1 * p.2 : ℕ) : ℝ) ≤ X) := by simpa [hprod] using hrint.2
      have hprod_le_X' : (p.1 : ℝ) * (p.2 : ℝ) ≤ X := by
        simpa [Nat.cast_mul] using hprod_le_X
      have hcond' : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X) := ⟨hcond.1, hprod_le_X⟩
      have hcond'' : 2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X := ⟨hcond.1, hprod_le_X'⟩
      have houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X := ⟨hcond.2, hp1_le_X⟩
      have hprod_coeff : coeff (p.1 * p.2) = coeff r := by rw [hprod]
      simp [pairTerm, houter, hcond', hcond'', hcond, hprod_coeff, Nat.cast_mul]
    · have hnot_outer_or_inner :
          ¬(x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X) ∨
            ¬(2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)) := by
        by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
        · right
          intro hinner
          apply hcond
          exact ⟨hinner.1, houter.1⟩
        · exact Or.inl houter
      rcases hnot_outer_or_inner with houter | hinner
      · simp [pairTerm, houter, hcond]
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, hinner, hinner', hcond, Nat.cast_mul]
  have hbij_sum (r : ℕ) (hrmem : r ∈ s) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      (∑ p ∈ ((s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)).filter
          (fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)),
          coeff r * ArithmeticFunction.vonMangoldt p.2) =
        ∑ q ∈ r.divisors.filter (fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ)),
          coeff r * ArithmeticFunction.vonMangoldt q := by
    refine Finset.sum_bij' (fun p hp => p.2) (fun q hq => (r / q, q)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpfiber, hpcond⟩
      have hprod : p.1 * p.2 = r := hpfiber.2
      have hr_ne : r ≠ 0 := by
        have : (0 : ℝ) < (r : ℝ) := by linarith [hx, hrint.1]
        exact_mod_cast this.ne'
      have hp2pos : 0 < p.2 := by omega
      have hp2dvd : p.2 ∣ r := by
        refine ⟨p.1, ?_⟩
        rw [mul_comm, hprod]
      have hp1_eq : p.1 = r / p.2 := by
        rw [← hprod]
        simp [hp2pos]
      constructor
      · exact Nat.mem_divisors.mpr ⟨hp2dvd, hr_ne⟩
      · constructor
        · exact hpcond.1
        · simpa [← hp1_eq] using hpcond.2
    · intro q hq
      simp only [Finset.mem_filter] at hq ⊢
      rcases hq with ⟨hqdivmem, hqcond⟩
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp hqdivmem).1
      have hr_ne : r ≠ 0 := (Nat.mem_divisors.mp hqdivmem).2
      have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
      have hqle : q ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr_ne) hqdiv
      have hdivle : r / q ≤ r := Nat.div_le_self r q
      have hr_lt : r < ⌈X⌉₊ + 1 := by simpa [s, Finset.mem_range] using hrmem
      have hqmems : q ∈ s := by simp only [s, Finset.mem_range]; omega
      have hdivmems : r / q ∈ s := by simp only [s, Finset.mem_range]; omega
      constructor
      · constructor
        · exact Finset.mem_product.mpr ⟨hdivmems, hqmems⟩
        · exact hprod
      · exact hqcond
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rcases hp with ⟨hpfiber, hpcond⟩
      have hprod : p.1 * p.2 = r := hpfiber.2
      have hp2pos : 0 < p.2 := by omega
      have hp1_eq : r / p.2 = p.1 := by rw [← hprod]; simp [hp2pos]
      ext
      · exact hp1_eq
      · rfl
    · intro q hq
      rfl
    · intro p hp
      rfl
  have hfiber_high (r : ℕ) (hrmem : r ∈ s) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p) =
        coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) := by
    calc
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p)
          = ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r),
              if 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ) then coeff r * ArithmeticFunction.vonMangoldt p.2 else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hpair_fiber r hrint p hp
      _ = ∑ p ∈ ((s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r)).filter
              (fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ)),
              coeff r * ArithmeticFunction.vonMangoldt p.2 := by
            exact (Finset.sum_filter (s := (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r))
              (p := fun p : ℕ × ℕ => 2 ≤ p.2 ∧ x ≤ (p.1 : ℝ))
              (f := fun p : ℕ × ℕ => coeff r * ArithmeticFunction.vonMangoldt p.2)).symm
      _ = ∑ q ∈ r.divisors.filter (fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ)),
              coeff r * ArithmeticFunction.vonMangoldt q := hbij_sum r hrmem hrint
      _ = coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) := by
            rw [Finset.mul_sum]
            simpa [mul_ite] using
              (Finset.sum_filter (s := r.divisors)
                (p := fun q : ℕ => 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ))
                (f := fun q : ℕ => coeff r * ArithmeticFunction.vonMangoldt q))
  have hfiber_zero (r : ℕ) (hrnot : ¬(x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)) :
      (∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r), pairTerm p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hprod : p.1 * p.2 = r := (Finset.mem_filter.mp hp).2
    by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
    · by_cases hinner : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
      · have hp2_ge_one : 1 ≤ p.2 := by omega
        have hp1_le_prod : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2_ge_one
        have hxle_r : x ≤ (r : ℝ) := by
          have : (p.1 : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast hp1_le_prod
          rw [hprod] at this
          exact le_trans houter.1 this
        have hrleX : (r : ℝ) ≤ X := by simpa [hprod] using hinner.2
        exact False.elim (hrnot ⟨hxle_r, hrleX⟩)
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, houter, hinner, hinner', Nat.cast_mul]
    · simp [pairTerm, houter]
  have hpair_zero_notmem (p : ℕ × ℕ) (hp : p ∈ s.product s)
      (hprodmem : ¬ p.1 * p.2 ∈ s) : pairTerm p = 0 := by
    by_cases houter : x ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X
    · by_cases hinner : 2 ≤ p.2 ∧ (((p.1 * p.2 : ℕ) : ℝ) ≤ X)
      · apply False.elim
        apply hprodmem
        simp only [s, Finset.mem_range]
        have hleceil : p.1 * p.2 ≤ ⌈X⌉₊ := by
          exact_mod_cast (le_trans hinner.2 (Nat.le_ceil X))
        omega
      · have hinner' : ¬(2 ≤ p.2 ∧ (p.1 : ℝ) * (p.2 : ℝ) ≤ X) := by
          intro h
          apply hinner
          exact ⟨h.1, by simpa [Nat.cast_mul] using h.2⟩
        simp [pairTerm, houter, hinner, hinner', Nat.cast_mul]
    · simp [pairTerm, houter]
  have hpair_sum :
      (∑ p ∈ s.product s, pairTerm p) =
        ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
    calc
      (∑ p ∈ s.product s, pairTerm p)
          = ∑ p ∈ s.product s, if p.1 * p.2 ∈ s then pairTerm p else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hprodmem : p.1 * p.2 ∈ s
            · simp [hprodmem]
            · rw [if_neg hprodmem, hpair_zero_notmem p hp hprodmem]
      _ = ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 ∈ s), pairTerm p := by
            exact (Finset.sum_filter (s := s.product s)
              (p := fun p : ℕ × ℕ => p.1 * p.2 ∈ s) (f := pairTerm)).symm
      _ = ∑ r ∈ s, ∑ p ∈ (s.product s).filter (fun p : ℕ × ℕ => p.1 * p.2 = r),
              pairTerm p := by
            exact (Finset.sum_fiberwise_eq_sum_filter (s.product s) s
              (fun p : ℕ × ℕ => p.1 * p.2) pairTerm).symm
      _ = ∑ r ∈ s,
          if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
            coeff r * (∑ q ∈ r.divisors,
              if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hrmem
            by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
            · rw [if_pos hrint, hfiber_high r hrmem hrint]
            · rw [if_neg hrint, hfiber_zero r hrint]
  have hfinal_point (r : ℕ) (hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X) :
      coeff r * (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) -
        coeff r * (∑ q ∈ r.divisors,
          if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) =
        coeff r * (∑ q ∈ r.divisors,
          if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) := by
    have hdiv_split :
        (∑ q ∈ r.divisors, ArithmeticFunction.vonMangoldt q) -
          (∑ q ∈ r.divisors,
            if 2 ≤ q ∧ x ≤ ((r / q : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt q else 0) =
          ∑ q ∈ r.divisors,
            if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hlt : ((r / q : ℕ) : ℝ) < x
      · have hnle : ¬ x ≤ ((r / q : ℕ) : ℝ) := not_le_of_gt hlt
        simp [hlt, hnle]
      · have hge : x ≤ ((r / q : ℕ) : ℝ) := le_of_not_gt hlt
        by_cases hq2 : 2 ≤ q
        · simp [hlt, hge, hq2]
        · have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
          have hqeq : q = 1 := by omega
          simp [hlt, hge, hq2, hqeq]
    rw [← mul_sub, hdiv_split]
  rw [hleft_expand, hright, hbase_sum, hpair_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hrmem
  by_cases hrint : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
  · rw [if_pos hrint, if_pos hrint, if_pos hrint]
    exact hfinal_point r hrint
  · rw [if_neg hrint, if_neg hrint, if_neg hrint]
    ring

@[blueprint "lem:finite-chain-cut-bound"
  (statement := /-- Let $x,X\in\mathbb{R}$ with $2\leq x$, and let
  $A\subseteq\mathbb{N}$ be a primitive set supported in $[x,X]$. Then $f(A)$
  is at most the finite von Mangoldt cut capacity associated with $x$ and
  $X$. -/)
  (proof := /-- Apply \cref{lem:finite-chain-erdos-le-initial-mass} to the
  primitive set $A$ and the support interval $[x,X]$.  This bounds $f(A)$ by the
  total initial mass of the finite von Mangoldt chain.  The exact finite
  reindexing identity \cref{lem:finite-chain-initial-mass-sum-eq-cut-capacity}
  then identifies that total initial mass with \cref{def:cut-capacity}, giving
  the asserted inequality. -/)
  (title := /-- Finite chain cut bound -/)
  (latexEnv := "lemma")]
lemma finite_chain_cut_bound (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ cut_capacity x X := by
  calc
    erdos_sum A ≤ ∑' n : ℕ, finite_chain_initial_mass x X n :=
      finite_chain_erdos_le_initial_mass A x X hx hprim hsupp
    _ = cut_capacity x X :=
      finite_chain_initial_mass_sum_eq_cut_capacity x X hx

@[blueprint "lem:cut-capacity-le-tail-majorant"
  (statement := /-- For every $x\geq 2$ and every real $X$, the finite cut
  capacity is bounded above by the reindexed tail majorant depending only on
  $x$. -/)
  (proof := /-- It suffices to bound each finite partial sum in
  \cref{def:cut-capacity}.  For every contributing divisor $q\mid r$, put
  $n=r/q$. Then $n<x$, and the condition $r\geq x$ gives $q\geq x/n$; together
  with the non-triviality forced by $r\geq x>n$, this gives
  $q\geq\max\{2,x/n\}$.  The summand is therefore the corresponding
  $n^{-1}$ multiple of the tail term from \cref{def:mangoldt-tail-term}.  Thus
  the finite partial sum embeds into a finite sum over pairs $(n,q)$ with
  $1\leq n<x$.  For each such $n$,
  \cref{lem:mangoldt-tail-finite-sum-le} bounds the finite $q$-sum by the full
  tail in \cref{def:mangoldt-tail-sum}.  Summing over the finitely many
  admissible $n$ gives the corresponding finite form of
  \cref{def:tail-majorant}, and hence the desired t-sum inequality. -/)
  (title := /-- Reindexing the cut capacity -/)
  (latexEnv := "lemma")]
lemma cut_capacity_le_tail_majorant (x X : ℝ) (hx : 2 ≤ x) :
    cut_capacity x X ≤ tail_majorant x := by
  rw [cut_capacity]
  apply tsum_le_of_sum_le'
  · rw [tail_majorant]
    apply tsum_nonneg
    intro n
    split_ifs with hn
    · apply mul_nonneg
      · positivity
      · rw [mangoldt_tail_sum]
        apply tsum_nonneg
        intro q
        split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
    · norm_num
  · intro s
    let M : ℕ := ⌈X⌉₊ + 1
    let ns : Finset ℕ := (Finset.range ⌈x⌉₊).filter (fun n => 1 ≤ n ∧ (n : ℝ) < x)
    let qs : Finset ℕ := Finset.range M
    let pairs : Finset (ℕ × ℕ) := ns.product qs
    let pairTerm : ℕ × ℕ → ℝ := fun p =>
      (1 / (p.1 : ℝ)) *
        (if max (2 : ℝ) (x / (p.1 : ℝ)) ≤ (p.2 : ℝ) then
          mangoldt_tail_term p.1 p.2 else 0)
    have hpair_nonneg : ∀ p, 0 ≤ pairTerm p := by
      intro p
      simp only [pairTerm]
      apply mul_nonneg
      · positivity
      · split_ifs
        · rw [mangoldt_tail_term]
          exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · norm_num
    have hD_sum (r : ℕ) :
        (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
            (∑ q ∈ r.divisors,
              if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) =
          ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
            (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
              ArithmeticFunction.vonMangoldt q := by
      rw [Finset.mul_sum]
      simpa [mul_ite] using
        (Finset.sum_filter (s := r.divisors)
          (p := fun q : ℕ => ((r / q : ℕ) : ℝ) < x)
          (f := fun q : ℕ =>
            (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
              ArithmeticFunction.vonMangoldt q)).symm
    have hterm (r q : ℕ) (hrx : x ≤ (r : ℝ))
        (hq : q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)) :
        (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
            ArithmeticFunction.vonMangoldt q = pairTerm (r / q, q) := by
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
      have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
      have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
      have hcast : (((r / q) * q : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hprod
      have hnlt : ((r / q : ℕ) : ℝ) < x := (Finset.mem_filter.mp hq).2
      have hrpos : 0 < r := by
        have : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast this
      have hqle : q ≤ r := Nat.le_of_dvd hrpos hqdiv
      have hnpos : 0 < r / q := Nat.div_pos hqle hqpos
      have hqtwo : (2 : ℝ) ≤ (q : ℝ) := by
        by_contra hnot
        have hq_lt_two : q < 2 := by exact_mod_cast lt_of_not_ge hnot
        have hq_le_one : q ≤ 1 := Nat.lt_succ_iff.mp hq_lt_two
        have hq_eq_one : q = 1 := Nat.le_antisymm hq_le_one hqpos
        have hr_eq : r / q = r := by simp [hq_eq_one]
        rw [hr_eq] at hnlt
        linarith
      have hxdiv : x / ((r / q : ℕ) : ℝ) ≤ (q : ℝ) := by
        have hnpos_real : 0 < ((r / q : ℕ) : ℝ) := by exact_mod_cast hnpos
        rw [div_le_iff₀ hnpos_real]
        calc
          x ≤ (r : ℝ) := hrx
          _ = (q : ℝ) * ((r / q : ℕ) : ℝ) := by
            rw [← hcast]
            simp [Nat.cast_mul, mul_comm]
      have hthresh : max (2 : ℝ) (x / ((r / q : ℕ) : ℝ)) ≤ (q : ℝ) :=
        max_le hqtwo hxdiv
      simp only [pairTerm]
      rw [if_pos hthresh, mangoldt_tail_term]
      rw [← hcast]
      simp only [Nat.cast_mul]
      ring_nf
    have hmem_pair (r q : ℕ) (hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X)
        (hq : q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)) :
        (r / q, q) ∈ pairs := by
      have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
      have hqpos : 0 < q := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hq).1
      have hnlt : ((r / q : ℕ) : ℝ) < x := (Finset.mem_filter.mp hq).2
      have hrpos : 0 < r := by
        have : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast this
      have hqle : q ≤ r := Nat.le_of_dvd hrpos hqdiv
      have hnpos : 0 < r / q := Nat.div_pos hqle hqpos
      have hnone : 1 ≤ r / q := Nat.succ_le_of_lt hnpos
      have hnltceil : r / q < ⌈x⌉₊ := by
        exact_mod_cast (lt_of_lt_of_le hnlt (Nat.le_ceil x))
      have hq_le_X : (q : ℝ) ≤ X := by
        have hqr : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hqle
        linarith
      have hq_le_ceil : q ≤ ⌈X⌉₊ := by
        exact_mod_cast (le_trans hq_le_X (Nat.le_ceil X))
      have hq_lt_M : q < M := by
        dsimp [M]
        omega
      simp [pairs, ns, qs, hnltceil, hnone, hnlt, hq_lt_M]
    have hper (r : ℕ) :
        (if x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X then
          1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) *
            ∑ q ∈ r.divisors,
              if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
        else 0) ≤
          ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p := by
      by_cases hr : x ≤ (r : ℝ) ∧ (r : ℝ) ≤ X
      · rw [if_pos hr]
        calc
          1 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) *
              (∑ q ∈ r.divisors,
                if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0)
              = (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
                  (∑ q ∈ r.divisors,
                    if ((r / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0) := by
                ring_nf
          _ = ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
                (Real.log (r : ℝ) ^ 2)⁻¹ * (r : ℝ)⁻¹ *
                  ArithmeticFunction.vonMangoldt q := hD_sum r
          _ = ∑ q ∈ r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x),
                pairTerm (r / q, q) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact hterm r q hr.1 hq
          _ = ∑ p ∈ (r.divisors.filter (fun q => ((r / q : ℕ) : ℝ) < x)).image
                (fun q => (r / q, q)), pairTerm p := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Prod.ext_iff.mp hab |>.2
          _ ≤ ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = r), pairTerm p := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp
                rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
                have hqdiv : q ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
                have hprod : (r / q) * q = r := Nat.div_mul_cancel hqdiv
                simp [hmem_pair r q hr hq, hprod]
              · intro p _ _
                exact hpair_nonneg p
      · rw [if_neg hr]
        exact Finset.sum_nonneg (fun p _ => hpair_nonneg p)
    have hsum_le :
        (∑ i ∈ s,
          if x ≤ (i : ℝ) ∧ (i : ℝ) ≤ X then
            1 / ((i : ℝ) * Real.log (i : ℝ) ^ 2) *
              ∑ q ∈ i.divisors,
                if ((i / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
          else 0) ≤ ∑ p ∈ pairs, pairTerm p := by
      calc
        (∑ i ∈ s,
          if x ≤ (i : ℝ) ∧ (i : ℝ) ≤ X then
            1 / ((i : ℝ) * Real.log (i : ℝ) ^ 2) *
              ∑ q ∈ i.divisors,
                if ((i / q : ℕ) : ℝ) < x then ArithmeticFunction.vonMangoldt q else 0
          else 0)
            ≤ ∑ i ∈ s, ∑ p ∈ pairs.filter (fun p => p.1 * p.2 = i), pairTerm p := by
              apply Finset.sum_le_sum
              intro i _
              exact hper i
        _ = ∑ p ∈ pairs.filter (fun p => p.1 * p.2 ∈ s), pairTerm p := by
          exact Finset.sum_fiberwise_eq_sum_filter pairs s
            (fun p : ℕ × ℕ => p.1 * p.2) pairTerm
        _ ≤ ∑ p ∈ pairs, pairTerm p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            exact (Finset.mem_filter.mp hp).1
          · intro p _ _
            exact hpair_nonneg p
    have htail_eq : tail_majorant x =
        ∑ n ∈ ns,
          if 1 ≤ n ∧ (n : ℝ) < x then
            (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
          else 0 := by
      rw [tail_majorant]
      exact tsum_eq_sum (s := ns) (fun n hn => by
        split_ifs with h
        · exfalso
          apply hn
          simp [ns]
          constructor
          · have hltceil : n < ⌈x⌉₊ := by
              exact_mod_cast (lt_of_lt_of_le h.2 (Nat.le_ceil x))
            simpa using hltceil
          · exact h
        · rfl)
    have hfinite_tail_le : (∑ p ∈ pairs, pairTerm p) ≤ tail_majorant x := by
      rw [htail_eq]
      change (∑ p ∈ ns ×ˢ qs, pairTerm p) ≤
        ∑ n ∈ ns,
          if 1 ≤ n ∧ (n : ℝ) < x then
            (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
          else 0
      rw [Finset.sum_product]
      apply Finset.sum_le_sum
      intro n hn
      have hnmem : n < ⌈x⌉₊ ∧ 1 ≤ n ∧ (n : ℝ) < x := by simpa [ns] using hn
      have hnprop : 1 ≤ n ∧ (n : ℝ) < x := hnmem.2
      rw [if_pos hnprop]
      simp only [pairTerm]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mangoldt_tail_finite_sum_le n hnprop.1 (max (2 : ℝ) (x / (n : ℝ)))
          (le_max_left _ _) qs) (by positivity)
    exact hsum_le.trans hfinite_tail_le

@[blueprint "lem:tail-majorant-bound"
  (statement := /-- There is a real constant $C\geq 0$ such that, for every
  real number $x\geq 2$, the reindexed tail majorant is at most
  $1+C/\log x$. -/)
  (proof := /-- Let $D\geq 0$ be the constant supplied by
  \cref{lem:mangoldt-tail-upper-bound}, set $K=1+\log 2$, and fix a real
  number $x\geq 2$ with $L=\log x$. By \cref{def:tail-majorant}, only the
  integers $1\leq n<x$ contribute.  For such an $n$, put
  $y=\max(2,x/n)$. Then $y\geq 2$ and $ny\geq x$, so
  \cref{lem:mangoldt-tail-upper-bound} gives
  $\sum_{q\geq y}\Lambda(q)/(q\log^2(nq))\leq L^{-1}+D L^{-2}$. Hence the
  majorant is at most $(L^{-1}+D L^{-2})\sum_{1\leq n\leq \lceil x\rceil}1/n$.
  Since $\lceil x\rceil\leq 2x$, the harmonic estimate
  $\sum_{1\leq n\leq \lceil x\rceil}1/n\leq L+K$ applies. Therefore the
  majorant is at most
  $1+(K+D)/L+KD/L^2$.  As $L\geq \log 2$, the final term is at most
  $(KD/\log 2)/L$. Taking $C=K+D+KD/\log 2$ proves the asserted bound. -/)
  (title := /-- Bounding the reindexed tail majorant -/)
  (latexEnv := "lemma")]
lemma tail_majorant_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x -> tail_majorant x ≤ 1 + C / Real.log x := by
  classical
  obtain ⟨D, hD_nonneg, hD_bound⟩ := mangoldt_tail_upper_bound
  let K : ℝ := 1 + Real.log (2 : ℝ)
  let C : ℝ := K + D + K * D / Real.log (2 : ℝ)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx
  let N : ℕ := ⌈x⌉₊
  let L : ℝ := Real.log x
  let A : ℝ := 1 / L + D / L ^ 2
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hlog2_le_L : Real.log (2 : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hx
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfinite : tail_majorant x =
      ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0 := by
    unfold tail_majorant
    dsimp [N]
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ)
      (s := Finset.range ⌈x⌉₊)
      (f := fun n : ℕ =>
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0) ?_
    intro n hn
    have hn_not_lt_x : ¬ (n : ℝ) < x := by
      intro hnx
      have hn_lt_ceil : n < ⌈x⌉₊ := by
        by_contra hnot
        have hceil_le_n : ⌈x⌉₊ ≤ n := le_of_not_gt hnot
        have hx_le_n : x ≤ (n : ℝ) := by
          exact (Nat.le_ceil x).trans (Nat.cast_le.mpr hceil_le_n)
        exact (not_lt_of_ge hx_le_n) hnx
      exact hn (Finset.mem_range.mpr hn_lt_ceil)
    simp [hn_not_lt_x]
  have hterm_le : ∀ n : ℕ,
      (if 1 ≤ n ∧ (n : ℝ) < x then
        (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
      else 0) ≤
      (if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) := by
    intro n
    by_cases hn : 1 ≤ n ∧ (n : ℝ) < x
    · have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn.1
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      let y : ℝ := max (2 : ℝ) (x / (n : ℝ))
      have hy : 2 ≤ y := by
        dsimp [y]
        exact le_max_left _ _
      have hxy : x ≤ (n : ℝ) * y := by
        have hdiv_le : x / (n : ℝ) ≤ y := by
          dsimp [y]
          exact le_max_right _ _
        calc
          x = (n : ℝ) * (x / (n : ℝ)) := by
            field_simp [hn_pos.ne']
          _ ≤ (n : ℝ) * y := mul_le_mul_of_nonneg_left hdiv_le (le_of_lt hn_pos)
      have hlog_ge : L ≤ Real.log ((n : ℝ) * y) := by
        dsimp [L]
        exact Real.log_le_log hx_pos hxy
      have hlog_pos : 0 < Real.log ((n : ℝ) * y) := hL_pos.trans_le hlog_ge
      have htail := (hD_bound n hn.1 y hy).2
      have hone : 1 / Real.log ((n : ℝ) * y) ≤ 1 / L := by
        exact one_div_le_one_div_of_le hL_pos hlog_ge
      have hsquare : D / (Real.log ((n : ℝ) * y)) ^ 2 ≤ D / L ^ 2 := by
        have hsquares : L ^ 2 ≤ (Real.log ((n : ℝ) * y)) ^ 2 := by
          nlinarith [hlog_ge, le_of_lt hL_pos, le_of_lt hlog_pos]
        exact div_le_div_of_nonneg_left hD_nonneg (sq_pos_of_pos hL_pos) hsquares
      have htail_A : mangoldt_tail_sum n y ≤ A := by
        calc
          mangoldt_tail_sum n y ≤
              1 / Real.log ((n : ℝ) * y) + D / (Real.log ((n : ℝ) * y)) ^ 2 := htail
          _ ≤ 1 / L + D / L ^ 2 := add_le_add hone hsquare
          _ = A := by rfl
      have hmul := mul_le_mul_of_nonneg_left htail_A (by positivity : 0 ≤ 1 / (n : ℝ))
      simpa [hn, y, A] using hmul
    · simp [hn]
  have hsum_A :
      (∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) ≤
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := by
    calc
      (∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0) =
          ∑ n ∈ (Finset.range N).filter (fun n : ℕ => 1 ≤ n ∧ (n : ℝ) < x),
            (1 / (n : ℝ)) * A := by
            rw [Finset.sum_filter]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          exact Finset.mem_Icc.mpr ⟨hn.2.1, Nat.le_of_lt hn.1⟩
        · intro n hnI hnnot
          positivity
  have hrecip_eq_harm :
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) = (harmonic N : ℝ) := by
    simpa [one_div, harmonic_eq_sum_Icc]
  have htail_le_HA : tail_majorant x ≤ (harmonic N : ℝ) * A := by
    calc
      tail_majorant x = ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then
          (1 / (n : ℝ)) * mangoldt_tail_sum n (max (2 : ℝ) (x / (n : ℝ)))
        else 0 := hfinite
      _ ≤ ∑ n ∈ Finset.range N,
        if 1 ≤ n ∧ (n : ℝ) < x then (1 / (n : ℝ)) * A else 0 := by
          exact Finset.sum_le_sum (by intro n hn; exact hterm_le n)
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * A := hsum_A
      _ = (harmonic N : ℝ) * A := by
        rw [← Finset.sum_mul, hrecip_eq_harm]
  have hN_lt_add_one : (N : ℝ) < x + 1 := by
    dsimp [N]
    exact Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  have hN_le_two_x : (N : ℝ) ≤ 2 * x := by
    nlinarith [hN_lt_add_one, hx]
  have hN_pos : 0 < (N : ℝ) := by
    have hx_le_N : x ≤ (N : ℝ) := by
      dsimp [N]
      exact Nat.le_ceil x
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log (2 : ℝ) + L := by
    have hlog_le := Real.log_le_log hN_pos hN_le_two_x
    have hlog_mul : Real.log (2 * x) = Real.log (2 : ℝ) + Real.log x := by
      rw [Real.log_mul] <;> positivity
    simpa [L, hlog_mul] using hlog_le
  have hH_le : (harmonic N : ℝ) ≤ L + K := by
    have hh := harmonic_le_one_add_log N
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := hh
      _ ≤ 1 + (Real.log (2 : ℝ) + L) := by linarith
      _ = L + K := by
        dsimp [K]
        ring
  have htail_le_main : tail_majorant x ≤ (L + K) * A :=
    le_trans htail_le_HA (mul_le_mul_of_nonneg_right hH_le hA_nonneg)
  have halg : (L + K) * A ≤ 1 + C / L := by
    have hKD_nonneg : 0 ≤ K * D := by positivity
    have hKD_div : K * D / L ≤ K * D / Real.log (2 : ℝ) := by
      exact div_le_div_of_nonneg_left hKD_nonneg hlog2_pos hlog2_le_L
    have hKD_sq : K * D / L ^ 2 ≤ (K * D / Real.log (2 : ℝ)) / L := by
      calc
        K * D / L ^ 2 = (K * D / L) / L := by
          field_simp [hL_pos.ne']
        _ ≤ (K * D / Real.log (2 : ℝ)) / L :=
          div_le_div_of_nonneg_right hKD_div (le_of_lt hL_pos)
    have hdecomp : (L + K) * A = 1 + (K + D) / L + K * D / L ^ 2 := by
      dsimp [A]
      field_simp [hL_pos.ne']
      ring
    have htarget : 1 + (K + D) / L + K * D / L ^ 2 ≤
        1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L := by
      linarith
    have hcombine : 1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L =
        1 + C / L := by
      dsimp [C]
      field_simp [hL_pos.ne']
      ring
    calc
      (L + K) * A = 1 + (K + D) / L + K * D / L ^ 2 := hdecomp
      _ ≤ 1 + (K + D) / L + (K * D / Real.log (2 : ℝ)) / L := htarget
      _ = 1 + C / L := hcombine
  exact le_trans htail_le_main halg

@[blueprint "lem:finite-large-primitive-bound"
  (statement := /-- There exists a real constant $C\geq 0$ such that, for all
  real numbers $x$ and $X$ with $2\leq x\leq X$, every primitive set
  $A\subseteq\mathbb{N}$ supported in $[x,X]$ has Erd\H{o}s sum at most
  $1+C/\log x$. -/)
  (proof := /-- Choose the nonnegative constant supplied by
  \cref{lem:tail-majorant-bound}.  To prove \cref{def:erdos1196-finite-bound},
  fix real numbers $x$ and $X$ with $2\leq x\leq X$ and a primitive set
  $A\subseteq\mathbb{N}$ supported in $[x,X]$.  By
  \cref{lem:finite-chain-cut-bound}, the Erd\H{o}s sum of $A$ is at most
  \cref{def:cut-capacity}.  The latter is at most \cref{def:tail-majorant} by
  \cref{lem:cut-capacity-le-tail-majorant}, and this is at most
  $1+C/\log x$ by \cref{lem:tail-majorant-bound}. -/)
  (title := /-- Finite large primitive-set bound -/)
  (latexEnv := "lemma")]
lemma finite_large_primitive_bound :
    ∃ C : ℝ, erdos1196_finite_bound C := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ := tail_majorant_bound
  refine ⟨C, hC_nonneg, ?_⟩
  intro x X hx _ A hprim hsupp
  calc
    erdos_sum A ≤ cut_capacity x X := finite_chain_cut_bound A x X hx hprim hsupp
    _ ≤ tail_majorant x := cut_capacity_le_tail_majorant x X hx
    _ ≤ 1 + C / Real.log x := hC_bound x hx

@[blueprint "lem:finite-truncation-principle"
  (statement := /-- If there exists a nonnegative real constant $C_0$ such that,
  for every pair of real numbers $x,X$ with $2\leq x\leq X$ and every primitive
  set $A\subseteq\mathbb N$ supported in $[x,X]$, one has
  $f(A)\leq 1+C_0/\log x$, then there exists a nonnegative real constant $C_1$
  such that, for every real number $x\geq 2$ and every primitive set
  $A\subseteq\mathbb N$ supported in $[x,\infty)$, the series defining $f(A)$ is
  summable and $f(A)\leq 1+C_1/\log x$. -/)
  (proof := /-- Unpack \cref{def:erdos1196-finite-bound}.  Fix $x\geq 2$ and
  a primitive set $A$ supported above $x$.  For each natural number $N$, put
  $B=A\cap \{0,\ldots,N-1\}$.  By \cref{def:primitive-set}, $B$ is primitive,
  and by \cref{def:supported-above,def:supported-in-interval} it is supported
  in $[x,\max\{x,N\}]$.  The finite hypothesis therefore bounds
  $f(B)$ by $1+C/\log x$.  By \cref{def:erdos-sum,def:erdos-weight}, this is
  exactly the $N$th finite partial sum of the nonnegative series defining
  $f(A)$.  Since all partial sums of this nonnegative real series are bounded by
  $1+C/\log x$, the standard bounded-partial-sums theorem for nonnegative real
  series gives summability of the series and bounds its sum by
  $1+C/\log x$.  Together with the same nonnegative constant $C$, this is
  precisely \cref{def:erdos1196-bound}. -/)
  (title := /-- Removing the finite truncation -/)
  (latexEnv := "lemma")]
lemma finite_truncation_principle :
    (∃ C : ℝ, erdos1196_finite_bound C) -> ∃ C : ℝ, erdos1196_bound C := by
  rintro ⟨C, hC⟩
  rw [erdos1196_finite_bound] at hC
  rcases hC with ⟨hC_nonneg, hfinite⟩
  refine ⟨C, ?_⟩
  rw [erdos1196_bound]
  refine ⟨hC_nonneg, ?_⟩
  intro x hx A hprim hsupp
  have hnonneg : ∀ n : ℕ, 0 ≤ A.indicator erdos_weight n := by
    intro n
    by_cases hnA : n ∈ A
    · rw [Set.indicator_of_mem hnA]
      rw [erdos_weight]
      have hn_two : (2 : ℝ) ≤ (n : ℝ) := le_trans hx (hsupp n hnA)
      have hn_one : (1 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hn_two
      exact div_nonneg zero_le_one
        (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hn_one))
    · rw [Set.indicator_of_notMem hnA]
  have hpartial_bound : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, A.indicator erdos_weight i) ≤
        1 + C / Real.log x := by
    intro N
    let B : Set ℕ := A ∩ {n : ℕ | n < N}
    have hprimB : primitive_set B := by
      rw [primitive_set] at hprim ⊢
      exact hprim.subset (by intro n hn; exact hn.1)
    have hsuppB : supported_in_interval B x (max x (N : ℝ)) := by
      intro n hn
      refine ⟨hsupp n hn.1, ?_⟩
      exact le_trans (by exact_mod_cast Nat.le_of_lt hn.2) (le_max_right x (N : ℝ))
    have htsumB : erdos_sum B = ∑ i ∈ Finset.range N, B.indicator erdos_weight i := by
      rw [erdos_sum]
      exact tsum_eq_sum (s := Finset.range N) (fun n hn => by
        have hnB : n ∉ B := by
          intro h
          exact hn (Finset.mem_range.mpr h.2)
        simp [Set.indicator_of_notMem hnB])
    have hsum_eq :
        (∑ i ∈ Finset.range N, A.indicator erdos_weight i) = erdos_sum B := by
      rw [htsumB]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_lt : i < N := Finset.mem_range.mp hi
      by_cases hiA : i ∈ A
      · have hiB : i ∈ B := ⟨hiA, hi_lt⟩
        simp [Set.indicator_of_mem hiA, Set.indicator_of_mem hiB]
      · have hiB : i ∉ B := by
          intro h
          exact hiA h.1
        simp [Set.indicator_of_notMem hiA, Set.indicator_of_notMem hiB]
    calc
      (∑ i ∈ Finset.range N, A.indicator erdos_weight i) = erdos_sum B := hsum_eq
      _ ≤ 1 + C / Real.log x :=
          hfinite x (max x (N : ℝ)) hx (le_max_left x (N : ℝ)) B hprimB hsuppB
  have hsumm : Summable (fun n : ℕ => A.indicator erdos_weight n) :=
    summable_of_sum_range_le hnonneg hpartial_bound
  refine ⟨hsumm, ?_⟩
  simpa [erdos_sum] using hsumm.tsum_le_of_sum_range_le hpartial_bound

@[blueprint "thm:erdos-sarkozy-szemeredi-1196"
  (statement := /-- There exists a nonnegative real constant $C$ such that, for
  every real number $x$ with $2\leq x$ and every primitive set
  $A\subseteq\mathbb{N}$ contained in $[x,\infty)$, the series defining the
  Erd\H{o}s sum of $A$ is summable and satisfies $f(A)\leq 1+C/\log x$. -/)
  (proof := /-- The finite theorem \cref{lem:finite-large-primitive-bound}
  supplies an absolute constant for all primitive sets supported in finite
  intervals $[x,X]$. Applying the limiting principle
  \cref{lem:finite-truncation-principle} removes the upper endpoint and gives
  both summability and the stated bound for all primitive sets contained in
  $[x,\infty)$. -/)
  (title := /-- Erd\H{o}s--S\'ark\"ozy--Szemer\'edi problem \#1196 -/)
  (latexEnv := "theorem")]
theorem erdos_sarkozy_szemeredi_1196 :
    ∃ C : ℝ, erdos1196_bound C := by
  exact finite_truncation_principle finite_large_primitive_bound

@[blueprint "def:prime-layer"
  (statement := /-- The first divisibility layer $\mathbb N_1$ is the set of
  prime natural numbers. -/)
  (title := /-- The prime layer -/)
  (latexEnv := "definition")]
def prime_layer : Set ℕ :=
  {n : ℕ | Nat.Prime n}

@[blueprint "def:eps-modified-chain-subinvariant-package"
  (statement := /-- This package records the formal interface supplied by the
  modified von Mangoldt downward chain used in the proof of the
  Erd\H{o}s primitive set conjecture.  It consists of transition weights
  $P(n,m)$ on $\mathbb N$, non-negative and of total mass one from every
  starting state; every prime is absorbing; and the Erd\H{o}s weight is
  sub-invariant for the transition kernel, namely
  $\sum_n \nu_0(n)P(n,m)\leq \nu_0(m)$ for all $m\geq2$. -/)
  (title := /-- Modified-chain sub-invariance package -/)
  (latexEnv := "definition")]
def eps_modified_chain_subinvariant_package : Prop :=
  ∃ P : ℕ → ℕ → ℝ,
    (∀ n m : ℕ, 0 ≤ P n m) ∧
    (∀ n : ℕ, (∑' m : ℕ, P n m) = 1) ∧
    (∀ p : ℕ, p ∈ prime_layer -> P p p = 1) ∧
    (∀ m : ℕ, 2 ≤ m -> (∑' n : ℕ, erdos_weight n * P n m) ≤ erdos_weight m)

@[blueprint "lem:eps-modified-chain-subinvariant"
  (statement := /-- The modified von Mangoldt downward chain with absorbing
  states the primes satisfies the sub-invariance package of
  \cref{def:eps-modified-chain-subinvariant-package}. -/)
  (proof := /-- Define the transition kernel exactly as in the source proof:
  away from prime powers it is the von Mangoldt downward chain, primes are
  absorbing, and for $p^k$ with $k\geq2$ the mass that would jump from $p^k$ to
  $1$ is redirected to the transition from $p^k$ to $p$.  The Markov property
  follows from $\sum_{q\mid n}\Lambda(q)=\log n$ and the identity
  $(k-2)/k+2/k=1$.  For the sub-invariance inequality, the ordinary von
  Mangoldt contribution is bounded by \cref{lem:mangoldt-subinvariant-bound}.
  If the target state is prime, the redirected prime-power contribution is the
  additional series displayed in the source proof; the elementary estimates
  there bound it by the remaining slack in the inequality.  These verifications
  give all clauses in \cref{def:eps-modified-chain-subinvariant-package}. -/)
  (title := /-- Sub-invariance of the modified chain -/)
  (latexEnv := "lemma")]
lemma eps_modified_chain_subinvariant :
    eps_modified_chain_subinvariant_package := by
  sorry_using [mangoldt_subinvariant_bound]

@[blueprint "lem:eps-modified-chain-hitting-mass-identity"
  (statement := /-- If the modified-chain sub-invariance package holds, then
  the adjoint upward chain started from initial mass $\nu_0$ on the prime layer
  has hitting mass exactly $\nu_0$ at every natural number.  Consequently the
  prime-layer Erd\H{o}s series is summable, and every primitive set has a
  summable Erd\H{o}s series whose sum is at most the Erd\H{o}s sum of the prime
  layer. -/)
  (proof := /-- Assume \cref{def:eps-modified-chain-subinvariant-package} and
  form the adjoint upward chain with respect to the weight $\nu_0$.  The
  sub-invariance clause supplies the missing transition mass to the absorbing
  state $\infty$, so the adjoint transition probabilities have total mass one.
  Start the chain with mass $\nu_0(p)$ at each prime $p$; this total initial
  mass is the convergent prime-layer series of \cref{def:prime-layer}.  Since
  primes are absorbing for the downward chain, the upward hitting mass equals
  the initial mass on the prime layer.  The adjoint recursion and induction on
  the divisibility rank then give hitting mass $\nu_0(n)$ for every $n$.  A
  primitive set meets any upward divisibility chain in at most one state, hence
  the chain-antichain inequality bounds every finite partial sum of the
  nonnegative series defining its Erd\H{o}s sum by the total initial mass on the
  primes.  The bounded-partial-sums criterion for nonnegative real series gives
  summability for the primitive set and the resulting inequality of
  \cref{def:erdos-sum}. -/)
  (title := /-- Hitting masses for the modified adjoint chain -/)
  (latexEnv := "lemma")]
lemma eps_modified_chain_hitting_mass_identity :
    eps_modified_chain_subinvariant_package ->
      Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
        ∀ A : Set ℕ, primitive_set A ->
          Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
            erdos_sum A ≤ erdos_sum prime_layer := by
  sorry

@[blueprint "lem:eps-chain-antichain-bound"
  (statement := /-- The prime-layer Erd\H{o}s series is summable, and every
  primitive set has a summable Erd\H{o}s series whose sum is at most the
  Erd\H{o}s sum of the prime layer. -/)
  (proof := /-- The sub-invariance package is supplied by
  \cref{lem:eps-modified-chain-subinvariant}.  Applying the hitting-mass
  identity \cref{lem:eps-modified-chain-hitting-mass-identity} to this package
  gives the summability of the prime-layer series and, for every primitive set,
  summability of its Erd\H{o}s series together with the desired bound. -/)
  (title := /-- Chain-antichain bound for the prime layer -/)
  (latexEnv := "lemma")]
lemma eps_chain_antichain_bound :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer := by
  sorry_using [eps_modified_chain_subinvariant, eps_modified_chain_hitting_mass_identity]

@[blueprint "thm:erdos-primitive-set-conjecture-164"
  (statement := /-- The Erd\H{o}s series of the prime layer $\mathbb N_1$ is
  summable.  For every primitive set $A\subseteq\mathbb N$, the Erd\H{o}s series
  of $A$ is summable and its sum is at most the Erd\H{o}s sum of the prime layer
  $\mathbb N_1$. -/)
  (proof := /-- This is precisely the chain-antichain bound established in
  \cref{lem:eps-chain-antichain-bound}. -/)
  (title := /-- Erd\H{o}s primitive set conjecture, problem \#164 -/)
  (latexEnv := "theorem")]
theorem erdos_primitive_set_conjecture_164 :
    Summable (fun n : ℕ => prime_layer.indicator erdos_weight n) ∧
      ∀ A : Set ℕ, primitive_set A ->
        Summable (fun n : ℕ => A.indicator erdos_weight n) ∧
          erdos_sum A ≤ erdos_sum prime_layer := by
  sorry_using [eps_chain_antichain_bound]

@[blueprint "def:real-initial-segment"
  (statement := /-- For a real parameter $x$, the initial segment
  $[1,x]\cap\mathbb N$ consists of natural numbers $n$ with $1\leq n\leq x$. -/)
  (title := /-- Real initial segment of the naturals -/)
  (latexEnv := "definition")]
def real_initial_segment (x : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ x}

@[blueprint "def:erdos-sum-up-to"
  (statement := /-- The truncated Erd\H{o}s sum $f(A\cap[1,x])$ is the
  Erd\H{o}s sum of the intersection of $A$ with
  \cref{def:real-initial-segment}. -/)
  (title := /-- Truncated Erd\H{o}s sum -/)
  (latexEnv := "definition")]
noncomputable def erdos_sum_up_to (A : Set ℕ) (x : ℝ) : ℝ :=
  erdos_sum (A ∩ real_initial_segment x)

@[blueprint "def:upper-doubly-log-density"
  (statement := /-- The upper doubly logarithmic density of a set
  $A\subseteq\mathbb N$ is
  $\limsup_{x\to\infty} f(A\cap[1,x])/\log\log x$, with the limit superior
  taken along real $x\to\infty$. -/)
  (title := /-- Upper doubly logarithmic density -/)
  (latexEnv := "definition")]
noncomputable def upper_doubly_log_density (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => erdos_sum_up_to A x / Real.log (Real.log x))
    Filter.atTop

@[blueprint "def:mangoldt-weight"
  (statement := /-- The invariant von Mangoldt weight is
  $\nu_\Lambda(1)=1$ and, for $n\neq1$,
  $\nu_\Lambda(n)=\int_1^\infty \log n/(\zeta(s)n^s)\,ds$ on the real axis. -/)
  (title := /-- Invariant von Mangoldt weight -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_weight (n : ℕ) : ℝ :=
  if n = 1 then 1 else
    ∫ s : ℝ in Set.Ioi (1 : ℝ),
      Real.log (n : ℝ) /
        (((riemannZeta (s : ℂ)).re) * Real.rpow (n : ℝ) s)

@[blueprint "def:mangoldt-weight-sum-up-to"
  (statement := /-- This is the truncated sum of the invariant von Mangoldt
  weight over $A\cap[1,x]$. -/)
  (title := /-- Truncated von Mangoldt-weight sum -/)
  (latexEnv := "definition")]
noncomputable def mangoldt_weight_sum_up_to (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (A ∩ real_initial_segment x).indicator mangoldt_weight n

@[blueprint "def:strictly-increasing-divisibility-chain"
  (statement := /-- A sequence $n_0,n_1,n_2,\ldots$ is a strictly increasing
  divisibility chain if it is strictly increasing as a sequence of natural
  numbers and each term divides its successor. -/)
  (title := /-- Strict increasing divisibility chains -/)
  (latexEnv := "definition")]
def strictly_increasing_divisibility_chain (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ ∀ i : ℕ, n i ∣ n (i + 1)

@[blueprint "def:chain-in-set"
  (statement := /-- A chain $n_0,n_1,n_2,\ldots$ lies in a set
  $A\subseteq\mathbb N$ if every term of the chain belongs to $A$. -/)
  (title := /-- Chain contained in a set -/)
  (latexEnv := "definition")]
def chain_in_set (n : ℕ → ℕ) (A : Set ℕ) : Prop :=
  ∀ i : ℕ, n i ∈ A

@[blueprint "def:chain-count-up-to"
  (statement := /-- The counting function of a chain at a real height $x$ is
  the number of indices $i$ for which $n_i\leq x$. -/)
  (title := /-- Chain counting function -/)
  (latexEnv := "definition")]
noncomputable def chain_count_up_to (n : ℕ → ℕ) (x : ℝ) : ℕ :=
  Set.ncard {i : ℕ | (n i : ℝ) ≤ x}

@[blueprint "def:upper-chain-density"
  (statement := /-- The upper doubly logarithmic density of the counting
  function of a chain is
  $\limsup_{x\to\infty}\#\{i:n_i\leq x\}/\log\log x$. -/)
  (title := /-- Upper density of a chain -/)
  (latexEnv := "definition")]
noncomputable def upper_chain_density (n : ℕ → ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => (chain_count_up_to n x : ℝ) / Real.log (Real.log x))
    Filter.atTop

@[blueprint "def:upper-chain-density-at-least"
  (statement := /-- The chain $n_0,n_1,n_2,\ldots$ has upper doubly
  logarithmic density at least $\Delta$ if its upper chain density is at least
  $\Delta$. -/)
  (title := /-- Lower bound for chain density -/)
  (latexEnv := "definition")]
def upper_chain_density_at_least (n : ℕ → ℕ) (Delta : ℝ) : Prop :=
  Delta ≤ upper_chain_density n

@[blueprint "def:chain-hits-count-up-to"
  (statement := /-- The hit-counting function of a chain against a set $A$ at
  height $x$ is the number of indices $i$ such that $n_i\in A$ and
  $n_i\leq x$. -/)
  (title := /-- Chain hit-counting function -/)
  (latexEnv := "definition")]
noncomputable def chain_hits_count_up_to (n : ℕ → ℕ) (A : Set ℕ) (x : ℝ) : ℕ :=
  Set.ncard {i : ℕ | n i ∈ A ∧ (n i : ℝ) ≤ x}

@[blueprint "def:upper-chain-hit-density"
  (statement := /-- The upper doubly logarithmic density of the visits of a
  chain to $A$ is
  $\limsup_{x\to\infty}\#\{i:n_i\in A,\ n_i\leq x\}/\log\log x$. -/)
  (title := /-- Upper density of chain hits -/)
  (latexEnv := "definition")]
noncomputable def upper_chain_hit_density (n : ℕ → ℕ) (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => (chain_hits_count_up_to n A x : ℝ) / Real.log (Real.log x))
    Filter.atTop

@[blueprint "def:chain-hits-density-at-least"
  (statement := /-- A chain visits $A$ with upper doubly logarithmic density at
  least $\Delta$ if its hit density against $A$ is at least $\Delta$. -/)
  (title := /-- Lower bound for hit density -/)
  (latexEnv := "definition")]
def chain_hits_density_at_least (n : ℕ → ℕ) (A : Set ℕ) (Delta : ℝ) : Prop :=
  Delta ≤ upper_chain_hit_density n A

@[blueprint "lem:mangoldt-weight-aggregate-comparison"
  (statement := /-- For every set $A\subseteq\mathbb N$, replacing the
  Erd\H{o}s weight by the invariant von Mangoldt weight does not change the
  upper doubly logarithmic density of the truncated sums. -/)
  (proof := /-- The source proves the asymptotic
  $\nu_\Lambda(n)=(1+O(1/\log n))\nu_0(n)$ with a more precise first-order
  term.  Summing the resulting error over $A\cap[1,x]$ gives an $O(1)$ total
  error, because $\sum_{n\leq x}1/(n\log^2 n)$ is bounded uniformly in $x$.
  Dividing by $\log\log x$ and taking the limit superior along $x\to\infty$
  therefore leaves the upper doubly logarithmic density unchanged. -/)
  (title := /-- Aggregate comparison of $\nu_\Lambda$ and $\nu_0$ -/)
  (latexEnv := "lemma")]
lemma mangoldt_weight_aggregate_comparison :
    ∀ A : Set ℕ,
      Filter.limsup
        (fun x : ℝ => mangoldt_weight_sum_up_to A x / Real.log (Real.log x))
        Filter.atTop = upper_doubly_log_density A := by
  sorry

@[blueprint "lem:probabilistic-dense-ambient-chain"
  (statement := /-- If $A\subseteq\mathbb N$ has positive upper doubly
  logarithmic density, then there exists a strictly increasing divisibility
  chain in $\mathbb N$ whose visits to $A$ have upper doubly logarithmic
  density at least that of $A$. -/)
  (proof := /-- Use the adjoint of the von Mangoldt downward chain with
  respect to the invariant weight $\nu_\Lambda$, started at $1$.  The invariant
  recursion implies that the expected number of visits to each state $n$ is
  $\nu_\Lambda(n)$.  By \cref{lem:mangoldt-weight-aggregate-comparison}, the
  expected normalized number of visits to $A\cap[1,x]$ has limit superior equal
  to the upper doubly logarithmic density of $A$.  The second-moment estimate
  in the source bounds the normalized visit counts uniformly in $L^2$, and the
  reverse Fatou argument then gives positive probability that the realized
  chain has visit-density at least this value.  Choosing such a realization
  gives the asserted ambient chain. -/)
  (title := /-- Dense ambient chain from the zeta process -/)
  (latexEnv := "lemma")]
lemma probabilistic_dense_ambient_chain :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_hits_density_at_least n A (upper_doubly_log_density A) := by
  sorry_using [mangoldt_weight_aggregate_comparison]

@[blueprint "lem:dense-hits-subchain-in-set"
  (statement := /-- Let $A\subseteq\mathbb N$ have positive upper doubly
  logarithmic density.  If a strictly increasing divisibility chain in
  $\mathbb N$ visits $A$ with upper doubly logarithmic density at least that of
  $A$, then the subsequence of its visits to $A$ is a strictly increasing
  divisibility chain lying in $A$ with the same lower bound for its upper
  doubly logarithmic density. -/)
  (proof := /-- Since the hit density is at least the positive number
  $\Delta$, the ambient chain visits $A$ infinitely often.  Enumerate the visit
  indices increasingly, and define the new chain by restricting the ambient
  chain to those indices.  Strict monotonicity is inherited from the ambient
  chain, and divisibility is inherited by transitivity along the intervening
  consecutive divisibility steps.  The counting function of the extracted
  chain up to height $x$ is exactly the hit-counting function of the ambient
  chain up to height $x$, so the upper doubly logarithmic density lower bound
  is preserved. -/)
  (title := /-- Extracting a dense subchain inside $A$ -/)
  (latexEnv := "lemma")]
lemma dense_hits_subchain_in_set :
    ∀ (A : Set ℕ) (ambient : ℕ → ℕ),
      0 < upper_doubly_log_density A ->
      strictly_increasing_divisibility_chain ambient ->
      chain_hits_density_at_least ambient A (upper_doubly_log_density A) ->
        ∃ n : ℕ → ℕ,
          strictly_increasing_divisibility_chain n ∧
          chain_in_set n A ∧
          upper_chain_density_at_least n (upper_doubly_log_density A) := by
  sorry

@[blueprint "thm:erdos-sarkozy-szemeredi-1217"
  (statement := /-- Let $A\subseteq\mathbb N$ have positive upper doubly
  logarithmic density $\Delta$.  Then $A$ contains a strictly increasing
  infinite divisibility chain $n_0\mid n_1\mid n_2\mid\cdots$ whose counting
  function has upper doubly logarithmic density at least $\Delta$. -/)
  (proof := /-- Apply \cref{lem:probabilistic-dense-ambient-chain} to obtain a
  strictly increasing divisibility chain in $\mathbb N$ whose visits to $A$
  have upper doubly logarithmic density at least $\Delta$.  Then apply
  \cref{lem:dense-hits-subchain-in-set} to the ambient chain.  The extracted
  subsequence lies in $A$, remains a strictly increasing divisibility chain,
  and has counting-density at least $\Delta$. -/)
  (title := /-- Erd\H{o}s--S\'ark\"ozy--Szemer\'edi problem \#1217 -/)
  (latexEnv := "theorem")]
theorem erdos_sarkozy_szemeredi_1217 :
    ∀ A : Set ℕ, 0 < upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        strictly_increasing_divisibility_chain n ∧
        chain_in_set n A ∧
        upper_chain_density_at_least n (upper_doubly_log_density A) := by
  sorry_using [probabilistic_dense_ambient_chain, dense_hits_subchain_in_set]
