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
  $[x,\infty)$, one has $f(A)\leq 1+C/\log x$. -/)
  (title := /-- Quantitative infinite-support bound -/)
  (latexEnv := "definition")]
def erdos1196_bound (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x -> ∀ A : Set ℕ,
      primitive_set A -> supported_above A x -> erdos_sum A ≤ 1 + C / Real.log x

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

@[blueprint "lem:dirichlet-eta-gamma-expectation"
  (statement := /-- For every real $s>1$, the eta value of
  \cref{def:dirichlet-eta-real} is the expectation of
  $h(x)=(1+e^{-x})^{-1}$ against the gamma distribution of shape $s$ and
  scale $1$.  In Lean this gamma distribution is
  `ProbabilityTheory.gammaMeasure s 1`. -/)
  (proof := /-- Fix $s>1$.  The measure
  `ProbabilityTheory.gammaMeasure s 1` has density
  $\Gamma(s)^{-1}x^{s-1}e^{-x}$ on $[0,\infty)$.  Multiplying this density by
  $h(x)=(1+e^{-x})^{-1}=e^x/(1+e^x)$ converts the expectation into
  $$\Gamma(s)^{-1}\int_0^\infty {x^{s-1}\over 1+e^x}\,dx.$$
  The classical Mellin transform formula for Dirichlet eta identifies this
  last integral with $(1-2^{1-s})\zeta(s)$, which is precisely the real value
  specified by \cref{def:dirichlet-eta-real} on the half-line $s>1$. -/)
  (title := /-- Gamma-expectation representation of eta -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_gamma_expectation :
    ∀ s : ℝ, 1 < s ->
      dirichlet_eta_real s =
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1) := by
  sorry

@[blueprint "lem:gamma-logistic-expectation-monotone"
  (statement := /-- The expectation of the increasing function
  $h(x)=(1+e^{-x})^{-1}$ under a gamma distribution of scale $1$ is
  non-decreasing as the positive shape parameter increases. -/)
  (proof := /-- Let $0<a\leq b$ and put $c=b-a\geq 0$.  If $c=0$ the two
  expectations are equal.  If $c>0$, let $X_a$ and $Y_c$ be independent gamma
  variables of shapes $a$ and $c$, both with scale $1$.  The additivity of
  gamma laws with common scale gives $X_a+Y_c$ the gamma law of shape $b$.
  Since $Y_c\geq 0$ almost surely and $h(x)=(1+e^{-x})^{-1}$ is increasing on
  $[0,\infty)$, one has $h(X_a)\leq h(X_a+Y_c)$ almost surely.  Taking
  expectations gives the desired monotonicity in the shape parameter. -/)
  (title := /-- Monotonicity of gamma-logistic expectations -/)
  (latexEnv := "lemma")]
lemma gamma_logistic_expectation_monotone :
    MonotoneOn
      (fun s : ℝ =>
        ∫ x : ℝ, (1 / (1 + Real.exp (-x))) ∂(ProbabilityTheory.gammaMeasure s 1))
      (Set.Ioi (0 : ℝ)) := by
  sorry

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
  sorry_using [dirichlet_eta_gamma_expectation, gamma_logistic_expectation_monotone]

@[blueprint "lem:dirichlet-eta-log-derivative-nonnegative"
  (statement := /-- For every real $s>1$, the logarithmic derivative of the
  real Dirichlet eta function is non-negative:
  $0\leq \eta'(s)/\eta(s)$. -/)
  (proof := /-- Fix $s>1$.  By \cref{lem:dirichlet-eta-monotone}, the function
  $\eta$ is non-decreasing on $(1,\infty)$.  The representation in
  \cref{lem:dirichlet-eta-gamma-expectation}, with its exponentially decaying
  gamma density, justifies differentiability at $s$ by differentiating under
  the integral sign on compact subintervals of $(1,\infty)$.  Hence the
  one-sided difference-quotient characterization of the derivative of a
  monotone differentiable function gives $\eta'(s)\geq 0$.  By
  \cref{lem:dirichlet-eta-positive}, $\eta(s)>0$.  Dividing the non-negative
  derivative by this positive value gives $\eta'(s)/\eta(s)\geq 0$. -/)
  (title := /-- Non-negativity of the eta logarithmic derivative -/)
  (latexEnv := "lemma")]
lemma dirichlet_eta_log_derivative_nonnegative :
    ∀ s : ℝ, 1 < s -> 0 ≤ deriv dirichlet_eta_real s / dirichlet_eta_real s := by
  sorry_using [dirichlet_eta_positive, dirichlet_eta_gamma_expectation, dirichlet_eta_monotone]

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
  (statement := /-- For every $u>0$, the eta-factor contribution to the
  logarithmic derivative at $1+u$ is non-negative:
  $$0\leq \operatorname{Re}\frac{\zeta'(1+u)}{\zeta(1+u)}+
  \frac{\log 2}{2^u-1}.$$
  This is the formal form, after substituting the defining identity
  $\eta(s)=(1-2^{1-s})\zeta(s)$, of the assertion that the Dirichlet eta
  function has non-negative logarithmic derivative on $(1,\infty)$. -/)
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
  sorry_using [dirichlet_eta_log_derivative_nonnegative, dirichlet_eta_zeta_log_derivative]

@[blueprint "lem:zeta-log-derivative-geometric-bound"
  (statement := /-- For every $u>0$, the logarithmic derivative of the Riemann
  zeta function at the real point $1+u$ satisfies
  $-\zeta'(1+u)/\zeta(1+u)\leq \log 2/(2^u-1)$.  In the Lean statement the
  complex logarithmic derivative is compared through its real part. -/)
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
  sorry_using [eta_log_derivative_nonnegative]

@[blueprint "lem:von-mangoldt-dirichlet-series-upper-bound"
  (statement := /-- For every $u>0$, the von Mangoldt Dirichlet series satisfies
  $\sum_q \Lambda(q)q^{-1-u}\leq 1/u$. -/)
  (proof := /-- The source proves this from the identity
  $\sum_q\Lambda(q)q^{-1-u}=-\zeta'(1+u)/\zeta(1+u)$.  Apply
  \cref{lem:zeta-log-derivative-geometric-bound} to bound the logarithmic
  derivative by $\log 2/(2^u-1)$.  Finally,
  $(2^u-1)/\log 2=u\int_0^1 2^{tu}\,dt\geq u$, since $2^{tu}\geq 1$ on
  $[0,1]$; rearranging gives $\log 2/(2^u-1)\leq 1/u$. -/)
  (title := /-- Dirichlet-series upper bound -/)
  (latexEnv := "lemma")]
lemma von_mangoldt_dirichlet_series_upper_bound :
    ∀ u : ℝ, 0 < u -> mangoldt_dirichlet_series u ≤ 1 / u := by
  sorry_using [zeta_log_derivative_geometric_bound]

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

@[blueprint "lem:mangoldt-subinvariant-bound"
  (statement := /-- For every natural $n\geq 2$,
  $\log n\sum_{q\geq 2}\Lambda(q)/(q\log^2(nq))\leq 1$. This is the
  non-asymptotic sub-invariance estimate for the doubly harmonic weight. -/)
  (proof := /-- Use the integral identity
  $1/\log^2 a=\int_0^\infty u a^{-u}\,du$, apply
  \cref{lem:von-mangoldt-dirichlet-series-upper-bound} inside the integral, and
  sum the resulting geometric series. The source then bounds the series
  $\sum_{j\geq 1} x/(x+j)^2$ by $x/(x+1/2)\leq 1$, where $n=2^x$. -/)
  (title := /-- Non-asymptotic sub-invariance estimate -/)
  (latexEnv := "lemma")]
lemma mangoldt_subinvariant_bound :
    ∀ n : ℕ, 2 ≤ n -> Real.log (n : ℝ) * mangoldt_tail_sum n 2 ≤ 1 := by
  sorry_using [von_mangoldt_dirichlet_series_upper_bound]

@[blueprint "lem:finite-chain-cut-bound"
  (statement := /-- Let $2\leq x\leq X$, and let $A\subseteq\mathbb{N}$ be a
  primitive set supported in $[x,X]$. Then $f(A)$ is at most the finite
  von Mangoldt cut capacity associated with $x$ and $X$. -/)
  (proof := /-- The source constructs the initial mass
  $b(n)=\nu_0(n)-\sum_{2\leq q\leq X/n}\nu_0(nq)P(nq\searrow n)$ on
  $[x,X]$ for the downward von Mangoldt chain. The nonnegativity of this mass is
  obtained from \cref{lem:mangoldt-subinvariant-bound}. The source then asserts
  the downward induction showing that the hitting mass equals $\nu_0(n)$ on
  $[x,X]$. Applying the primitive-set chain inequality and using
  \cref{lem:von-mangoldt-divisor-sum} identifies the remaining boundary
  contribution with the cut capacity. -/)
  (title := /-- Finite chain cut bound -/)
  (latexEnv := "lemma")]
lemma finite_chain_cut_bound (A : Set ℕ) (x X : ℝ) (hx : 2 ≤ x)
    (hprim : primitive_set A) (hsupp : supported_in_interval A x X) :
    erdos_sum A ≤ cut_capacity x X := by
  sorry_using [von_mangoldt_divisor_sum, mangoldt_subinvariant_bound]

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
  (statement := /-- There is an absolute constant $C$ for which the finite
  version of the Erd\H{o}s--S\'ark\"ozy--Szemer\'edi bound holds: every primitive
  set supported in $[x,X]$ with $2\leq x\leq X$ has Erd\H{o}s sum at most
  $1+C/\log x$. -/)
  (proof := /-- Choose the constant supplied by \cref{lem:tail-majorant-bound}.
  For a primitive set supported in $[x,X]$, first apply
  \cref{lem:finite-chain-cut-bound} to bound its Erd\H{o}s sum by the cut
  capacity. Then apply \cref{lem:cut-capacity-le-tail-majorant} and finally the
  estimate from \cref{lem:tail-majorant-bound}. -/)
  (title := /-- Finite large primitive-set bound -/)
  (latexEnv := "lemma")]
lemma finite_large_primitive_bound :
    ∃ C : ℝ, erdos1196_finite_bound C := by
  sorry_using [finite_chain_cut_bound, cut_capacity_le_tail_majorant, tail_majorant_bound]

@[blueprint "lem:finite-truncation-principle"
  (statement := /-- If there is a real constant $C\geq 0$ such that every
  primitive set supported in a finite interval $[x,X]$ with $2\leq x\leq X$
  satisfies $f(A)\leq 1+C/\log x$, then there is a real constant $C\geq 0$ such
  that every primitive set supported in $[x,\infty)$ with $x\geq 2$ satisfies
  $f(A)\leq 1+C/\log x$. -/)
  (proof := /-- Unpack \cref{def:erdos1196-finite-bound}.  Fix $x\geq 2$ and
  a primitive set $A$ supported above $x$.  For each natural number $N$, put
  $B=A\cap \{0,\ldots,N-1\}$.  By \cref{def:primitive-set}, $B$ is primitive,
  and by \cref{def:supported-above,def:supported-in-interval} it is supported
  in $[x,\max\{x,N\}]$.  The finite hypothesis therefore bounds
  $f(B)$ by $1+C/\log x$.  By \cref{def:erdos-sum,def:erdos-weight}, this is
  exactly the $N$th finite partial sum of the nonnegative series defining
  $f(A)$.  Since all partial sums of this nonnegative real series are bounded by
  $1+C/\log x$, the standard bounded-partial-sums theorem for nonnegative real
  series gives $f(A)\leq 1+C/\log x$.  Together with the same nonnegative
  constant $C$, this is precisely \cref{def:erdos1196-bound}. -/)
  (title := /-- Removing the finite truncation -/)
  (latexEnv := "lemma")]
lemma finite_truncation_principle :
    (∃ C : ℝ, erdos1196_finite_bound C) -> ∃ C : ℝ, erdos1196_bound C := by
  rintro ⟨C, hC_nonneg, hfinite⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx A hA_primitive hA_supported
  let f : ℕ → ℝ := fun n => A.indicator erdos_weight n
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hnA : n ∈ A
    · have h2n : (2 : ℝ) ≤ (n : ℝ) := le_trans hx (hA_supported n hnA)
      have hn_pos : 0 < (n : ℝ) := by linarith
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      simp only [f, Set.indicator_of_mem hnA]
      unfold erdos_weight
      positivity
    · simp [f, Set.indicator_of_notMem hnA]
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ 1 + C / Real.log x := by
    intro N
    let B : Set ℕ := A ∩ (Finset.range N : Set ℕ)
    have hB_primitive : primitive_set B := by
      exact hA_primitive.subset (by intro n hn; exact hn.1)
    have hB_supported : supported_in_interval B x (max x (N : ℝ)) := by
      intro n hn
      constructor
      · exact hA_supported n hn.1
      · exact le_trans (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hn.2)))
          (le_max_right x (N : ℝ))
    have hB_sum : erdos_sum B = ∑ n ∈ Finset.range N, f n := by
      unfold erdos_sum
      rw [tsum_eq_sum]
      · refine Finset.sum_congr rfl ?_
        intro n hn
        by_cases hnA : n ∈ A
        · have hnB : n ∈ B := ⟨hnA, hn⟩
          simp [f, Set.indicator_of_mem hnB, Set.indicator_of_mem hnA]
        · have hnB : n ∉ B := by
            intro h
            exact hnA h.1
          simp [f, Set.indicator_of_notMem hnB, Set.indicator_of_notMem hnA]
      · intro n hn
        have hn_not_lt : ¬ n < N := by
          intro hnlt
          exact hn (Finset.mem_range.mpr hnlt)
        have hnB : n ∉ B := by
          intro h
          exact hn_not_lt (Finset.mem_range.mp h.2)
        simp [Set.indicator_of_notMem hnB]
    have hB_bound := hfinite x (max x (N : ℝ)) hx (le_max_left x (N : ℝ)) B
      hB_primitive hB_supported
    simpa [hB_sum] using hB_bound
  have hf_summable : Summable f := summable_of_sum_range_le hf_nonneg hpartial
  have hsum_le : (∑' n : ℕ, f n) ≤ 1 + C / Real.log x :=
    hf_summable.tsum_le_of_sum_range_le hpartial
  simpa [erdos_sum, f] using hsum_le

@[blueprint "thm:erdos-sarkozy-szemeredi-1196"
  (statement := /-- There is an absolute constant $C$ such that, for every real
  $x\geq 2$ and every primitive set $A\subseteq\mathbb{N}$ contained in
  $[x,\infty)$, one has
  $f(A)\leq 1+C/\log x$. Equivalently,
  $f(A)\leq 1+O(1/\log x)$ uniformly for primitive sets supported above $x$. -/)
  (proof := /-- The finite theorem \cref{lem:finite-large-primitive-bound}
  supplies an absolute constant for all primitive sets supported in finite
  intervals $[x,X]$. Applying the limiting principle
  \cref{lem:finite-truncation-principle} removes the upper endpoint and gives
  the stated bound for all primitive sets contained in $[x,\infty)$. -/)
  (title := /-- Erd\H{o}s--S\'ark\"ozy--Szemer\'edi problem \#1196 -/)
  (latexEnv := "theorem")]
theorem erdos_sarkozy_szemeredi_1196 :
    ∃ C : ℝ, erdos1196_bound C := by
  sorry_using [finite_large_primitive_bound, finite_truncation_principle]
