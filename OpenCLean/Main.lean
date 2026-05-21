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

@[blueprint "lem:zeta-log-derivative-geometric-bound"
  (statement := /-- For every $u>0$, the logarithmic derivative of the Riemann
  zeta function at the real point $1+u$ satisfies
  $-\zeta'(1+u)/\zeta(1+u)\leq \log 2/(2^u-1)$.  In the Lean statement the
  complex logarithmic derivative is compared through its real part. -/)
  (proof := /-- Define the Dirichlet eta function by
  $\eta(s)=(1-2^{1-s})\zeta(s)$.  Differentiating the identity gives
  $\zeta'(1+u)/\zeta(1+u)+\log 2/(2^u-1)=\eta'(1+u)/\eta(1+u)$.  Hence the
  desired inequality is equivalent to the non-negativity of this logarithmic
  derivative.  For $s>1$ the Mellin representation
  $\eta(s)=\Gamma(s)^{-1}\int_0^\infty x^{s-1}(e^x+1)^{-1}\,dx$ can be written
  as $\eta(s)=\mathbb E h(X_s)$, where $h(x)=(1+e^{-x})^{-1}$ and $X_s$ has
  the gamma distribution of shape $s$ and scale $1$.  If $t>s>1$, then
  $X_t$ has the same distribution as $X_s+Y_{t-s}$ for an independent gamma
  variable $Y_{t-s}$, and $h$ is increasing; therefore $\eta(t)\geq\eta(s)$.
  Thus $\eta$ is non-decreasing on $(1,\infty)$, so its logarithmic derivative
  is non-negative there, proving the displayed comparison. -/)
  (title := /-- Zeta logarithmic-derivative comparison -/)
  (latexEnv := "lemma")]
lemma zeta_log_derivative_geometric_bound :
    ∀ u : ℝ, 0 < u ->
      ((- deriv riemannZeta ((1 + u : ℝ) : ℂ) /
          riemannZeta ((1 + u : ℝ) : ℂ)).re) ≤
        Real.log (2 : ℝ) / (Real.rpow (2 : ℝ) u - 1) := by
  sorry

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

@[blueprint "lem:mangoldt-tail-upper-bound"
  (statement := /-- There is an absolute constant $C$ such that, for every
  natural $m\geq 1$ and every real $y\geq 2$, the von Mangoldt tail series is
  summable and
  $\sum_{q\geq y}\Lambda(q)/(q\log^2(mq))\leq
  1/\log(my)+C/\log^2(my)$. -/)
  (proof := /-- Apply partial summation to the reciprocal von Mangoldt sum in
  \cref{lem:mertens-von-mangoldt-reciprocal} with the decreasing function
  $t\mapsto \log^{-2}(mt)$.  This proves convergence of the improper tail sum.
  The boundary term and the integral give
  $1/\log(my)$, while the uniform Mertens error contributes
  $O(\log^{-2}(my))$, yielding the displayed one-sided estimate after enlarging
  the absolute constant. -/)
  (title := /-- Upper von Mangoldt tail estimate -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_upper_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y ->
      Summable (fun q : ℕ => if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ∧
        mangoldt_tail_sum m y ≤
          1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  sorry_using [mertens_von_mangoldt_reciprocal]

@[blueprint "lem:mangoldt-tail-finite-sum-le"
  (statement := /-- Let $m\geq 1$, let $y\geq 2$, and let $S$ be a finite set of
  natural numbers.  The contribution of $S$ to the von Mangoldt tail is bounded
  above by the full tail:
  $\sum_{q\in S}1_{q\geq y}\Lambda(q)/(q\log^2(mq))\leq
  \sum_{q\geq y}\Lambda(q)/(q\log^2(mq))$. -/)
  (proof := /-- By \cref{lem:mangoldt-tail-upper-bound}, the non-negative tail
  series defining \cref{def:mangoldt-tail-sum} is summable for the stated
  values of $m$ and $y$.  The von Mangoldt function is non-negative, and the
  remaining factors in the tail summand are non-negative; hence every summand in
  the tail is non-negative.  The standard finite-partial-sum comparison for a
  summable non-negative real series then gives the asserted bound for the finite
  set $S$. -/)
  (title := /-- Finite tails are bounded by the full von Mangoldt tail -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_finite_sum_le (m : ℕ) (hm : 1 ≤ m) (y : ℝ) (hy : 2 ≤ y)
    (s : Finset ℕ) :
    (∑ q ∈ s, if y ≤ (q : ℝ) then mangoldt_tail_term m q else 0) ≤
      mangoldt_tail_sum m y := by
  sorry_using [mangoldt_tail_upper_bound]

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
  (proof := /-- Discard the upper restriction $r\leq X$ in the cut capacity and
  write $r=nq$. The condition $r/q<x$ becomes $n<x$, and the condition
  $r\geq x$ forces $q\geq x/n$. Combining this with the original restriction
  $q\geq 2$ gives the lower threshold $q\geq\max(2,x/n)$.  For each fixed
  $n$ with $1\leq n<x$, \cref{lem:mangoldt-tail-finite-sum-le} bounds the
  resulting finite set of $q$-contributions by the full tail in
  \cref{def:mangoldt-tail-sum}.  Summing these inequalities over $n$ gives
  exactly the majorant in \cref{def:tail-majorant}. -/)
  (title := /-- Reindexing the cut capacity -/)
  (latexEnv := "lemma")]
lemma cut_capacity_le_tail_majorant (x X : ℝ) (hx : 2 ≤ x) :
    cut_capacity x X ≤ tail_majorant x := by
  sorry_using [mangoldt_tail_finite_sum_le]

@[blueprint "lem:tail-majorant-bound"
  (statement := /-- There is an absolute constant $C$ such that, for every
  $x\geq 2$, the reindexed tail majorant is at most $1+C/\log x$. -/)
  (proof := /-- For each integer $1\leq n<x$, apply
  \cref{lem:mangoldt-tail-upper-bound} with
  $y=\max(2,x/n)$. Since $n\max(2,x/n)\geq x$, the main term is at most
  $1/\log x$ and the error term is $O(1/\log^2 x)$. Summing over
  $1\leq n<x$ gives $\sum_{n<x}1/n=\log x+O(1)$ by the standard harmonic
  estimates, and hence the claimed bound. -/)
  (title := /-- Bounding the reindexed tail majorant -/)
  (latexEnv := "lemma")]
lemma tail_majorant_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x -> tail_majorant x ≤ 1 + C / Real.log x := by
  sorry_using [mangoldt_tail_upper_bound]

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
