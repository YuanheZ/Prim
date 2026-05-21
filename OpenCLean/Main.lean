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
  (statement := /-- For every natural number $n$, the von Mangoldt function
  satisfies $\sum_{q\mid n}\Lambda(q)=\log n$. -/)
  (proof := /-- This is exactly the standard divisor-sum identity for the von
  Mangoldt function, with the sum taken over the finite set of positive divisors
  of $n$. -/)
  (title := /-- Divisor sum of the von Mangoldt function -/)
  (latexEnv := "lemma")]
lemma von_mangoldt_divisor_sum (n : ℕ) :
    (∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q) = Real.log (n : ℝ) := by
  sorry

@[blueprint "lem:mertens-von-mangoldt-reciprocal"
  (statement := /-- There is an absolute constant $C$ such that, for every
  $t\geq 1$, the reciprocal von Mangoldt sum satisfies
  $|\sum_{q\leq t}\Lambda(q)/q-\log t|\leq C$. -/)
  (proof := /-- This is the Mertens estimate for the reciprocal von Mangoldt
  sum invoked in the partial summation proof of the tail estimate. The source
  cites Mertens' theorem for this input. -/)
  (title := /-- Mertens estimate for reciprocal von Mangoldt sums -/)
  (latexEnv := "lemma")]
lemma mertens_von_mangoldt_reciprocal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t ->
      |mangoldt_reciprocal_partial_sum t - Real.log t| ≤ C := by
  sorry

@[blueprint "lem:von-mangoldt-dirichlet-series-upper-bound"
  (statement := /-- For every $u>0$, the von Mangoldt Dirichlet series satisfies
  $\sum_q \Lambda(q)q^{-1-u}\leq 1/u$. -/)
  (proof := /-- The source proves this from the identity
  $\sum_q\Lambda(q)q^{-1-u}=-\zeta'(1+u)/\zeta(1+u)$, the comparison
  $-\zeta'(1+u)/\zeta(1+u)\leq \log 2/(2^u-1)$, and the elementary inequality
  $\log 2/(2^u-1)\leq 1/u$. -/)
  (title := /-- Dirichlet-series upper bound -/)
  (latexEnv := "lemma")]
lemma von_mangoldt_dirichlet_series_upper_bound :
    ∀ u : ℝ, 0 < u -> mangoldt_dirichlet_series u ≤ 1 / u := by
  sorry

@[blueprint "lem:mangoldt-tail-upper-bound"
  (statement := /-- There is an absolute constant $C$ such that, for every
  natural $m\geq 1$ and every real $y\geq 2$,
  $\sum_{q\geq y}\Lambda(q)/(q\log^2(mq))\leq
  1/\log(my)+C/\log^2(my)$. -/)
  (proof := /-- Apply partial summation to the reciprocal von Mangoldt sum in
  \cref{lem:mertens-von-mangoldt-reciprocal} with the decreasing function
  $t\mapsto \log^{-2}(mt)$. The boundary term and the integral give
  $1/\log(my)$, while the uniform Mertens error contributes
  $O(\log^{-2}(my))$, yielding the displayed one-sided estimate after enlarging
  the absolute constant. -/)
  (title := /-- Upper von Mangoldt tail estimate -/)
  (latexEnv := "lemma")]
lemma mangoldt_tail_upper_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m -> ∀ y : ℝ, 2 ≤ y ->
      mangoldt_tail_sum m y ≤
        1 / Real.log ((m : ℝ) * y) + C / (Real.log ((m : ℝ) * y)) ^ 2 := by
  sorry_using [mertens_von_mangoldt_reciprocal]

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
  $q\geq 2$ gives the lower threshold $q\geq\max(2,x/n)$, which is precisely the
  summation defining the tail majorant. -/)
  (title := /-- Reindexing the cut capacity -/)
  (latexEnv := "lemma")]
lemma cut_capacity_le_tail_majorant (x X : ℝ) (hx : 2 ≤ x) :
    cut_capacity x X ≤ tail_majorant x := by
  sorry

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
  (statement := /-- If the finite-support version of the problem holds with an
  absolute constant, then the same absolute-constant bound holds for arbitrary
  primitive sets supported in $[x,\infty)$. -/)
  (proof := /-- The source invokes this limiting step at the beginning of the
  proof. The asserted argument is to apply the finite bound to the truncations
  $A\cap [x,X]$ and then let $X$ tend to infinity, using the convergence of the
  nonnegative Erd\H{o}s sum over the primitive set. -/)
  (title := /-- Removing the finite truncation -/)
  (latexEnv := "lemma")]
lemma finite_truncation_principle :
    (∃ C : ℝ, erdos1196_finite_bound C) -> ∃ C : ℝ, erdos1196_bound C := by
  sorry

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
