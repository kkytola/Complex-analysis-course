import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Power series" =>
%%%
file := "power-series"
%%%

:::group "grp_power_series"
Power series
:::

# Uniform convergence

:::definition "def_uniform_limit" (parent := "grp_power_series") (uses := "def_limit")
{nodetitle}[Uniform convergence] {palka}[Sec. VII.1.1]

Let $`(f_n)_{n \in \bN}` be a sequence of functions
$`f_n \colon X \to \bC`, and let $`f \colon X \to \bC`
also be a such function. We say that the sequence
$`(f_n)_{n \in \bN}` {term}[converges uniformly] to $`f`
(on $`X`) if for every $`\eps > 0` there exists an $`N \in \bN`
such that for all $`n \ge N` we have
$$`
\begin{align*}
  \big| f_n(x) - f(x) \big| < \eps
  \qquad \text{ for all } x \in X .
\end{align*}
`
:::

:::lemma_ "lem_cauchy_uniform_limit_criterion" (parent := "grp_power_series") (uses := "def_uniform_limit")
{nodetitle}[Cauchy criterion for uniform convergence] {palka}[Thm VII.1.2]

Let $`f_n \colon A \to \bC`, $`n \in \bN`,
be complex-valued functions defined on the same set $`A`.
Then the sequence $`(f_n)_{n \in \bN}` converges uniformly on $`A`
if and only if for every $`\eps > 0` there exists an $`N \in \bN`
such that for all $`m,n \ge N` and all $`z \in A`
we have $`|f_n(z) - f_m(z)| < \eps`.

(When $`(f_n)_{n \in \bN}` satisfies the condition above, it could
be called a {term}[uniform Cauchy sequence] on $`A`.)
:::

:::proof "lem_cauchy_uniform_limit_criterion" (uses := "lem_complex_complete")
…
:::

:::lemma_ "lem_uniform_limit_continuous" (parent := "grp_power_series") (uses := "def_uniform_limit, def_continuous")
{nodetitle}[Continuity is preserved in uniform limits] {palka}[Thm VII.1.1]

Let $`X` be a metric space (e.g., $`\bR`, $`\bC`, or a subset of these).
If a sequence $`(f_n)_{n \in \bN}` of continuous functions
$`f_n \colon X \to \bC` converges uniformly to a function
$`f \colon X \to \bC`, then $`f` is continuous.
:::

:::proof "lem_uniform_limit_continuous"
See *MS-C1541 Metric Spaces*.
:::

:::lemma_ "lem_uniform_limit_integral" (parent := "grp_power_series") (uses := "def_uniform_limit, def_continuous, def_riemann_integral, lem_uniform_limit_continuous")
{nodetitle}[Integration commutes with uniform limits] {palka}[Thm VII.1.1]

If a sequence $`(f_n)_{n \in \bN}` of continuous functions
$`f_n \colon [a,b] \to \bC` on a closed interval $`[a,b] \subset \bR`
converges uniformly to a function
$`f \colon [a,b] \to \bC`, then we have
$$`
\begin{align*}
  \lim_{n \to \infty} \int_a^b f_n(x) \, \ud x
    = \int_a^b f(x) \, \ud x .
\end{align*}
`
:::

:::proof "lem_uniform_limit_integral"
…
:::

:::corollary "cor_uniform_limit_contour_integral" (parent := "grp_power_series") (uses := "def_uniform_limit, def_continuous, def_contour_integral")
{nodetitle}[Contour integration commutes with uniform limits] {palka}[Thm VII.1.1]

If a sequence $`(f_n)_{n \in \bN}` of continuous functions
$`f_n \colon A \to \bC` on a subset $`A \subset \bC` of the complex plane
converges uniformly to a function
$`f \colon A \to \bC`, then for any piecewise smooth path $`\gamma`
in $`A` we have
$$`
\begin{align*}
  \lim_{n \to \infty} \int_\gamma f_n(z) \, \ud z
    = \int_\gamma f(z) \, \ud z .
\end{align*}
`
:::

:::proof "cor_uniform_limit_contour_integral" (uses := "lem_uniform_limit_integral")
This follows straightforwardly from the definition of contour integration
and {bpref "lem_uniform_limit_integral"}[] above.
:::

:::definition "def_uoc_limit" (parent := "grp_power_series") (uses := "def_uniform_limit")
{nodetitle}[Convergence uniformly on compacts] {palka}[Sec. VII.1.2]

Let $`(f_n)_{n \in \bN}` be a sequence of functions
$`f_n \colon A \to \bC` on $`A \subset \bC`, and
let $`f \colon A \to \bC` also be a such function. We say
that the sequence $`(f_n)_{n \in \bN}` {term}[converges uniformly
on compacts] (UOC) to $`f` if for every compact subset $`K \subset A`
the restrictions $`f_n|_K \colon K \to \bC` converge
uniformly on $`K` to $`f|_K \colon K \to \bC`. We then write
$$`
\begin{align*}
  f_n \xrightarrow{\UOC} f \qquad \text{ as } n \to \infty .
\end{align*}
`

(This notion is also called by the alternative names
{term}[locally uniform convergence] and {term}[normal convergence].)
:::

:::lemma_ "lem_uoc_limit_analytic" (parent := "grp_power_series") (uses := "def_uoc_limit, def_analytic_function")
{nodetitle}[UOC limit of analytic functions] {palka}[Thm VII.3.1]

Suppose that functions $`f_1, f_2, \ldots \colon U \to \bC`
are analytic functions on an open set $`U \subset \bC`
and the sequence $`(f_n)_{n \in \bN}` converges uniformly
on compacts to a function $`f`. Then $`f` is analytic on $`U`.
Moreover, for any $`k \in \bN`, the sequence $`(f^{(k)}_n)_{n \in \bN}`
of $`k`th derivatives converges uniformly on compacts to $`f^{(k)}`.
:::

:::proof "lem_uoc_limit_analytic" (uses := "cor_uniform_limit_contour_integral, thm_cauchy_formula_derivative")
…
:::

# Complex series

:::definition "def_complex_series" (parent := "grp_power_series") (uses := "def_limit, thm_complex_number_field")
{nodetitle}[Complex series] {palka}[Sec. VII.2.1]

Let $`z_1, z_2, z_3, \ldots \in \bC` be complex numbers.
For $`N \in \bN`, define the $`N`th {term}[partial sum] of these as
$$`
\begin{align*}
  S_N \; = \; \sum_{n=1}^N z_n \; = \; z_1 + z_2 + \cdots + z_N \, .
\end{align*}
`
We say that the series $`\sum_{n=1}^\infty z_n` {term}[converges]
if the sequence $`(S_N)_{N \in \bN}` of partial sums has
a limit, and we then denote
$$`
\begin{align*}
  \sum_{n=1}^\infty z_n = \lim_{N \to \infty} \; \sum_{n=1}^N z_n \, .
\end{align*}
`

(Obvious modifications to the above definition are made
if the terms' indexing starts from $`n=0` or some other index, and
the notation is correspondingly changed to, e.g., $`\sum_{n=0}^\infty`.)
:::

:::lemma_ "lem_terms_tend_to_zero" (parent := "grp_power_series") (uses := "def_complex_series")
{nodetitle}[Terms of a convergent series tend to zero]

If a complex series $`\sum_{n=1}^\infty z_n` converges,
then we have
$$`
\begin{align*}
  \lim_{n \to \infty} z_n = 0 .
\end{align*}
`
:::

:::proof "lem_terms_tend_to_zero"
…
:::

:::lemma_ "lem_geometric_series" (parent := "grp_power_series") (uses := "def_complex_series")
{nodetitle}[Geometric series]

The geometric series
$$`
\begin{align*}
  \sum_{n=0}^\infty z^n \; = \; 1 + z + z^2 + z^3 + \cdots ,
\end{align*}
`
with ratio $`z \in \bC` converges if and only if
$`|z| < 1`. In that case its sum is
$$`
\begin{align*}
  \sum_{n=0}^\infty z^n \; = \; \frac{1}{1-z} .
\end{align*}
`
:::

:::proof "lem_geometric_series"
…
:::

:::definition "def_absolute_convergence" (parent := "grp_power_series") (uses := "def_complex_series, def_absolute_value")
{nodetitle}[Absolute convergence of a complex series]

A complex series $`\sum_{n=1}^\infty z_n` is said to
{term}[converge absolutely] if the series of absolute values
$`\sum_{n=1}^\infty |z_n|` converges.
:::

:::lemma_ "lem_absolute_convergence_implies_convergence" (parent := "grp_power_series") (uses := "def_absolute_convergence, def_complex_series")
{nodetitle}[Absolute convergence implies convergence]

If a complex series
converges absolutely, then it converges.
:::

:::proof "lem_absolute_convergence_implies_convergence" (uses := "lem_complex_complete")
…
:::

:::lemma_ "lem_ratio_test" (parent := "grp_power_series") (uses := "def_complex_series, def_absolute_convergence")
{nodetitle}[D'Alembert's ratio test]

Suppose that $`\sum_{n=1}^\infty z_n` is a complex
series such that the limit
$$`
\begin{align*}
  r = \lim_{n \to \infty} \frac{|z_{n+1}|}{|z_n|}
\end{align*}
`
exists. Then:

* (i) If $`r < 1`, then the series $`\sum_{n=1}^\infty z_n` converges absolutely.
* (ii) If $`r > 1`, then the series $`\sum_{n=1}^\infty z_n` does not converge.
:::

:::proof "lem_ratio_test" (uses := "lem_terms_tend_to_zero, lem_geometric_series, lem_absolute_convergence_implies_convergence")
…
:::

# Series of functions

:::definition "def_function_series" (parent := "grp_power_series") (uses := "def_limit, def_uniform_limit, def_complex_series")
{nodetitle}[Series of functions] {palka}[Sec. VII.2.2]

Let $`f_1, f_2, f_3, \ldots` be complex-valued functions on a set $`A`.
For $`N \in \bN`,
define their $`N`th {term}[partial sum] function $`F_N \colon A \to \bC` by
$$`
\begin{align*}
  F_N(z) \; = \; \sum_{n=1}^N f_n(z) \; = \; f_1(z) + \cdots + f_N(z) \, .
\end{align*}
`
We say that the function series $`\sum_{n=1}^\infty f_n`
{term}[converges pointwise]
if the sequence $`\big(F_N(z)\big)_{N \in \bN}` of partial sums has
a limit at every $`z \in A`.
We say that the function series $`\sum_{n=1}^\infty f_n`
{term}[converges uniformly] on $`A`
if the sequence $`(F_N)_{N \in \bN}` of partial sum functions
converges uniformly on $`A`.
We say that the function series $`\sum_{n=1}^\infty f_n`
{term}[converges uniformly on compacts]
if the sequence $`(F_N)_{N \in \bN}` of partial sum functions
converges uniformly on compacts.

The limit function is then denoted by $`\sum_{n=1}^\infty f_n`.

(Obvious modifications to the above are made
if the terms' indexing starts from $`n=0` or some other index, and
the notation is correspondingly changed to, e.g., $`\sum_{n=0}^\infty`.)
:::

:::lemma_ "lem_weierstrass_test" (parent := "grp_power_series") (uses := "def_function_series")
{nodetitle}[Weierstrass M-test] {palka}[Thm VII.2.2]

Suppose that $`M_1,M_2,\ldots \ge 0` are nonnegative
numbers such that the series $`\sum_{n=1}^\infty M_n` converges.
Suppose also that for each $`n \in \bN`,
$`f_n \colon X \to \bC` is a function on $`X`
such that $`|f_n(x)| \le M_n` for all $`x \in X`.
Then the series $`\sum_{n=1}^\infty f_n`
converges absolutely and uniformly on $`X`.
:::

:::proof "lem_weierstrass_test" (uses := "lem_cauchy_uniform_limit_criterion")
…
:::

:::lemma_ "lem_uoc_analytic_series" (parent := "grp_power_series") (uses := "def_uniform_limit, def_function_series, def_analytic_function")
{nodetitle}[Series of analytic functions] {palka}[Thm VII.3.2]

Suppose that functions $`f_1, f_2, \ldots \colon U \to \bC`
are analytic functions on an open set $`U \subset \bC`
such that the series
$`\sum_{n=1}^\infty f_n` converges uniformly on compacts to a
function $`f \colon U \to \bC`. Then $`f` is analytic on $`U`.
Moreover, for any $`k \in \bN`, the series $`\sum_{n=1}^\infty f^{(k)}_n`
of $`k`th derivatives converges uniformly on compacts to $`f^{(k)}`.
:::

:::proof "lem_uoc_analytic_series" (uses := "lem_uoc_limit_analytic")
…
:::

# Power series

:::definition "def_power_series" (parent := "grp_power_series") (uses := "def_function_series")
{nodetitle}[Power series] {palka}[Sec. VII.3.3]

Let $`z_0 \in \bC` be a point in the complex plane
and let $`a_0,a_1,a_2\ldots \in \bC` be coefficients.
A function series of the form
$$`
\begin{align*}
\sum_{n=0}^\infty a_n \, (z-z_0)^n
  = a_0 + a_1 \, (z - z_0) + a_2 \, (z - z_0)^2 + \cdots
\end{align*}
`
is called a {term}[power series] centered at $`z_0`.
:::

:::lemma_ "lem_abel" (parent := "grp_power_series") (uses := "def_power_series, def_absolute_convergence")
{nodetitle}[Abel's theorem]

If a power series
$$`
\begin{align*}
  \sum_{n=0}^\infty a_n \, (z-z_0)^n
\end{align*}
`
converges at $`z = w \in \bC`, then it converges
absolutely for all $`z \in \bC` such that $`|z-z_0| < |w-z_0|`.
:::

:::proof "lem_abel" (uses := "lem_absolute_convergence_implies_convergence")
…
:::

:::corollary "cor_abel_contrapositive" (parent := "grp_power_series") (uses := "def_power_series, def_absolute_convergence")
{nodetitle}[Abel's theorem in the contrapositive]

If a power series
$$`
\begin{align*}
  \sum_{n=0}^\infty a_n \, (z-z_0)^n
\end{align*}
`
does not converge at $`z = w \in \bC`, then it does not converge
at any $`z \in \bC` such that $`|z-z_0| > |w-z_0|`.
:::

:::proof "cor_abel_contrapositive" (uses := "lem_abel")
…
:::

:::definition "def_radius_of_convergence" (parent := "grp_power_series") (uses := "def_power_series, lem_abel, cor_abel_contrapositive")
{nodetitle}[Radius of convergence]

The {term}[radius of convergence] of a power series
$$`
\begin{align*}
  \sum_{n=0}^\infty a_n \, (z-z_0)^n
\end{align*}
`
is defined as
$$`
\begin{align*}
  R \; := \;
    \sup \bigg\{ |z-z_0| \; \bigg| \;
      \sum_{n=0}^\infty a_n \, (z-z_0)^n \, \text{ converges} \bigg\} .
\end{align*}
`

From {bpref "lem_abel"}[] and {bpref "cor_abel_contrapositive"}[]
it follows that the power series $`\sum_{n=0}^\infty a_n \, (z-z_0)^n`
converges for all $`z \in \bC` such that $`|z-z_0| < R`
and diverges for all $`z \in \bC` such that $`|z-z_0| > R`.
The disk $`\DiskRC{R}{z_0}` is called the {term}[disk of convergence]
of the power series $`\sum_{n=0}^\infty a_n \, (z-z_0)^n`.

(If $`R=+\infty`, we interpret $`\DiskRC{R}{z_0} = \bC`.)
:::

:::lemma_ "lem_ratio_test_radius_of_convergence" (parent := "grp_power_series") (uses := "def_radius_of_convergence")
{nodetitle}[D'Alembert's ratio test for the radius of convergence]

Suppose that for the coefficients of a power series
$$`
\begin{align*}
  \sum_{n=0}^\infty a_n \, (z-z_0)^n
\end{align*}
`
the limit
$$`
\begin{align*}
  \rho = \lim_{n \to \infty} \frac{|a_n|}{|a_{n+1}|}
\end{align*}
`
exists. Then the radius of convergence $`R` of the power series
is $`R = \rho`.
:::

:::proof "lem_ratio_test_radius_of_convergence" (uses := "lem_ratio_test")
…
:::

:::theorem "thm_hadamard_formula" (parent := "grp_power_series") (uses := "def_radius_of_convergence, def_limsup")
{nodetitle}[Hadamard's formula for the radius of convergence] {palka}[Thm VII.3.3]

Let $`z_0 \in \bC` be a point in the complex plane
and let $`a_0,a_1,a_2\ldots \in \bC` be coefficients.
The radius of convergence of a power series
$$`
\begin{align*}
  \sum_{n=0}^\infty a_n \, (z-z_0)^n
\end{align*}
`
is given by the formula
$$`
\begin{align*}
  R = \frac{1}{\limsup_{n \to \infty} \sqrt[n]{|a_n|}} ,
\end{align*}
`
with the conventions $`\frac{1}{+\infty}=0` and $`\frac{1}{0} = +\infty`.
:::

:::proof "thm_hadamard_formula" (uses := "lem_weierstrass_test, lem_terms_tend_to_zero")
…
:::

:::lemma_ "lem_power_series_analytic" (parent := "grp_power_series") (uses := "def_power_series, def_analytic_function, thm_hadamard_formula")
{nodetitle}[Analyticity of power series] {palka}[Thm VII.3.3]

Let $`z_0 \in \bC` be a point in the complex plane
and let $`a_0,a_1,a_2\ldots \in \bC` be coefficients.
Suppose that the power series
$$`
\begin{align*}
  f(z) = \sum_{n=0}^\infty a_n \, (z-z_0)^n
\end{align*}
`
has radius of convergence $`R > 0`.
Then it defines an analytic function $`f` on the disk $`\DiskRC{R}{z_0}`.
The derivative of $`f` is given by the power series
$$`
\begin{align*}
  f'(z) = \sum_{n=1}^\infty n \, a_n \, (z-z_0)^{n-1} .
\end{align*}
`
Moreover, the coefficients $`a_k` are related to the $`k`th derivatives of $`f`
at $`z_0` through the formula
$$`
\begin{align*}
  a_k = \frac{f^{(k)}(z_0)}{k!} .
\end{align*}
`
:::

:::proof "lem_power_series_analytic" (uses := "lem_uoc_analytic_series, lem_polynomial_analytic")
…
:::

:::lemma_ "lem_power_series_uniqueness" (parent := "grp_power_series") (uses := "def_power_series")
{nodetitle}[Uniqueness of power series representation]

Suppose that two power series $`\sum_{n=0}^\infty a_n \, (z-z_0)^n`
and $`\sum_{n=0}^\infty b_n \, (z-z_0)^n`
converge in a disk $`\DiskRC{r}{z_0}` of radius $`r > 0`
and represent the same function
$$`
\begin{align*}
  \sum_{n=0}^\infty a_n \, (z-z_0)^n
  \; = \; \sum_{n=0}^\infty b_n \, (z-z_0)^n
  \qquad \text{ for } z \in \DiskRC{r}{z_0} .
\end{align*}
`
Then their coefficients must be equal:
$`a_n = b_n` for all $`n`.
:::

:::proof "lem_power_series_uniqueness" (uses := "lem_power_series_analytic")
…
:::

# Taylor series and local representation of analytic functions

:::theorem "thm_analytic_function_taylor_series" (parent := "grp_power_series") (uses := "def_power_series, def_analytic_function")
{nodetitle}[Taylor series of analytic functions] {palka}[Thm VII.3.4]

Suppose that $`f \colon U \to \bC` is an analytic function
on an open set $`U \subset \bC` which contains
a disk $`\DiskRC{r}{z_0} \subset U`.
Then the function $`f` can be represented in $`\DiskRC{r}{z_0}`
as a power series
$$`
\begin{align*}
  f(z) = \sum_{n=0}^\infty \frac{f^{(n)}(z_0)}{n!} \, (z-z_0)^n .
\end{align*}
`
Moreover, this is the unique power series centered at $`z_0`
that representats $`f` in a neighborhood of $`z_0`.
:::

:::proof "thm_analytic_function_taylor_series" (uses := "thm_cauchy_formula_derivative, lem_uniform_limit_integral, lem_power_series_analytic")
…
:::

:::theorem "thm_TFAE_ANALYTIC" (parent := "grp_power_series") (uses := "def_analytic_function, def_power_series, def_primitive")
{nodetitle}[Equivalent characterizations of analyticity]

Let $`f \colon U \to \bC` be a continuous function on an open
set $`U \subset \bC`.
Then the following are equivalent:

* $`f` is analytic on $`U`;
* for any $`z \in U` there exists a neighborhood of $`z`
  in which $`f` has a primitive;
* for any $`z \in U` there exists a neighborhood of $`z`
  in which $`f` can be represented as a convergent power series.
:::

:::proof "thm_TFAE_ANALYTIC" (uses := "thm_analytic_function_taylor_series, lem_power_series_analytic, thm_morera")
…
:::

:::lemma_ "lem_no_vanishing_of_all_order_derivatives" (parent := "grp_power_series") (uses := "def_analytic_function, lem_higher_derivatives_analytic")
{nodetitle}[No vanishing of all derivatives at a point] {palka}[Thm VIII.1.1]

Suppose that $`f \colon \Domain \to \bC` is an analytic function
on a connected open set $`\Domain \subset \bC`.
If there exists a point $`z_0 \in \Domain`
such that $`f^{(n)}(z_0) = 0` for all $`n \in \bN`, then $`f` is a constant
function.
:::

:::proof "lem_no_vanishing_of_all_order_derivatives" (uses := "thm_analytic_function_taylor_series")
…
:::

:::theorem "thm_factor_theorem_for_analytic_functions" (parent := "grp_power_series") (uses := "def_analytic_function")
{nodetitle}[Factor theorem for analytic functions] {palka}[Thm VIII.1.2]

Suppose that $`f \colon \Domain \to \bC` is a non-constant analytic function
on a connected open set $`\Domain \subset \bC`, and $`z_0 \in \Domain`
is a point where $`f(z_0) = 0`.
Then $`f` can be uniquely represented as
$$`
\begin{align*}
  f(z) = (z - z_0)^m \, g(z) \qquad \text{ for } z \in \Domain ,
\end{align*}
`
where $`m \in \bN` and $`g \colon \Domain \to \bC` is an analytic
function such that $`g(z_0) \ne 0`.
:::

:::proof "thm_factor_theorem_for_analytic_functions" (uses := "thm_analytic_function_taylor_series, lem_no_vanishing_of_all_order_derivatives")
…
:::

:::corollary "cor_analytic_local_representation" (parent := "grp_power_series") (uses := "def_analytic_function")
{nodetitle}[Local representation of analytic functions] {palka}[Cor VIII.1.3]

Suppose that $`f \colon \Domain \to \bC` is a non-constant analytic function
on a connected open set $`\Domain \subset \bC`.
Then for any $`z_0 \in \Domain`, we can write $`f` uniquely in the form
$$`
\begin{align*}
  f(z) = f(z_0) + (z - z_0)^m \, g(z) \qquad \text{ for } z \in \Domain ,
\end{align*}
`
where $`m \in \bN` and $`g \colon \Domain \to \bC` is an analytic
function such that $`g(z_0) \ne 0`.
:::

:::proof "cor_analytic_local_representation" (uses := "thm_factor_theorem_for_analytic_functions")
Apply {bpref "thm_factor_theorem_for_analytic_functions"}[] to the
function $`z \mapsto f(z) - f(z_0)`.
:::

:::theorem "thm_l_hospital_rule" (parent := "grp_power_series") (uses := "def_analytic_function")
{nodetitle}[L'Hospital's rule for analytic functions] {palka}[Thm VIII.1.4]

Let $`f` and $`g` be functions that are analytic in a neighborhood of $`z_0`
such that $`f(z_0) = 0` and $`g(z_0) = 0`. Then we have
$$`
\begin{align*}
  \lim_{z \to z_0} \frac{f(z)}{g(z)} = \lim_{z \to z_0} \frac{f'(z)}{g'(z)} ,
\end{align*}
`
understood in the sense that either both limits exist and are equal
to each other, or else neither limit exists.
:::

:::proof "thm_l_hospital_rule" (uses := "cor_analytic_local_representation")
…
:::

:::theorem "thm_discrete_mapping_theorem" (parent := "grp_power_series") (uses := "def_analytic_function")
{nodetitle}[Discrete mapping theorem] {palka}[Thm VIII.1.5]

Suppose that $`f \colon \Domain \to \bC` is a non-constant
analytic function on a connected open set $`\Domain \subset \bC`.
Then the set of zeros of $`f` is discrete, i.e., for
every $`z_0 \in \Domain` such that $`f(z_0)=0`,
there exists a $`r>0` such that $`f(z) \ne 0`
for all $`z \in \BallRC{r}{z_0} \setminus \set{z_0}`.
:::

:::proof "thm_discrete_mapping_theorem" (uses := "thm_factor_theorem_for_analytic_functions")
…
:::

:::corollary "cor_ANALYTIC_CONTINUATION" (parent := "grp_power_series") (uses := "def_analytic_function")
{nodetitle}[Principle of analytic continuation] {palka}[Cor VIII.1.6]

Let $`f, g \colon \Domain \to \bC` be two analytic functions on a connected
open set $`\Domain \subset \bC`.
If $`f(z) = g(z)` for all $`z` in
some subset of $`\Domain` which has an accumulation point in $`\Domain`,
then we have $`f(z) = g(z)` for all $`z \in \Domain`.
:::

:::proof "cor_ANALYTIC_CONTINUATION" (uses := "thm_discrete_mapping_theorem")
…
:::

# Laurent series

:::definition "def_doubly_infinite_series" (parent := "grp_power_series") (uses := "def_complex_series")
{nodetitle}[Doubly infinite series] {palka}[Sec. VII.2.1]

A doubly infinite series of complex numbers is a series of the form
$$`
\begin{align*}
  \sum_{n=-\infty}^\infty z_n
    = \cdots + z_{-2} + z_{-1} + z_0 + z_1 + z_2 + \cdots ,
\end{align*}
`
where $`\ldots, z_{-2}, z_{-1}, z_0, z_1, z_2, \ldots \in \bC`.
We say that such a series {term}[converges] to $`s \in \bC` if
for all $`\eps > 0` there exists an $`N \in \bN`
such that for all $`m_+ \ge N` and $`m_- \le -N` we have
$$`
\begin{align*}
  \Big| \sum_{n=m_-}^{m_+} z_n - s \Big| < \eps .
\end{align*}
`
:::

:::lemma_ "lem_convergence_doubly_infinite" (parent := "grp_power_series") (uses := "def_doubly_infinite_series")
{nodetitle}[Convergence of doubly infinite series] {palka}[Lem VII.2.1]

A doubly infinite series
$$`
\begin{align*}
  \sum_{n=-\infty}^\infty z_n
    = \cdots + z_{-2} + z_{-1} + z_0 + z_1 + z_2 + \cdots ,
\end{align*}
`
of complex numbers converges if and only if both the series
$`\sum_{n=0}^\infty z_n` and $`\sum_{n=1}^\infty z_{-n}` converge.
:::

:::proof "lem_convergence_doubly_infinite" (uses := "def_limit")
…
:::

:::definition "def_laurent_series" (parent := "grp_power_series") (uses := "def_doubly_infinite_series")
{nodetitle}[Laurent series] {palka}[Sec. VII.3.4]

A {term}[Laurent series] centered at $`z_0 \in \bC` is a doubly infinite series
of functions of the form
$$`
\begin{align*}
  z \mapsto & \; \sum_{n=-\infty}^\infty a_n (z - z_0)^n \\
       = & \; \cdots + \frac{a_{-2}}{(z-z_0)^2} + \frac{a_{-1}}{z-z_0}
              + a_0 + a_1 (z-z_0) + a_2 (z-z_0)^2 + \cdots .
\end{align*}
`
:::

:::lemma_ "lem_laurent_series_analytic" (parent := "grp_power_series") (uses := "def_laurent_series")
{nodetitle}[Annulus of convergence of Laurent power series] {palka}[Thm VII.3.5]

Consider a Laurent series
$$`
\begin{align*}
  f(z) = & \; \sum_{n=-\infty}^\infty a_n (z - z_0)^n .
\end{align*}
`
Denote
$$`
\begin{align*}
  \rho_- = \limsup_{n \to \infty} \sqrt[n]{|a_{-n}|}, \qquad
  \rho_+ = \Big( \limsup_{n \to \infty} \sqrt[n]{|a_{n}|} \Big)^{-1} .
\end{align*}
`
Then the series $`\sum_{n=-\infty}^\infty a_n (z - z_0)^n`
converges for all $`z` is the annulus
$$`
\begin{align*}
  \AnnRRC{\rho_-}{\rho_+}{z_0}
    := \Big\{ z \in \bC \; \Big| \; \rho_- < |z-z_0| < \rho_+ \Big\} .
\end{align*}
`
Moreover, the convergence is uniform on compact subsets
of $`\AnnRRC{\rho_-}{\rho_+}{z_0}`, and the series defines an analytic
function $`f(z)` on the annulus $`\AnnRRC{\rho_-}{\rho_+}{z_0}`.
:::

:::proof "lem_laurent_series_analytic" (uses := "lem_power_series_analytic")
…
:::

:::theorem "thm_ANALYTIC_FUNCTION_LAURENT_SERIES" (parent := "grp_power_series") (uses := "def_laurent_series, def_analytic_function")
{nodetitle}[Laurent series for analytic functions] {palka}[Thm VII.3.6]

Suppose that $`f \colon U \to \bC` is an analytic function
on an open set $`U \subset \bC` which contains
an annulus
$$`
\begin{align*}
  \AnnRRC{r_1}{r_2}{z_0} = \Big\{z \in \bC \; \Big| \; r_1 < |z - z_0| < r_2 \Big\}
\end{align*}
`
for some $`z_0 \in \bC` and $`0 \le r_1 < r_2`.
Then the function $`f` can be uniquely
represented in $`\AnnRRC{r_1}{r_2}{z_0}` as a series
$$`
\begin{align*}
  f(z) = \sum_{n=-\infty}^\infty a_n \, (z-z_0)^n ,
\end{align*}
`
where the coefficients $`a_n`, for $`n \in \bZ`, are given by
$$`
\begin{align*}
  a_n = \frac{1}{2\pi \ii}
    \oint_{\bdry \BallRC{r}{z_0}} \frac{f(z)}{(z - z_0)^{n+1}} \, \ud z
  \qquad \text{ for any } r \in (r_1, r_2) .
\end{align*}
`
:::

:::proof "thm_ANALYTIC_FUNCTION_LAURENT_SERIES" (uses := "thm_cauchy_formula_derivative, lem_uniform_limit_integral, lem_laurent_series_analytic, thm_analytic_function_taylor_series")
…
:::
