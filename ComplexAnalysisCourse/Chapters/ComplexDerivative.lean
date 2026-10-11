import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Complex derivatives and analytic functions" =>
%%%
file := "complex-derivative"
%%%

# Real linear maps versus complex linear maps

The right abstract way of understanding the differential of a function is as a linear
approximation to a function locally. The key difference between real analysis and
complex analysis is whether one uses real linear maps or complex linear maps.

:::definition "def_linear"
{nodetitle}[Linear map]

Let $`\bK` be a field (for example $`\bK = \bR` or $`\bK = \bC`), and let
$`V` and $`W` be vector spaces over $`\bK`. A function $`L : V \to W` is
said to be {term}[$`\bK`-linear] if
$$`
\begin{align*}
  L(v_1 + v_2) = \; & L(v_1) + L(v_2) & & \text{ for all } v_1, v_2 \in V, \\
  L(c v) = \; & c \, L(v) & & \text{ for all } v \in V, c \in \bK .
\end{align*}
`
Such a function $`L` is also called a {term}[$`\bK`-linear map] (or a
{term}[$`\bK`-linear transformation]) between the spaces $`V` and $`W`.
:::

The complex plane $`\bC \cong \bR^2` can be seen either as a 2-dimensional real vector space
or as a $`1`-dimensional complex vector space. In particular, it makes sense to talk about
both $`\bR`-linear maps $`\bC \to \bC` and $`\bC`-linear maps $`\bC \to \bC`.

More generally, any complex vector space can be seen as a real vector space
(of twice the same dimension), and any complex linear map becomes a real linear map.
The converse is not true! Let us elaborate on this in a simple example which
will soon be seen to pertain to the difference of complex differentiability
and real differentiability.

*Remark:* Identifying $`\bC = \bR^2` (and choosing basis vectors $`1, \ii \in \bC`
for $`\bC` seen as a 2-dimensional vector space), we see that an
$`\bR`-linear map $`L : \bC \to \bC` can be encoded in a $`2 \times 2` matrix with real entries,
$$`
\begin{align*}
  M = \left[ \begin{array}{cc} a & b \\ c & d \end{array} \right] \in \bR^{2 \times 2}
\end{align*}
`
in such a way that
$$`
\begin{align*}
  L (x + \ii y) = (a x + b y) + \ii (c x + d y) .
\end{align*}
`

*Remark:* A $`\bC`-linear map $`L : \bC \to \bC` can be encoded in a single complex number
$`\lambda \in \bC` (or more pedantically, in a $`1 \times 1` matrix $`[\lambda] \in \bC^{1 \times 1}`),
in such a way that
$$`
\begin{align*}
  L z = \lambda z .
\end{align*}
`
We can write $`\lambda = \alpha + \ii \beta`, with
$`\alpha = \re(\lambda), \beta = \im(\lambda) \in \bR`. We can also write $`z = x + \ii y`
and obtain the expression
$$`
\begin{align*}
  L (x + \ii y) = (\alpha + \ii \beta) (x + \ii y)
    = (\alpha x - \beta y) + \ii (\beta x + \alpha y) .
\end{align*}
`
In other words, seen as a real-linear map, the complex multiplication by $`\lambda`
corresponds to the matrix
$$`
\begin{align*}
  M = \left[ \begin{array}{cc} \alpha & -\beta \\ \beta & \alpha \end{array} \right] .
\end{align*}
`
This clearly shows that not every real-linear map $`\bC \to \bC` is complex linear.
It also gives an explicit set of equations for the entries of
the matrix of a real-linear map characterizing complex-linearity, which turn out to be
very closely related to the Cauchy-Riemann equations.

:::lemma_ "lem_complex_linear_vs_real_linear" (uses := "def_linear, thm_complex_number_field")
{nodetitle}[Complex linear versus real linear maps of $`\bC`]

Let $`L : \bC \to \bC` be a $`\bR`-linear map represented in the basis $`1,\ii` by
the matrix $`M = \left[ \begin{array}{cc} a & b \\ c & d \end{array} \right] \in \bR^{2 \times 2}`.
Then the following are equivalent:

* $`L` is $`\bC`-linear;
* $`b = - c` and $`a = d`.
:::

:::proof "lem_complex_linear_vs_real_linear"
Clear from the above discussion.
:::

# Complex derivative

:::definition "def_complex_derivative" (uses := "thm_complex_number_field, def_limit")
{nodetitle}[Complex derivative] {palka}[Sec. III.1.1]

Let $`f \colon A \to \bC` be a complex-valued function defined on
a subset $`A \subset \bC` of the complex plane, and let $`z_0 \in A`
be an interior point of the subset.

The $`f` is said to have
a {term}[complex derivative]
$$`
\begin{align*}
  f'(z_0) := \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}
\end{align*}
`
at $`z_0`, if the limit on the right hand side above exists.

(In complex analysis we often drop the epithet “complex” above,
and simply call $`f'(z_0)` the {term}[derivative] of $`f` at $`z_0`.)
:::

:::lemma_ "lem_local_linear_approximation" (uses := "def_complex_derivative")
{nodetitle}[Local linear approximation]

If a function $`f \colon A \to \bC` has complex derivative
$`f'(z_0) = \lambda \in \bC` at a point $`z_0 \in A`, then
we can write a linear approximation
$$`
\begin{align*}
  f(z) = f(z_0) + (z - z_0) \, \lambda + \epsilon(z) ,
\end{align*}
`
where the error term $`\epsilon` is small near $`z_0` in the sense that
$`\lim_{z \to z_0} \frac{\epsilon(z)}{|z-z_0|} = 0`.
:::

:::proof "lem_local_linear_approximation"
…
:::

:::lemma_ "lem_complex_derivative_implies_continuous" (uses := "def_continuous, def_complex_derivative")
{nodetitle}[Complex differentiability implies continuity] {palka}[Sec. III.1.1]

If a function $`f \colon A \to \bC` has a complex derivative $`f'(z_0)`
at a point $`z_0 \in A`, then it is continuous at $`z_0`.
:::

:::proof "lem_complex_derivative_implies_continuous" (uses := "lem_differentiable_implies_continuous")
…
:::

# Cauchy-Riemann equations

:::lemma_ "lem_complex_derivative_implies_differentiable" (uses := "def_complex_derivative, def_differential, lem_complex_linear_vs_real_linear")
{nodetitle}[Complex derivative implies differentiability]

Let $`f \colon A \to \bC` be a function defined on a set $`A \subset \bC`,
and let $`u \colon A \to \bR` and $`v \colon A \to \bR` be its
real and imaginary parts, viewed as real-valued functions of two real variables,
$`u(x,y) = \re \big( f (x + \ii y) \big)` and
$`v(x,y) = \im \big( f (x + \ii y) \big)`,
so that $`f = u + \ii \, v`.
If $`f` has a complex derivative $`f'(z_0)` at an interior
point $`z_0 = x_0 + \ii y_0 \in A`, then $`u` and $`v` are differentiable
at $`(x_0,y_0)` and their partial derivatives satisfy the
{term}[Cauchy-Riemann equations]
$$`
\begin{align*}
  \pderof{u}{x}(x_0,y_0) = \pderof{v}{y}(x_0,y_0)
  \quad \text{and} \quad
  \pderof{u}{y}(x_0,y_0) = - \pderof{v}{x}(x_0,y_0).
\end{align*}
`

(These equations are equivalent to the differential
$`\ud f (x_0, y_0) \colon \bR^2 \to \bR^2`
being $`\bC`-linear when we identify $`\bR^2 = \bC`.)

We can then write the derivative at $`z_0` in any of the following ways:
$$`
\begin{align*}
  f'(z_0) \, = \; & \pderof{u}{x}(x_0,y_0) + \ii \, \pderof{v}{x}(x_0,y_0)
  = \pderof{v}{y}(x_0,y_0) - \ii \, \pderof{u}{y}(x_0,y_0) \\
  = \; & \pderof{u}{x}(x_0,y_0) - \ii \, \pderof{u}{y}(x_0,y_0)
  = \pderof{v}{y}(x_0,y_0) + \ii \, \pderof{v}{x}(x_0,y_0) .
\end{align*}
`
:::

:::proof "lem_complex_derivative_implies_differentiable" (uses := "lem_local_linear_approximation, lem_jacobian_matrix")
…
:::

## Differentiation rules

:::lemma_ "lem_derivative_linearity" (uses := "def_complex_derivative, def_linear")
{nodetitle}[Linearity of the derivative] {palka}[Sec. III.1.2 (3.4)]

If two functions $`f, g \colon A \to \bC` have complex derivatives
$`f'(z_0), g'(z_0)` at a point $`z_0 \in A`, then the sum function $`f + g`
has a complex derivative at $`z_0` given by
$$`
\begin{align*}
  (f + g)'(z_0) = f'(z_0) + g'(z_0) .
\end{align*}
`
If a function $`f \colon A \to \bC` is has a complex derivative
$`f'(z_0)` at a point $`z_0 \in A` and $`c \in \bC` is a complex number,
then the function $`c f` has complex derivative
$$`
\begin{align*}
  (c f)'(z_0) = c \, f'(z_0)
\end{align*}
`
at $`z_0`.
:::

:::proof "lem_derivative_linearity" (uses := "lem_complex_limit_properties")
…
:::

:::lemma_ "lem_leibniz_rule" (uses := "def_complex_derivative")
{nodetitle}[Leibniz rule] {palka}[Sec. III.1.2 (3.4)]

If two functions $`f, g \colon A \to \bC` have complex derivatives
$`f'(z_0), g'(z_0)` at a point $`z_0 \in A`, then the product function $`f g`
has complex derivative
$$`
\begin{align*}
  (f g)'(z_0) = f'(z_0) \, g(z_0) + f(z_0) \, g'(z_0)
\end{align*}
`
at $`z_0`.
:::

:::proof "lem_leibniz_rule"
…
:::

:::lemma_ "lem_quotient_derivative" (uses := "def_complex_derivative")
{nodetitle}[Derivative of a quotient] {palka}[Sec. III.1.2 (3.4)]

If two functions $`f, g \colon A \to \bC` have complex derivatives
$`f'(z_0), g'(z_0)` at a point $`z_0 \in A` and $`g(z_0) \ne 0`, then
the quotient function $`f / g` has complex derivative
$$`
\begin{align*}
  \left( \frac{f}{g} \right)'(z_0)
    = \frac{f'(z_0) \, g(z_0) - f(z_0) \, g'(z_0)}{g(z_0)^2} .
\end{align*}
`
at $`z_0`.
:::

:::proof "lem_quotient_derivative"
…
:::

:::lemma_ "lem_chain_rule" (uses := "def_complex_derivative")
{nodetitle}[Chain rule] {palka}[Thm III.1.1]

If $`f \colon A \to B \subset \bC` is differentiable at $`z_0 \in A`
and $`g \colon B \to \bC` is differentiable at $`f(z_0) \in B`,
then the composition $`g \circ f \colon A \to \bC` is differentiable at $`z_0`,
with derivative
$$`
\begin{align*}
  (g \circ f)'(z_0) = f'(z_0) \; g'\big( f(z_0) \big) .
\end{align*}
`
:::

:::proof "lem_chain_rule"
…
:::

:::lemma_ "lem_inverse_derivative" (uses := "def_complex_derivative")
{nodetitle}[Derivative of inverse] {palka}[Thm III.4.1]

Suppose that $`f` is a complex-valued function defined on a subset of
the complex plane, which has a nonzero complex derivative $`f'(z_0) \ne 0`
at a point $`z_0` and which has a local inverse function near $`z_0` in the
sense that there are open sets $`U, V \subset \bC` with $`z_0 \in U`
and $`f(z_0) \in V`, and the restriction of $`f` to $`U`
is continuous $`U \to V` with a continuous inverse. Then
the local inverse function $`f^{-1} \colon V \to U` has complex derivative
at $`w_0 := f(z_0)` given by
$$`
\begin{align*}
  (f^{-1})'(w_0) = \frac{1}{f'(z_0)} .
\end{align*}
`
:::

:::proof "lem_inverse_derivative" (uses := "lem_chain_rule")
…
:::

## Analytic functions

:::definition "def_analytic_function" (uses := "def_complex_derivative, def_open_set")
{nodetitle}[Analytic function] {palka}[Sec. III.1.3]

A function $`f \colon U \to \bC` defined on an open set $`U \subset \bC` is
said to be {term}[analytic] (or {term}[holomorphic]) if it is complex
differentiable at every point $`z_0 \in U`.
:::

:::theorem "thm_cauchy_riemann" (uses := "def_analytic_function")
{nodetitle}[Cauchy-Riemann equations] {palka}[Thm III.2.2]

Let $`f \colon U \to \bC` be a function defined on an open set $`U \subset \bC`,
and let $`u \colon U \to \bR` and $`v \colon U \to \bR` be its
real and imaginary parts, viewed as real-valued functions of two real variables,
$$`
\begin{align*}
  u(x,y) = \re \Big( f (x + \ii y) \Big)
  \quad \text{and} \quad
  v(x,y) = \im \Big( f (x + \ii y) \Big)
\end{align*}
`
so that $`f = u + \ii \, v`.

Then the following are equivalent:

* The functions $`u` and $`v` are differentiable at every point in $`U`
  and their partial derivatives satisfy the {term}[Cauchy-Riemann equations]
  $$`
  \begin{align*}
    \pderof{u}{x} = \pderof{v}{y}
    \quad \text{and} \quad
    \pderof{u}{y} = - \pderof{v}{x}
  \end{align*}
  `
  in $`U`.
* The function $`f` is analytic.
:::

:::proof "thm_cauchy_riemann" (uses := "lem_complex_derivative_implies_differentiable")
…
:::

:::lemma_ "lem_analytic_implies_continuous" (uses := "def_analytic_function, def_continuous")
{nodetitle}[Analytic functions are continuous]

Every function $`f \colon U \to \bC` which is analytic on
an open set $`U \subset \bC` is also continuous on $`U`.
:::

:::proof "lem_analytic_implies_continuous" (uses := "lem_complex_derivative_implies_continuous")
…
:::

:::lemma_ "lem_polynomial_analytic" (uses := "def_polynomial, def_analytic_function")
{nodetitle}[Polynomials are analytic]

Every polynomial function $`p \colon \bC \to \bC` is analytic.
:::

:::proof "lem_polynomial_analytic" (uses := "lem_derivative_linearity, lem_leibniz_rule")
…
:::

:::lemma_ "lem_rational_function_analytic" (uses := "def_rational_function, def_analytic_function")
{nodetitle}[Rational functions are analytic]

Every rational function $`f \colon U \to \bC` is analytic
on its domain of definition $`U \subset \bC`.
:::

:::proof "lem_rational_function_analytic" (uses := "lem_polynomial_analytic, lem_quotient_derivative")
…
:::

:::lemma_ "lem_exp_analytic" (uses := "def_complex_exp, def_analytic_function")
{nodetitle}[The complex exponential is analytic]

The complex exponential function $`\exp \colon \bC \to \bC` is analytic.
Its (complex) derivative at $`z \in \bC` is $`\exp'(z) = \exp(z)`.
:::

:::proof "lem_exp_analytic" (uses := "thm_cauchy_riemann")
…
:::

:::lemma_ "lem_root_function_analytic" (uses := "def_analytic_function, def_principal_complex_nth_root")
{nodetitle}[Branches of $`n`th root functions are analytic]

The principal branch of the $`n`th root function
$`z \mapsto \sqrt[n]{z}` is analytic on its domain
$`\bC \setminus (-\infty,0]`.

(Different branch choices can be made to obtain analyticity on
other domains, but for $`n \ge 2`,
no branch of $`\sqrt[n]{z}` can be made analytic on all of $`\bC`.)
:::

:::proof "lem_root_function_analytic" (uses := "lem_inverse_derivative")
…
:::

## Consequences of Cauchy-Riemann equations

:::lemma_ "lem_zero_derivative_implies_constant" (uses := "def_analytic_function")
{nodetitle}[Analytic functions of vanishing derivative]

Suppose that $`f \colon D \to \bC` is a analytic function
on a connected open subset $`D \subset \bC` of the complex plane
such that $`f'(z) = 0` for all $`z \in D`.
Then $`f` is a constant function.
:::

:::proof "lem_zero_derivative_implies_constant" (uses := "thm_cauchy_riemann, lem_vanishing_partial_derivatives")
…
:::

:::theorem "thm_constantness_criteria" (uses := "def_analytic_function")
{nodetitle}[Criteria for constantness of a analytic function]

Suppose that $`f \colon D \to \bC` is a analytic function
on a connected open subset $`D \subset \bC` of the complex plane.
If any of the functions $`u = \re(f) \colon D \to \bR`,
$`v = \im(f) \colon D \to \bR`, $`|f| \colon D \to \bR`,
is constant on $`D`, then $`f` is itself a constant function.
:::

:::proof "thm_constantness_criteria" (uses := "thm_cauchy_riemann, lem_zero_derivative_implies_constant")
…
:::

:::lemma_ "lem_real_and_imaginary_parts_harmonic" (uses := "def_analytic_function")
{nodetitle}[Harmonicity of real and imaginary parts]

Suppose that $`f \colon U \to \bC` is a analytic function
on an open subset $`U \subset \bC` of the complex plane.
Let $`u,v \colon U \to \bR` denote the real and imaginary
parts of $`f` defined by $`u(x,y) = \re \big( f(x + \ii y)\big)`
and $`v(x,y) = \im \big( f(x + \ii y)\big)`. Assume
moreover that that $`u` and $`v` are twice continuously differentiable
(later it will be shown that this assumption holds automatically
by the analyticity of $`f`).
Then $`u` and $`v` are {term}[harmonic functions],
i.e., they satisfy
$$`
\begin{align*}
  \triangle u = 0 \qquad \text{ and } \qquad \triangle v = 0 ,
  \qquad \text{ where} \qquad
  \triangle = \pdder{x} + \pdder{y} .
\end{align*}
`
:::

:::proof "lem_real_and_imaginary_parts_harmonic" (uses := "thm_cauchy_riemann")
…
:::

:::definition "def_harmonic_conjugate" (uses := "def_analytic_function, lem_real_and_imaginary_parts_harmonic")
{nodetitle}[Harmonic conjugate]

Suppose that $`u \colon U \to \bR` is harmonic function
on an open subset $`U \subset \bR^2`, i.e., a twice continuously
differentiable function satisfying $`\pdder{x} u + \pdder{y} u = 0`
on $`U`. A function $`v \colon U \to \bR` is called a
{term}[harmonic conjugate] of $`u` if the function
$$`
\begin{align*}
  x + \ii y \; \mapsto \; u(x,y) + \ii \, v(x,y)
\end{align*}
`
is analytic on $`U`.
:::

:::lemma_ "lem_harmonic_conjugate_existence" (uses := "def_harmonic_conjugate, lem_real_and_imaginary_parts_harmonic")
{nodetitle}[Local existence of harmonic conjugates]

Let $`B = \BallRC{r}{z_0} \subset \bC` be a disk in the complex plane.
Suppose that $`u \colon B \to \bR` is harmonic function on $`B`. Then a
harmonic conjugate $`v \colon B \to \bR` of $`u` in the disk $`B` exists and
is unique up to an additive constant.
:::

:::proof "lem_harmonic_conjugate_existence" (uses := "thm_cauchy_riemann")
…
:::
