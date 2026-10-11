import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Contour integration" =>
%%%
file := "contour-integration"
%%%

# Complex-valued integrals

:::definition "def_complex_valued_integral" (uses := "def_riemann_integral, lem_continuous_complex, lem_continuous_implies_riemann_integrable")
{nodetitle}[Integral of a complex-valued function]

Let $`f \colon [a,b] \to \bC` be a complex-valued continuous function
defined on a closed interval $`[a,b] \subset \bR`. We define the
{term}[integral] of $`f` as
$$`
\begin{align*}
  \int_a^b f(t) \, \ud t
    \; = \; \int_a^b \re \big( f(t) \big) \, \ud t
            \; + \; \ii \int_a^b \im \big( f(t) \big) \, \ud t .
\end{align*}
`

(Note that on the right hand side we have just Riemann integrals
of the continuous real-valued functions $`t \mapsto \re \big( f(t) \big)`
and $`t \mapsto \im \big( f(t) \big)`.)
:::

:::lemma_ "lem_linearity_of_complex_integral" (uses := "def_complex_valued_integral, def_linear")
{nodetitle}[Complex linearity of complex-valued integrals]

If $`f, g \colon [a,b] \to \bC` are complex-valued continuous
functions defined on a closed interval $`[a,b] \subset \bR`,
then the integral of their sum is
$$`
\begin{align*}
  \int_a^b \big( f(t) + g(t) \big) \, \ud t
    \; = \; \int_a^b f(t) \, \ud t + \int_a^b g(t) \, \ud t .
\end{align*}
`

If $`f \colon [a,b] \to \bC` is a complex-valued continuous
function defined on a closed interval $`[a,b] \subset \bR`,
and $`\lambda \in \bC` is a complex number, then the integral of
the scalar multiple of $`f` is
$$`
\begin{align*}
  \int_a^b \lambda \, f(t) \, \ud t
    \; = \; \lambda \int_a^b f(t) \, \ud t .
\end{align*}
`
:::

:::proof "lem_linearity_of_complex_integral"
…
:::

:::lemma_ "lem_ftc_for_complex_valued_integrals" (uses := "def_complex_valued_integral")
{nodetitle}[Fundamental theorem of calculus for complex-valued integrals]

Suppose that $`f \colon [a,b] \to \bC` is a continuously differentiable
complex-valued function on a closed interval $`[a,b] \subset \bR`.
Denote its derivative by $`\dot{f}(t) = \frac{\ud}{\ud t} f(t)`.
Then for the integral of the derivative of $`f` we have
$$`
\begin{align*}
  \int_a^b \dot{f}(t) \, \ud t \; = \; f(b) - f(a) .
\end{align*}
`
:::

:::proof "lem_ftc_for_complex_valued_integrals"
…
:::

# Paths in the complex plane

:::definition "def_path" (uses := "def_continuous")
{nodetitle}[Path] {palka}[Sec. IV.1.1]

A {term}[path] in the complex plane is a continuous function $`\gamma \colon [a,b] \to \bC`
from a closed interval $`[a,b] \subset \bR` to $`\bC`.

When $`A \subset \bC` is a subset of the complex plane, we say that $`\gamma` is a path in $`A`
if $`\gamma(t) \in A` for all $`t \in [a,b]`.

If the starting point and the end point of the path $`\gamma` are the same,
$`\gamma(a) = \gamma(b)`, then we say that $`\gamma` is a {term}[closed path].

We sometimes want to disregard the parametrization, and view a path
$`\gamma \colon [a,b] \to \bC` as a subset of the complex plane.
This subset is the range
$`\big\{ \gamma(t) \, \big| \, t \in [a,b] \big\} \subset \bC` of the
parametrizing function, but with a slight abuse of notation we often just
write $`\gamma \subset \bC` also for this subset.

(Note that the subset $`\gamma \subset \bC` is compact, by continuity of
$`\gamma \colon [a,b] \to \bC` and compactness of $`[a,b]`.)
:::

:::definition "def_smooth_path" (uses := "def_path, def_continuous")
{nodetitle}[Smooth path] {palka}[Sec. IV.1.2]

A path $`\gamma \colon [a,b] \to \bC` is {term}[smooth]
if it is continuously differentiable, i.e., the derivative
$$`
\begin{align*}
  \dot{\gamma}(t) = \frac{\ud}{\ud t} \gamma(t)
\end{align*}
`
with respect to the parameter $`t`
exists for all $`t \in [a,b]` (one-sided derivatives at the interval
end points $`a` and $`b`),
and defines a continuous complex-valued function $`t \mapsto \dot{\gamma}(t)`
on $`[a,b]`.
:::

:::definition "def_contour" (uses := "def_smooth_path, def_continuous")
{nodetitle}[Contour / piecewise smooth path] {palka}[Sec. IV.1.2]

A {term}[contour] (also called a {term}[piecewise smooth path])
is a continuous function $`\gamma \colon [a,b] \to \bC`
such that for some finite subdivision $`a = t_0 < t_1 < \ldots < t_n = b`,
the restrictions $`\gamma|_{[t_{j-1},t_j]}`
to the subintervals $`[t_{j-1},t_j] \subset [a,b]`
are smooth paths for each $`j = 1, \ldots, n`.

If the starting point and the end point of the contour $`\gamma` are the same,
$`\gamma(a) = \gamma(b)`, then we say that $`\gamma` is a {term}[closed contour].
:::

:::definition "def_reverse_path" (uses := "def_path")
{nodetitle}[Reverse path] {palka}[Sec. IV.1.4]

Given a path $`\gamma \colon [a,b] \to \bC`,
the {term}[reverse path] $`\opp{\gamma} \colon [a,b] \to \bC`
is the path defined by
$$`
\begin{align*}
  \opp{\gamma}(t) = \gamma(a+b-t) \qquad \text{ for } t \in [a,b] .
\end{align*}
`
:::

:::definition "def_path_concatenation" (uses := "def_path")
{nodetitle}[Concatenation of paths] {palka}[Sec. IV.1.4]

Given path $`\gamma \colon [a,b] \to \bC` and
$`\eta \colon [c,d] \to \bC` with $`\gamma(b) = \eta(c)`
(the starting point of $`\eta` coincides with the end point of $`\gamma`),
the {term}[concatenation] of $`\gamma` and $`\eta` is the path
$`\gamma \concat \eta \colon [a,b+d-c] \to \bC` defined by
$$`
\begin{align*}
  (\gamma \concat \eta)(t) =
  \begin{cases}
    \gamma(t) & \text{ for } t \in [a,b] , \\
    \eta(c+t-b)) & \text{ for } t \in [b,b+d-c] .
  \end{cases}
\end{align*}
`

(The slightly cumbersome formula in the second case is due to the fact
that we need to attach the two parameter intervals of lengths
$`b-a` and $`d-c` to each other, and we have, somewhat arbitrarily,
chosen to glue them to form the interval $`[a,b+d-c]`.)
:::

:::definition "def_path_reparametrization" (uses := "def_path, lem_continuous_bijection_homeomorphism, def_contour")
{nodetitle}[Reparametrization of paths] {palka}[Sec. IV.1.5]

Given a path $`\gamma \colon [a,b] \to \bC` and a continuous increasing
bijection $`\phi \colon [c,d] \to [a,b]`, we define the {term}[reparametrization]
of $`\gamma` by $`\phi` as the path
$$`
\begin{align*}
  \gamma \circ \phi \, \colon \, [c,d] \, \to \; & \bC \\
  t \, \mapsto \; & \gamma(\phi(t)) .
\end{align*}
`

Note that

* $`\phi^{-1} \colon [a,b] \to [c,d]` is also a continuous increasing
  bijection (a continuous bijection from the
  compact $`[a,b]` is automatically a homeomorphism; see
  {bpref "lem_continuous_bijection_homeomorphism"}[]) and
  reparametrization can be undone by rereparametrizing by $`\phi^{-1}`;
* If both $`\gamma` and the reparametrization function $`\phi` are
  smooth (continuously differentiable), then the reparametrized
  path $`\gamma \circ \phi` is also smooth;
* If both $`\gamma` and the reparametrization function $`\phi` are
  piecewise smooth, then the reparametrized path $`\gamma \circ \phi`
  is also piecewise smooth, i.e., a contour.
:::

# Integrals along paths

:::definition "def_smooth_contour_integral" (uses := "def_complex_valued_integral, def_smooth_path")
{nodetitle}[Contour integral along a smooth path] {palka}[Sec. IV.2.1]

Let $`f : A \to \bC` be a continuous function defined on a subset $`A \subset \bC`.
Let $`\gamma \colon [a,b] \to A` be a smooth path in $`A`.
We define the {term}[integral of $`f` along $`\gamma`] as
$$`
\begin{align*}
  \int_\gamma f(z) \, dz
  \; = \; \int_a^b f \big( \gamma(t) \big) \, \dot{\gamma}(t) \; \ud t .
\end{align*}
`

(Here $`\dot{\gamma}(t) = \frac{\ud}{\ud t} \gamma(t)` denotes the derivative of
the smooth path $`\gamma` with respect to its parameter $`t`.)
:::

Sometimes it is appropriate to integrate functions with respect to the
arc length in the following sense.

:::definition "def_smooth_arc_length_integral" (uses := "def_complex_valued_integral, lem_continuous_implies_riemann_integrable, def_smooth_path")
{nodetitle}[Arc length integral along a smooth path] {palka}[Sec. IV.2.1]

Let $`f : A \to \bC` be a continuous function defined on a subset $`A \subset \bC`.
Let $`\gamma \colon [a,b] \to A` be a smooth path in $`A`.
We define the {term}[integral of $`f` with respect to the arc length of $`\gamma`] as
$$`
\begin{align*}
  \int_\gamma f(z) \, |dz|
  \; = \; \int_a^b f \big( \gamma(t) \big) \, |\dot{\gamma}(t)| \; \ud t .
\end{align*}
`

(Here $`\dot{\gamma}(t) = \frac{\ud}{\ud t} \gamma(t) \in \bC` denotes the
derivative of the smooth path $`\gamma` with respect to its parameter $`t`,
and $`|\dot{\gamma}(t)| \ge 0` denotes the absolute value of this derivative.)
:::

In order to extend the definition of contour integrals to piecewise smooth paths,
we note that the definition behaves additively under path concatenation.

:::lemma_ "lem_integral_concatenation" (uses := "def_smooth_contour_integral, def_smooth_arc_length_integral, def_path_concatenation")
{nodetitle}[Contour integrals and smooth path concatenation] {palka}[Lem IV.2.1(iv)]

If a smooth path $`\gamma` in $`A` is a concatenation of smooth
paths $`\eta_1, \ldots, \eta_n`, and
$`f : A \to \bC` is a continuous function defined on $`A \subset \bC`,
then we have
$$`
\begin{align*}
  \int_\gamma f(z) \, \ud z \; = \; \sum_{j=1}^n \int_{\eta_j} f(z) \, \ud z
\end{align*}
`
and
$$`
\begin{align*}
  \int_\gamma f(z) \, |\ud z| \; = \; \sum_{j=1}^n \int_{\eta_j} f(z) \, |\ud z| .
\end{align*}
`
:::

:::proof "lem_integral_concatenation"
…
:::

By virtue of the above, the following gives a well-defined meaning
to integrals along piecewise smooth paths.

:::definition "def_contour_integral" (uses := "def_smooth_contour_integral, def_contour, lem_integral_concatenation")
{nodetitle}[Contour integral] {palka}[Sec. IV.2.1]

Let $`f : A \to \bC` be a continuous function defined on a subset $`A \subset \bC`.
Let $`\gamma \colon [a,b] \to A` be a piecewise smooth path in $`A`,
which is a concatenation of smooth paths $`\eta_1, \ldots, \eta_n`.
We define the {term}[integral of $`f` along $`\gamma`] as
$$`
\begin{align*}
  \int_\gamma f(z) \, dz \; = \; \sum_{j=1}^n \int_{\eta_j} f(z) \, dz .
\end{align*}
`
:::

:::definition "def_arc_length_integral" (uses := "def_smooth_arc_length_integral, def_contour, lem_integral_concatenation")
{nodetitle}[Arc-length integral]

Let $`f : A \to \bC` be a continuous function defined on a subset $`A \subset \bC`.
Let $`\gamma \colon [a,b] \to A` be a piecewise smooth path (i.e., a contour) in $`A`,
which is a concatenation of smooth paths $`\eta_1, \ldots, \eta_n`.
We define the {term}[integral of $`f` with respect to the arc length of $`\gamma`] as
$$`
\begin{align*}
  \int_\gamma f(z) \, |dz| \; = \; \sum_{j=1}^n \int_{\eta_j} f(z) \, |dz| .
\end{align*}
`
:::

:::definition "def_length" (uses := "def_arc_length_integral")
{nodetitle}[Length of a path or a contour]

Let $`\gamma \colon [a,b] \to \bC` be a piecewise smooth path (i.e., a contour)
in $`\bC`. The {term}[length] $`\ell(\gamma)` of $`\gamma` is defined as
$$`
\begin{align*}
  \ell(\gamma) = \int_\gamma |\ud z| .
\end{align*}
`
:::

:::lemma_ "lem_reparametrization_invariance_of_integral" (uses := "def_contour_integral, def_arc_length_integral, def_path_reparametrization")
{nodetitle}[Reparametrization invariance of integrals] {palka}[Lem IV.2.1(v)]

Let $`\gamma` be a piecewise smooth path in $`A`,
and let $`\widetilde{\gamma}` be obtained from $`\gamma` by an
orientation-preserving reparametrization. Then for any continuous
function $`f : A \to \bC` we have
$$`
\begin{align*}
  \int_{\widetilde{\gamma}} f(z) \, dz \; = \; \int_{\gamma} f(z) \, dz
\end{align*}
`
and
$$`
\begin{align*}
  \int_{\widetilde{\gamma}} f(z) \, |dz| \; = \; \int_{\gamma} f(z) \, |dz| .
\end{align*}
`
:::

:::lemma_ "lem_integral_reversal" (uses := "def_contour_integral, def_arc_length_integral, def_reverse_path")
{nodetitle}[Contour integrals and path reversal] {palka}[Lem IV.2.1(iii)]

If $`f : A \to \bC` is a continuous function defined on $`A \subset \bC`,
and $`\gamma` is a piecewise path in $`A`, then for the contour integral
and the arc length integral behave as follows under path reversal:
then we have
$$`
\begin{align*}
  \int_{\opp{\gamma}} f(z) \, \ud z \; = \; - \int_{\gamma} f(z) \, \ud z
\end{align*}
`
and
$$`
\begin{align*}
  \int_{\opp{\gamma}} f(z) \, |\ud z| \; = \; \int_{\gamma} f(z) \, |\ud z|
\end{align*}
`
:::

:::proof "lem_integral_reversal"
…
:::

:::lemma_ "lem_integral_linearity" (uses := "def_contour_integral, def_arc_length_integral, def_linear")
{nodetitle}[Linearity of integrals] {palka}[Lem IV.2.1(i-ii)]

Let $`A \subset \bC` be a subset of the complex plane let and $`\gamma \colon [a,b] \to A`
be a contour in $`A`.

If $`f, g \colon A \to \bC` are continuous
functions defined on $`A`, then the contour integral
and the arc length integral of their sum are
$$`
\begin{align*}
  \int_\gamma \big( f(z) + g(z) \big) \, \ud z
    \; = \; & \int_\gamma f(z) \, \ud z + \int_\gamma g(z) \, \ud z \\
  \int_\gamma \big( f(z) + g(z) \big) \, |\ud z|
    \; = \; & \int_\gamma f(z) \, |\ud z| + \int_\gamma g(z) \, |\ud z| .
\end{align*}
`

If $`f \colon A \to \bC` is a complex-valued continuous
function defined on $`A`,
and $`\lambda \in \bC` is a complex number, then the contour
integral and the arc length integral of the scalar multiple of $`f` are
$$`
\begin{align*}
  \int_\gamma \lambda \, f(z) \, \ud z
    \; = \; & \lambda \int_\gamma f(z) \, \ud z \\
  \int_\gamma \lambda \, f(z) \, |\ud z|
    \; = \; & \lambda \int_\gamma f(z) \, |\ud z| .
\end{align*}
`
:::

:::proof "lem_integral_linearity" (uses := "lem_linearity_of_complex_integral")
…
:::

:::lemma_ "lem_integral_triangle_inequality" (uses := "def_contour_integral, def_arc_length_integral")
{nodetitle}[Triangle inequality for contour integrals] {palka}[Lem IV.2.1(vi)]

Let $`f : A \to \bC` be a continuous function defined on $`A \subset \bC`,
and let $`\gamma` be a contour in $`A`. Then we have
$$`
\begin{align*}
  \left| \int_\gamma f(z) \, \ud z \right| \; \le \; \int_\gamma |f(z)| \, |dz| .
\end{align*}
`
:::

:::proof "lem_integral_triangle_inequality"
…
:::

:::corollary "lem_contour_integral_bound" (uses := "def_contour_integral, def_length")
{nodetitle}[An a priori bound for contour integrals]

Let $`f : A \to \bC` be a continuous function defined on $`A \subset \bC`,
and let $`\gamma` be a contour in $`A`.
Assume that $`|f(z)| \le M` for all points $`z` on the contour $`\gamma`.
Then we have
$$`
\begin{align*}
  \left| \int_\gamma f(z) \, \ud z \right| \; \le \; M \, \ell(\gamma) ,
\end{align*}
`
where $`\ell(\gamma) = \int_\gamma |\ud z|` denotes the length of
the contour $`\gamma`.
:::

:::proof "lem_contour_integral_bound" (uses := "lem_integral_triangle_inequality")
…
:::

The following slightly technical auxiliary result will only be used later
(for winding number properties and for Cauchy's formula for the derivative).
But since the result only requires contour integration,
the natural logical place for it is here. Also, strictly speaking, we
only need the cases $`k = 1` and $`k = 2` in this lemma; but including
general $`k \in \bN` gives the quickest route to Cauchy's formula for
higher order derivatives.

:::lemma_ "lem_derivative_auxiliary_integral" (uses := "def_contour_integral, def_analytic_function")
{palka}[Lemma V.1.6]

Let $`\gamma` be a contour in $`\bC`, and let $`h \colon \gamma \to \bC`
be a continuous function on the contour (we slightly abuse the notation
here to identify the contour as a subset $`\gamma \subset \bC`).
Let $`k \in \bN` be a positive integer.
Define $`H \colon \bC \setminus \gamma \to \bC` by
$$`
\begin{align*}
  H(z) = \int_\gamma \frac{h(\zeta)}{(\zeta - z)^{k}} \, \ud \zeta .
\end{align*}
`
Then $`H` is analytic on $`\bC \setminus \gamma`, and its derivative
at $`z \in \bC \setminus \gamma` is given by
$$`
\begin{align*}
  H'(z) = k \, \int_\gamma \frac{h(\zeta)}{(\zeta - z)^{k+1}} \, \ud \zeta .
\end{align*}
`
:::

:::proof "lem_derivative_auxiliary_integral" (uses := "lem_contour_integral_bound")
…
:::

# Primitives

:::definition "def_primitive" (uses := "def_analytic_function")
{nodetitle}[Primitive of a function] {palka}[Sec. IV.2.3]

Let $`f : U \to \bC` be a function defined on an open subset $`U \subset \bC`.
A {term}[primitive] of $`f` is a function $`F : U \to \bC` such that
$`F` is analytic (i.e., complex differentiable) on $`U`,
$$`
\begin{align*}
  F'(z) = f(z) \qquad \text{ for all } z \in U .
\end{align*}
`
:::

:::theorem "thm_ftc_for_contour_integrals" (uses := "def_primitive, def_contour_integral")
{nodetitle}[Fundamental theorem of calculus for contour integrals] {palka}[Thm IV.2.2]

Suppose that $`f \colon U \to \bC` is a continuous function
on an open set $`U \subset \bC`, and that $`f` has a
primitive $`F \colon U \to \bC`.
Then for any contour $`\gamma \colon [a,b] \to U` we have
$$`
\begin{align*}
  \int_\gamma f(z) \, dz \; = \; F \big( \gamma(b) \big) - F \big( \gamma(a) \big) .
\end{align*}
`
In particular for any closed contour $`\gamma` in $`U`, we have
$$`
\begin{align*}
  \oint_\gamma f(z) \, dz \; = \; 0 .
\end{align*}
`
:::

:::proof "thm_ftc_for_contour_integrals" (uses := "lem_ftc_for_complex_valued_integrals")
…
:::

:::lemma_ "lem_monomial_primitive" (uses := "def_primitive, def_polynomial, def_rational_function")
{nodetitle}[Existence of primitives for monomials]

For $`n \in \set{0,1,2,\ldots}`, the monomial
function $`f(z) = z^n` has a primitive
$`F(z) = \frac{1}{n+1} z^{n+1} + c` (with $`c \in \bC` arbitrary)
in the whole complex plane $`\bC`.

For $`n \in \set{-2,-3,-4,\ldots}`, the monomial
function $`f(z) = z^n` has a primitive
$`F(z) = \frac{1}{n+1} z^{n+1} + c` (with $`c \in \bC` arbitrary)
in the punctured complex plane $`\bC \setminus \set{0}`.

The monomial function $`f(z) = z^{-1} = \frac{1}{z}` does not have
a primitive in the punctured complex plane $`\bC \setminus \set{0}`.
:::

:::proof "lem_monomial_primitive" (uses := "thm_ftc_for_contour_integrals")
…
:::

:::theorem "thm_primitive_characterization" (uses := "def_primitive")
{nodetitle}[Characterization of the existence of primitives]

Let $`f \colon U \to \bC` be a continuous function on an open
set $`U \subset \bC`. Then the following conditions are equivalent:

* (a) $`f` has a primitive on $`U`;
* (b) the contour integrals $`\int_\gamma f(z) \, \ud z`
  of $`f` along contours $`\gamma` in $`U` only depend on the
  starting point and the end point of $`\gamma`;
* (c) for all closed contours $`\gamma` in $`U` we have
  $`\oint_\gamma f(z) \, \ud z = 0`.
:::

:::proof "thm_primitive_characterization" (uses := "thm_ftc_for_contour_integrals")
…
:::
