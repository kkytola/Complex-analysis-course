import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Appendix: Preliminaries from calculus" =>
%%%
file := "calculus-background"
%%%

# Differentiability

:::definition "def_differential" (uses := "def_limit, def_linear, def_interior")
{nodetitle}[Real differentiability]

Let $`m,n \in \bN`, and
let $`f \colon U \to \bR^m` be a function
defined on a subset $`U \subset \bR^n`.
A linear map $`L \colon \bR^n \to \bR^m`
is said to be a {term}[differential] of $`f`
at $`p_0 \in U` if
$$`
\begin{align*}
  f(p) = f(p_0) + L (p-p_0) + E(p-p_0)
\end{align*}
`
where the error term $`E` is small near $`p_0` in the sense that
$$`
\begin{align*}
  \lim_{p \to p_0} \frac{\| E(p-p_0) \|}{\|p-p_0\|} = 0 .
\end{align*}
`
We say that $`f` is {term}[differentiable] at $`p_0` if such
a linear map $`L` exists.

It is easy to check that the differential $`L` of $`f` at $`p_0`
is unique if $`p_0` is an interior point of $`U`;
we then denote it by $`L = \ud f (p_0)`.
:::

:::lemma_ "lem_differentiable_implies_continuous" (uses := "def_differential, def_continuous")
{nodetitle}[Differentiability implies continuity]

If a function $`f \colon U \to \bR^m`
defined on a subset $`U \subset \bR^n` is differentiable
at $`p_0 \in U`, then it is continuous at $`p_0`.
:::

:::proof "lem_differentiable_implies_continuous"
…
:::

:::lemma_ "lem_jacobian_matrix" (uses := "def_differential")
{nodetitle}[Jacobian matrix of the differential]

If a function $`f \colon U \to \bR^m`
defined on a subset $`U \subset \bR^n` is differentiable
at an interior point $`p_0` of $`U`, then it has
all first order partial derivatives at $`p_0`, and the
matrix representation of the differential $`\ud f (p_0)`
in the standard bases of $`\bR^m` and $`\bR^n` is
$$`
\begin{align*}
  \ud f (p_0)
    = \left[ \begin{array}{ccc}
      \frac{\partial f_1}{\partial x_1}(p_0) & \cdots & \frac{\partial f_1}{\partial x_n}(p_0) \\
      \vdots & \ddots & \vdots \\
      \frac{\partial f_m}{\partial x_1}(p_0) & \cdots & \frac{\partial f_m}{\partial x_n}(p_0)
      \end{array} \right]
    \in \bR^{m \times n} ,
\end{align*}
`
where $`f_1, \ldots, f_m \colon U \to \bR` denote component functions of $`f`.
:::

:::proof "lem_jacobian_matrix"
…
:::

:::lemma_ "lem_vanishing_partial_derivatives" (uses := "def_differential, def_open_set, def_connected")
{nodetitle}[Vanishing partial derivatives implies locally constant]

Suppose that $`f \colon U \to \bR^m` is a function
defined on an open and connected subset $`U \subset \bR^n` of $`\bR^n`
whose first order partial derivatives exist and are zero at all points
of $`U`. Then $`f` is a constant function.
:::

:::proof "lem_vanishing_partial_derivatives" (uses := "lem_open_connected_iff_path_connected")
…
:::

# Riemann integral

For the purposes of this course, it suffices to know the Riemann
integral. (Those who already know Lebesgue integration theory can
substitute that more general notion of integral everywhere.)

:::definition "def_riemann_integral"
{nodetitle}[Riemann integral]

…
:::

:::lemma_ "lem_continuous_implies_riemann_integrable" (uses := "def_riemann_integral")
{nodetitle}[Riemann integrability of continuous functions]

Any continuous function $`f \colon [a,b] \to \bR` is Riemann
integrable on $`[a,b]`.
:::

:::proof "lem_continuous_implies_riemann_integrable" (uses := "lem_on_compact_continuous_implies_uniformly_continuous, thm_bolzano_weierstrass, thm_continuous_on_compact_implies_bounded")
See {metSpCourse}[].
:::

# Trigonometry

:::lemma_ "lem_trigonometric_angle_sum"
{nodetitle}[Trigonometric angle sum identities]

Let $`\alpha, \beta \in \bR`. Then we have
$$`
\begin{align*}
  \cos (\alpha + \beta) \; = \; \cos (\alpha) \, \cos (\beta) - \sin (\alpha) \, \sin (\beta) \\
  \sin (\alpha + \beta) \; = \; \cos (\alpha) \, \sin (\beta) + \sin (\alpha) \, \cos (\beta) .
\end{align*}
`
:::

:::proof "lem_trigonometric_angle_sum"
…
:::

# Supremum, infimum, limit superior, and limit inferior

:::definition "def_supremum"
{nodetitle}[Supremum]

The {term}[supremum], or the {term}[least upper bound], of a set $`A \subset \bR`
is the smallest real number $`s` such that $`a \le s` for all $`a \in A`,
and is denoted by $`s = \sup A`.

By the completeness axiom of real numbers,
every nonempty set ($`A \ne \emptyset`) of real numbers which is bounded
from above (for some $`u \in \bR` we have $`a \le u` for all $`a \in A`)
has a supremum $`\sup A \in \bR`. We adopt the notational conventions
that $`\sup \emptyset = -\infty`, and that $`\sup A = +\infty` if $`A` is not
bounded from above.

For convenience, we also adopt some flexibility in the
notation:
for example the supremum of values of a real-valued
function on a set $`D` is denoted by
$$`
\begin{align*}
  \sup_{x \in D} f(x) \; := \; \sup \big\{ f(x) \; \big| \; x \in D \big\}
\end{align*}
`
and the supremum of values in the tail of a real-number
sequence $`(x_n)` starting from index $`m` is denoted by
$$`
\begin{align*}
  \sup_{n \ge m} x_n \; := \; \sup \big\{ x_n \; \big| \; m \ge n \big\} \, .
\end{align*}
`
:::

:::definition "def_infimum"
{nodetitle}[Infimum]

The {term}[infimum], or the {term}[greatest lower bound], of a set $`A \subset \bR`
is the greatest real number $`i` such that $`a \ge i` for all $`a \in A`,
and is denoted by $`i = \inf A`.

By the completeness axiom of real numbers,
every nonempty set ($`A \ne \emptyset`) of real numbers which is bounded
from below (for some $`\ell \in \bR` we have $`a \ge \ell` for all $`a \in A`)
has an infimum $`\inf A \in \bR`. We adopt the notational conventions
that $`\inf \emptyset = +\infty`, and that $`\inf A = -\infty` if $`A` is not
bounded from below.

For convenience, we also adopt some flexibility in the
notation for infimums of function values or sequence
values, similarly as with supremums.
:::

:::definition "def_limsup" (uses := "def_supremum")
{nodetitle}[Limit superior]

Let $`(x_n)_{n \in \bN}` be a sequence of real numbers.
Then the {term}[limit superior] of the sequence is defined as
$$`
\begin{align*}
  \limsup_{n \to \infty} x_n \; := \; \lim_{m \to \infty} \Big( \sup_{n \ge m} x_n \Big) .
\end{align*}
`

With the following conventions, the limit superior of a sequence always exists
as either a real number or one of the symbols $`\pm\infty`.
If the sequence is not bounded from above, then by
conventions regarding the supremum, we have
$`\sup_{n \ge m} x_n = +\infty` for every $`m`, so we correspondingly
set $`\limsup_{n \to \infty} x_n = +\infty`.
Otherwise the sequence $`(\sup_{n \ge m} x_n)_{m \in \bN}`
is a decreasing sequence of real numbers, so either it is
bounded from below and converges to
$`\lim_{m \to \infty} \big( \sup_{n \ge m} x_n \big) \, = \, \inf_{m \in \bN} \big( \sup_{n \ge m} x_n \big) \in \bR`,
or it is not bounded from below and we set
$`\limsup_{n \to \infty} x_n \, = \, \inf_{m \in \bN} \big( \sup_{n \ge m} x_n \big) = -\infty`.
:::

:::definition "def_liminf" (uses := "def_infimum")
{nodetitle}[Limit inferior]

Let $`(x_n)_{n \in \bN}` be a sequence of real numbers.
Then the {term}[limit inferior] of the sequence is defined as
$$`
\begin{align*}
  \liminf_{n \to \infty} x_n \; := \; \lim_{m \to \infty} \Big( \inf_{n \ge m} x_n \Big) .
\end{align*}
`

With the following conventions, the limit inferior of a sequence always exists
as either a real number or one of the symbols $`\pm \infty`.
If the sequence is not bounded from below, then by
conventions regarding the infimum, we have
$`\inf_{n \ge m} x_n = -\infty` for every $`m`, so we correspondingly
set $`\liminf_{n \to \infty} x_n = -\infty`.
Otherwise the sequence $`(\inf_{n \ge m} x_n)_{m \in \bN}`
is an increasing sequence of real numbers, so either it is
bounded from above and converges to
$`\lim_{m \to \infty} \big( \inf_{n \ge m} x_n \big) \, = \, \sup_{m \in \bN} \big( \inf_{n \ge m} x_n \big) \in \bR`,
or it is not bounded from above and we set
$`\liminf_{n \to \infty} x_n \, = \, \sup_{m \in \bN} \big( \inf_{n \ge m} x_n \big) = +\infty`.
:::

:::lemma_ "lem_limit_with_limsup_liminf" (uses := "def_limsup, def_liminf, def_limit")
{nodetitle}[Limit with limsup and liminf]

Let $`(x_n)_{n \in \bN}` be a sequence of real numbers, and let $`x \in \bR`.
Then the following are equivalent:

* The limit $`\lim_{n \to \infty} x_n` exists and equals $`x`.
* We have both $`\limsup_{n \to \infty} x_n = x` and
  $`\liminf_{n \to \infty} x_n = x`.

(With the usual conventions of $`\pm\infty` as possible limits of real-number sequences,
the above equivalence of conditions also extends to the cases $`x = \pm \infty`.)
:::

:::proof "lem_limit_with_limsup_liminf"
…
:::
