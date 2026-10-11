import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Appendix: Topological preliminaries" =>
%%%
file := "topology-background"
%%%

:::group "grp_topology_background"
Topological preliminaries
:::

# Metrics and related concepts

:::definition "def_metric_space" (parent := "grp_topology_background")
{nodetitle}[Metric]

A {term}[metric] on a set $`X` is a function
$`\genmet \colon X \times X \to [0,\infty)` such that
for all $`p_1, p_2, p_3 \in X` we have
$$`
\begin{align*}
  \genmet(p_1, p_3) \le \; & \genmet(p_1,p_2) + \genmet(p_2,p_3)
          & \text{(triangle inequality)} \\
  \genmet(p_1, p_2) = \; & \genmet(p_2,p_1)
          & \text{(symmetricity)} \\
  \genmet(p_1, p_2) = \; & 0 \text{ if and only if } p_1 = p_2 .
          & \text{(separation of points)}
\end{align*}
`
The set $`X` equipped with the metric $`\genmet` on
it is called a {term}[metric space].
:::

:::lemma_ "lem_metric_on_C" (parent := "grp_topology_background") (uses := "def_metric_space, def_absolute_value")
{nodetitle}[Metric in the complex plane]

The formula
$$`
\begin{align*}
  \genmet(z,w) = |z - w|
  \qquad \text{ for } z,w \in \bC
\end{align*}
`
defines a metric on the complex plane $`\bC`.

(Thus $`\bC` becomes a metric space. Also any subset of $`\bC`,
in particular $`\bR \subset \bC`, becomes a metric space when equipped
with the metric given by the above formula restricted to the subset.)
:::

:::proof "lem_metric_on_C" (uses := "lem_absolute_value_properties")
…
:::

:::definition "def_ball" (parent := "grp_topology_background") (uses := "def_metric_space")
{nodetitle}[Ball (disk)]

Let $`X` be a metric space with metric $`\genmet \colon X \times X \to [0,\infty)`.
Let $`p_0 \in X` be a point and let $`r>0`.

The set
$$`
\begin{align*}
  \BallRC{r}{p_0} = \Big\{ p \in X \; \Big| \; \genmet(p,p_0) < r \Big\}
\end{align*}
`
is called an {term}[open ball] in $`X`, centered at $`p_0`, and with radius $`r`.

The set
$$`
\begin{align*}
  \CBallRC{r}{p_0} = \Big\{ p \in X \; \Big| \; \genmet(p,p_0) \le r \Big\}
\end{align*}
`
is called a {term}[closed ball] in $`X`, centered at $`p_0`, and with radius $`r`.

(In the case of the complex plane $`\bC`, the term {term}[disk]
is often used instead of the general metric space theory term {term}[ball].)
:::

:::definition "def_interior" (parent := "grp_topology_background") (uses := "def_ball")
{nodetitle}[Interior point]

Let $`X` be a metric space, and $`A \subset X` a subset.
A point $`p \in A` is said to be an {term}[interior point] of $`A`
if for some $`r > 0` we have $`\BallRC{r}{p} \subset A`.
:::

:::definition "def_exterior" (parent := "grp_topology_background") (uses := "def_ball, def_interior")
{nodetitle}[Exterior point]

Let $`X` be a metric space, and $`A \subset X` a subset.
A point $`p \in X \setminus A` is said to be an {term}[exterior point] of $`A`
if for some $`r > 0` we have $`\BallRC{r}{p} \subset X \setminus A`.

(It is easy to see that the exterior points of $`A` are exactly the interior
points)
:::

:::definition "def_boundary" (parent := "grp_topology_background") (uses := "def_ball, def_interior, def_exterior")
{nodetitle}[Boundary]

Let $`X` be a metric space, and $`A \subset X` a subset.
A point $`p \in X` is said to be a {term}[boundary point] of $`A`
if for all $`r > 0` we have that $`\BallRC{r}{p}` contains points
of $`A` and $`X \setminus A` (i.e. $`\BallRC{r}{p} \cap A \ne \emptyset`
and $`\BallRC{r}{p} \setminus A \ne \emptyset`).

The set of all boundary points of $`A` is denoted $`\bdry A` and called the
{term}[boundary] of $`A`.

(It is easy to see that the boundary $`\bdry A \subset X` is exactly
the set of points of $`X` which are neither interior nor exterior points
of $`A`.)
:::

:::definition "def_open_set" (parent := "grp_topology_background") (uses := "def_metric_space, def_ball, def_interior")
{nodetitle}[Open set]

Let $`X` be a metric space.
A subset $`U \subset X` is said to be an {term}[open set] if
each point $`p \in U` is an interior point of $`U`.
:::

:::definition "def_closed_set" (parent := "grp_topology_background") (uses := "def_open_set, def_exterior")
{nodetitle}[Closed set]

Let $`X` be a metric space.
A subset $`F \subset X` is said to be a {term}[closed set] if
the complement $`X \setminus F \subset X` is an open set.

(Equivalently, each point $`p \in X \setminus F` in the complement
of $`F` is an exterior point of $`F`.)
:::

:::definition "def_bounded" (parent := "grp_topology_background") (uses := "def_metric_space")
{nodetitle}[Boundedness]

Let $`X` be a metric space.
with metric $`\genmet \colon X \times X \to [0,\infty)`.

A subset $`A \subset X` is {term}[bounded] if there exists
a number $`M>0` such that $`\genmet(p,q) \le M` for all $`p,q \in A`.
(If $`X` is nonempty, an equivalent definition would be that
$`A` is bounded if it is a subset of some ball in $`X`.)

A function $`f \colon Z \to X` with values in a metric space $`X`
is {term}[bounded] if the set $`f[Z] \subset X` of its values is a
bounded subset of $`X`.

(In the case $`X = \bC` we have the following further characterizations:
A subset $`A \subset \bC` is bounded if and only if there exists an $`R>0`
such that $`|z| \le R` for all $`z \in A`. A function $`f \colon Z \to \bC`
is bounded if and only if there exists an $`R>0` such that $`|f(z)| \le R`
for all $`z \in Z`.)
:::

# Limits

:::definition "def_limit" (parent := "grp_topology_background") (uses := "def_metric_space")
{nodetitle}[Limit]

Let $`X` be a metric space and
let $`(x_n)_{n \in \bN}` be a sequence of points in $`X`.
We say that the sequence $`(x_n)_{n \in \bN}` {term}[converges]
to a {term}[limit] $`x \in X`
if for any $`\eps > 0` there exists an $`N \in \bN` such that
for all $`n \ge N` we have $`x_n \in \BallRC{\eps}{x}`
(i.e., $`\genmet(x_n,x) < \eps`).
We then denote
$$`
\begin{align*}
  \lim_{n \to \infty} x_n = x .
\end{align*}
`
(It is straightforward to check that the limit is
unique if it exists.)

Let then $`X` and $`Y` be metric spaces, with respective metrics
$`\genmet_X` and $`\genmet_Y`, and
let $`f \colon X \to Y` be a function.
We say that the function $`f` has a {term}[limit] $`y \in Y`
{term}[at a point] $`p_0 \in X`
if for any $`\eps > 0` there exists a $`\delta > 0` such that
for all $`p \in \BallRC{\delta}{p_0} \setminus \set{p_0}`
we have $`f(p) \in \BallRC{\eps}{y}`.
We then denote
$$`
\begin{align*}
  \lim_{p \to p_0} f(p) = y .
\end{align*}
`
(It is straightforward to check that the limit is
unique if it exists.)

(Equivalently, written in terms of distances,
$`\lim_{p \to p_0} f(p) = y` means that
for any $`\eps > 0` there exists a $`\delta > 0` such that
we have $`\genmet_Y \big( f(p), y \big) < \eps` whenever
$`0 < \genmet_X (p,p_0) < \delta`.)
:::

:::lemma_ "lem_complex_limit" (parent := "grp_topology_background") (uses := "def_limit, lem_metric_on_C")
{nodetitle}[Limits in the complex plane]

For a sequence $`(z_n)_{n \in \bN}` of complex numbers
we have
$$`
\begin{align*}
  \lim_{n \to \infty} z_n = z
\end{align*}
`
if and only if
$$`
\begin{align*}
  \lim_{n \to \infty} \re(z_n) = \re(z)
  \quad \text{and} \quad
  \lim_{n \to \infty} \im(z_n) = \im(z) .
\end{align*}
`

Let $`X` be a metric space,
let $`f \colon X \to \bC` a complex-valued
function on $`X`, and
let $`p_0 \in X` be a point. Then we have
$$`
\begin{align*}
  \lim_{p \to p_0} f(p) = z
\end{align*}
`
if and only if
$$`
\begin{align*}
  \lim_{p \to p_0} \re \big( f(p) \big) = \re(z)
  \quad \text{and} \quad
  \lim_{p \to p_0} \im \big( f(p) \big) = \im(z) .
\end{align*}
`
:::

:::proof "lem_complex_limit"
…
:::

:::lemma_ "lem_complex_limit_properties" (parent := "grp_topology_background") (uses := "lem_complex_limit, thm_complex_number_field")
{nodetitle}[Operations with complex limits]

Let $`(z_n)_{n \in \bN}` and $`(w_n)_{n \in \bN}`
be complex number sequences converging to limits
$$`
\begin{align*}
  \lim_{n \to \infty} z_n = z
  \quad \text{and} \quad
  \lim_{n \to \infty} w_n = w .
\end{align*}
`
Then we have
$$`
\begin{align*}
  \lim_{n \to \infty} (z_n + w_n) \, = \, z + w ,
  \quad
  \lim_{n \to \infty} (z_n w_n) \, = \, z w ,
  \quad
  \lim_{n \to \infty} \frac{z_n}{w_n} \, = \, \frac{z}{w}
  \; \text{ if $w \ne 0$}.
\end{align*}
`

Let $`X` be a metric space, let $`p_0 \in X`
be a point, and let $`f,g \colon X \to \bC`
be two complex-valued functions on $`X` such that
$$`
\begin{align*}
  \lim_{p \to p_0} f(p) = z
  \quad \text{and} \quad
  \lim_{p \to p_0} g(p) = w .
\end{align*}
`
Then we have
$$`
\begin{align*}
  \lim_{p \to p_0} \big( f(p) + g(p) \big) \, = \, z + w ,
  \quad
  \lim_{p \to p_0} \big( f(p) \, g(p) \big) \, = \, z w ,
  \quad
  \lim_{p \to p_0} \frac{f(p)}{g(p)} \, = \, \frac{z}{w}
  \; \text{ if $w \ne 0$}.
\end{align*}
`
:::

:::proof "lem_complex_limit_properties"
The arguments are similar to the proofs given in
{metSpCourse}[] for the real-valued cases.
:::

:::definition "def_cauchy_sequence" (parent := "grp_topology_background") (uses := "def_metric_space")
{nodetitle}[Cauchy sequence]

…
:::

:::lemma_ "lem_real_complete" (parent := "grp_topology_background") (uses := "def_cauchy_sequence, def_limit")
{nodetitle}[Every real Cauchy sequence converges]

If a real number sequence $`(x_n)_{n \in \bN}` is Cauchy,
then it converges to a limit $`\lim_{n \to \infty} x_n \in \bR`.

(This property is known as {term}[completeness] of the metric space $`\bR`.)
:::

:::proof "lem_real_complete"
See {metSpCourse}[].
:::

:::lemma_ "lem_complex_complete" (parent := "grp_topology_background") (uses := "def_cauchy_sequence, def_limit, lem_metric_on_C")
{nodetitle}[Every complex Cauchy sequence converges]

If a complex number sequence $`(z_n)_{n \in \bN}` is Cauchy,
then it converges to a limit $`\lim_{n \to \infty} z_n \in \bC`.

(This property is known as {term}[completeness] of the metric space $`\bC`.)
:::

:::proof "lem_complex_complete" (uses := "lem_real_complete, lem_complex_limit")
See {metSpCourse}[].

(Idea: This follows from {bpref "lem_real_complete"}[] by
considering real and imaginary parts separately and picking
a subsequence of a subsequence.)
:::

# Continuity

:::definition "def_continuous" (parent := "grp_topology_background") (uses := "def_metric_space, def_limit")
{nodetitle}[Continuity]

Let $`X` and $`Y` be metric spaces.
A function $`f \colon X \to Y` is said to be {term}[continuous at a point]
$`p_0 \in X` if $`\lim_{p \to p_0} f(p) = f(p_0)`.

(Equivalently, for every $`\eps > 0` there
exists a $`\delta > 0` such that for any $`p \in \BallRC{\delta}{p_0}`
we have $`f(p) \in \BallRC{\eps}{f(p_0)}`.)

A function $`f \colon X \to Y` is said to be {term}[continuous] if
it is continuous at every point $`p_0 \in X`.
:::

:::lemma_ "lem_continuous_complex" (parent := "grp_topology_background") (uses := "def_continuous")
{nodetitle}[Continuity of complex-valued functions]

Let $`X` be a metric space, and let $`f \colon X \to \bC` be
a complex-valued function on $`X`. Then $`f` is continuous
at $`p_0 \in X` if and only if its real and imaginary parts
$`p \mapsto \re \big( f(p) \big)`
and $`p \mapsto \im \big( f(p) \big)` are continuous at $`p_0`.
:::

:::proof "lem_continuous_complex" (uses := "lem_complex_limit")
…
:::

:::corollary "cor_coordinate_continuous" (parent := "grp_topology_background") (uses := "def_continuous")
{nodetitle}[Continuity of coordinate projections]

The coordinate projections
$$`
\begin{align*}
  \re \colon \; & \bC \to \bR
  \qquad\qquad \text{ and } & \quad
  \im \colon \; & \bC \to \bR \\
  & z \mapsto \re(z) &
  & z \mapsto \im(z)
\end{align*}
`
are continuous functions.
:::

:::proof "cor_coordinate_continuous" (uses := "lem_continuous_complex")
…
:::

:::lemma_ "lem_complex_continuity_properties" (parent := "grp_topology_background") (uses := "def_continuous, thm_complex_number_field")
{nodetitle}[Operations with continuous complex-valued functions]

Let $`X` be a metric space, let $`p_0 \in X`
be a point, and let $`f,g \colon X \to \bC`
be two complex-valued functions on $`X`
which are continuous at $`p_0`.
Then also the functions
$$`
\begin{align*}
  p \mapsto f(p) + g(p)
  \quad \text{and} \quad
  p \mapsto f(p) \, g(p)
\end{align*}
`
are continuous at $`p_0`.

If moreover $`g(p_0) \ne 0`, then
also the function
$`p \mapsto \frac{f(p)}{g(p)}`
is continuous at $`p_0`.
:::

:::proof "lem_complex_continuity_properties" (uses := "lem_continuous_complex, lem_complex_limit_properties")
…
:::

:::lemma_ "lem_continuity_characterization" (parent := "grp_topology_background") (uses := "def_continuous, def_open_set, def_closed_set")
{nodetitle}[Continuity characterization]

Let $`X` and $`Y` be metric spaces, and let $`f \colon X \to Y` be a function.
Then the following are equivalent:

* $`f` is a continuous function;
* for every open set $`V \subset Y`, the preimage
  $`f^{-1}[V] = \big\{ x \in X \, \big| \, f(x) \in V \big\}`
  is an open set in $`X`;
* for every closed set $`A \subset Y`, the preimage
  $`f^{-1}[A] = \big\{ x \in X \, \big| \, f(x) \in A \big\}`
  is a closed set in $`X`.
:::

:::proof "lem_continuity_characterization"
See {metSpCourse}[].
:::

:::lemma_ "lem_composition_continuous" (parent := "grp_topology_background") (uses := "def_continuous")
{nodetitle}[Composition of continuous functions]

Let $`X`, $`Y`, and $`Z` be metric spaces, and
let $`f \colon X \to Y` and $`g \colon Y \to Z` be functions.
If $`f` is continuous at $`x_0 \in X` and $`g` is continuous at $`f(x_0) \in Y`,
then the composition $`g \circ f \colon X \to Z` is continuous at $`x_0`.

(The composition $`g \circ f` is defined by
the formula $`(g \circ f)(x) = g \big( f(x) \big)`.)
:::

:::proof "lem_composition_continuous" (uses := "lem_continuity_characterization")
…
:::

:::corollary "cor_multivariate_polynomial_continuous" (parent := "grp_topology_background") (uses := "def_continuous")
{nodetitle}[Real multivariate polynomials are continuous]

Let $`N \in \bN` be a natural number, and let
$`c_{n,m} \in \bR` be real numbers for $`n,m \in \{0,1,\ldots,N\}`.
Then the function $`p \colon \bC \to \bR` defined by
$$`
\begin{align*}
  p(x + \ii y) = \sum_{m=0}^N \sum_{n=0}^N c_{m,n} \, x^m \, y^n
\end{align*}
`
is continuous.
:::

:::proof "cor_multivariate_polynomial_continuous" (uses := "lem_composition_continuous, lem_complex_continuity_properties, cor_coordinate_continuous")
See {metSpCourse}[].
:::

:::definition "def_uniformly_continuous" (parent := "grp_topology_background") (uses := "def_metric_space")
{nodetitle}[Uniform continuity]

Let $`X` and $`Y` be metric spaces.
A function $`f \colon X \to Y` is {term}[uniformly continuous] if
for every $`\eps > 0` there exists a $`\delta > 0` such that for
any $`p_0 \in X` and $`p \in \BallRC{\delta}{p_0}`
we have $`f(p) \in \BallRC{\eps}{f(p_0)}`.
:::

:::lemma_ "lem_uniformly_continuous_implies_continuous" (parent := "grp_topology_background") (uses := "def_continuous, def_uniformly_continuous")
{nodetitle}[Uniform continuity implies continuity]

If a function $`f \colon X \to Y` is uniformly continuous, then it is continuous.
:::

:::proof "lem_uniformly_continuous_implies_continuous"
See {metSpCourse}[].

(The easy proof is also a good exercise.)
:::

# Connectedness and path-connectedness

:::definition "def_connected" (parent := "grp_topology_background") (uses := "def_metric_space")
{nodetitle}[Connectedness]

A set $`A \subset X` in a metric space $`X`
is {term}[disconnected] if there exists
a continuous surjective function
$`f \colon A \to \set{0,1}` onto the two-element discrete
set $`\set{0,1}`.
Otherwise $`A` is {term}[connected];
then every continuous function $`A \to \set{0,1}` must be
either constant $`0` or constant $`1`.

(The usual definition in topology textbooks reads
slightly differently, but it is
equivalent to the one we chose here by
{bpref "lem_continuity_characterization"}[].)
:::

:::definition "def_path_connected" (parent := "grp_topology_background") (uses := "def_path")
{nodetitle}[Path-connectedness]

A set $`A \subset X` in a metric space $`X`
is {term}[path connected] if for any two points $`p, q \in X`
there exists a continuous function $`\gamma \colon [0,1] \to X`
such that $`\gamma(0) = p` and $`\gamma(1) = q`
(a parametrized path in $`X` starting from $`p` and ending at $`q`).
:::

:::lemma_ "lem_path_connected_implies_connected" (parent := "grp_topology_background") (uses := "def_connected, def_path_connected")
{nodetitle}[Path-connectedness implies connectedness]

If a metric space $`X` is path-connected, then it is connected.
:::

:::proof "lem_path_connected_implies_connected"
See {metSpCourse}[].
:::

:::lemma_ "lem_open_connected_iff_path_connected" (parent := "grp_topology_background") (uses := "def_connected, def_path_connected, def_open_set, lem_metric_on_C")
{nodetitle}[Open connected sets are path-connected]

Suppose that $`U \subset \bC` is an open subset of the complex plane.
Then $`U` is connected if and only if it is path-connected.
:::

:::proof "lem_open_connected_iff_path_connected" (uses := "lem_path_connected_implies_connected")
See {metSpCourse}[].
:::

# Compactness

:::definition "def_compact" (parent := "grp_topology_background") (uses := "def_limit")
{nodetitle}[Compactness]

Let $`X` be a metric space.
A subset $`K \subset X` is {term}[compact] if every sequence
$`(x_n)_{n \in \bN}` of points $`x_n \in K` has a subsequence
$`(x_{n_k})_{k \in \bN}` which converges to a limit
$`\lim_{k \to \infty} x_{n_k} \in K` in the set $`K`.
:::

:::theorem "thm_bolzano_weierstrass" (parent := "grp_topology_background") (uses := "def_compact, def_closed_set, lem_metric_on_C, def_bounded")
{nodetitle}[Bolzano-Weierstrass theorem]

A subset $`B \subset \bR` of the real line is compact
if an only if it is closed and bounded.

A subset $`A \subset \bC` of the complex plane is compact
if an only if it is closed and bounded.
:::

:::proof "thm_bolzano_weierstrass"
See {metSpCourse}[].
:::

:::theorem "thm_continuous_on_compact_implies_bounded" (parent := "grp_topology_background") (uses := "def_compact, def_bounded, def_continuous")
{nodetitle}[Boundedness of continuous functions on compacts]

Suppose that $`X` is compact.
Then every continuous function $`f \colon X \to \bR`
is bounded.
:::

:::proof "thm_continuous_on_compact_implies_bounded"
…
:::

:::lemma_ "lem_on_compact_continuous_implies_uniformly_continuous" (parent := "grp_topology_background") (uses := "def_continuous, def_uniformly_continuous, def_compact")
{nodetitle}[On a compact domain continuity implies uniform continuity]

If $`X` is compact and a function $`f \colon X \to Y` is continuous, then it is uniformly continuous.
:::

:::proof "lem_on_compact_continuous_implies_uniformly_continuous"
See {metSpCourse}[].
:::

:::lemma_ "lem_continuous_bijection_homeomorphism" (parent := "grp_topology_background") (uses := "def_compact, def_continuous")
{nodetitle}[Continuous bijection from a compact domain is a homeomorphism]

Let $`X` and $`Y` be metric spaces and assume that $`X` is compact.
Then for any continuous bijection $`f \colon X \to Y`,
also the inverse $`f^{-1} \colon Y \to X` is continuous.
:::

:::proof "lem_continuous_bijection_homeomorphism" (uses := "lem_continuity_characterization")
See {metSpCourse}[].
:::

:::theorem "thm_intersect_nested_compacts" (parent := "grp_topology_background") (uses := "def_compact")
{nodetitle}[Cantor's intersection theorem] {palka}[Thm II.4.5]

Let $`X` be a metric space.
Suppose that $`K_1, K_2, K_3, \ldots` are nonempty compact
subsets of $`X` nested so that $`K_1 \supset K_2 \supset K_3 \supset \cdots`.
Then the intersection $`\bigcap_{n=1}^\infty K_n` is nonempty.
:::

:::proof "thm_intersect_nested_compacts"
See {metSpCourse}[].
:::

# Simple connectedness

:::definition "def_path_homotopy" (parent := "grp_topology_background") (uses := "def_path, def_continuous")
{nodetitle}[Path homotopy for closed paths]

Let $`X` be a metric space and
$`\gamma_0 \colon [a,b] \to X` and $`\gamma_0 \colon [a,b] \to X`
two closed paths in $`X`.
If there exists a
continuous function (called a {term}[homotopy])
$$`
\begin{align*}
  \Gamma \colon [0,1] \times [a,b] \to X
\end{align*}
`
such that
$$`
\begin{align*}
  & \Gamma(0,t) = \gamma_0(t)
    \quad \text{ and } \quad
    \Gamma(1,t) = \gamma_1(t)
    \qquad \text{for all $t \in [a,b]$}
\end{align*}
`
and
$$`
\begin{align*}
  \Gamma(s,a) = \Gamma(s,b) \qquad \text{for all $s \in [0,1]$,}
\end{align*}
`
then we say that the closed paths $`\gamma_0` and $`\gamma_1`
are {term}[homotopic].
:::

:::definition "def_contractible" (parent := "grp_topology_background") (uses := "def_path_homotopy")
{nodetitle}[Contractible path]

Let $`X` be a metric space.
A closed path $`\gamma \colon [a,b] \to X` is called
{term}[contractible] if it is homotopic to a constant path.
:::

:::definition "def_simply_connected" (parent := "grp_topology_background") (uses := "def_contractible")
{nodetitle}[Simple connectedness]

A metric space is said to be {term}[simply connected]
if every closed path $`\gamma \colon [a,b] \to X` in $`X`
is contractible.
:::
