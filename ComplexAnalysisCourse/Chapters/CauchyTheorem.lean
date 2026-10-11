import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Cauchy's theorem and consequences" =>
%%%
file := "cauchy-theorem"
%%%

# Convex, star-shaped, and simply connected domains

:::definition "def_line_segment" (uses := "thm_complex_number_field, def_path")
{nodetitle}[Line segment]

Given two points $`z_1, z_2 \in \bC` in the complex plane,
the {term}[line segment] between $`z_1` and $`z_2` is the path
$$`
\begin{align*}
  \gamma \colon [0,1] & \; \to \bC \\
  \gamma(t) & \; = z_1 + t \, (z_2 - z_1) .
\end{align*}
`

We also often view the line segment as a subset of $`\bC`
rather than a parametrized path, and we then denote it by
$$`
\begin{align*}
  [z_1, z_2]
  \, = \, \Big\{ z_1 + t \, (z_2 - z_1) \; \Big| \; t \in [0,1] \Big\}
  \, \subset \, \bC.
\end{align*}
`
:::

:::definition "def_convex" (uses := "def_line_segment")
{nodetitle}[Convex set]

A subset $`A \subset \bC` of the complex plane is called
{term}[convex] if for any two points $`z_1, z_2 \in A`,
the line segment between them is contained in the subset,
$$`
\begin{align*}
  [z_1, z_2] \, \subset \, A .
\end{align*}
`
:::

:::definition "def_star_shaped" (uses := "def_line_segment")
{nodetitle}[Star-shaped set]

A subset $`A \subset \bC` of the complex plane is called
{term}[star-shaped] if there exists a point $`z_* \in A`
such that for any $`z \in A`,
the line segment between $`z_*` and $`z` is contained in the subset,
$$`
\begin{align*}
  [z_*, z] \, \subset \, A .
\end{align*}
`
:::

:::lemma_ "lem_convex_implies_star_shaped" (uses := "def_convex, def_star_shaped")
{nodetitle}[Convex sets are star-shaped]

Any nonempty convex set is star-shaped.
:::

:::proof "lem_convex_implies_star_shaped"
…
:::

:::lemma_ "lem_star_shaped_implies_simply_connected" (uses := "def_simply_connected, def_star_shaped, def_path_connected")
{nodetitle}[Star-shaped sets are path connected and simply connected]

Any star-shaped set $`U \subset \bC` is path connected and simply connected.
:::

:::proof "lem_star_shaped_implies_simply_connected"
…
:::

# Cauchy's integral theorem

:::lemma_ "lem_goursat" (uses := "def_analytic_function, def_contour_integral")
{nodetitle}[Goursat's lemma] {palka}[Lem V.1.1]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
set $`U \subset \bC`.
Then for any closed triangle $`\Tri \subset U`, we have
$$`
\begin{align*}
  \oint_{\bdry \Tri} f(z) \, \ud z = 0 .
\end{align*}
`
:::

:::proof "lem_goursat" (uses := "thm_intersect_nested_compacts, lem_local_linear_approximation")
…
:::

:::lemma_ "lem_primitive_star_shaped" (uses := "def_primitive, def_star_shaped")
{nodetitle}[Existence of primitives in star-shaped domains]

Every analytic function $`f \colon U \to \bC` on a star-shaped
domain $`U \subset \bC` has a primitive in $`U`.
:::

:::proof "lem_primitive_star_shaped" (uses := "lem_goursat")
…
:::

:::theorem "thm_cauchy_theorem_star_shaped" (uses := "def_analytic_function, def_contour_integral, def_star_shaped")
{nodetitle}[Cauchy's integral theorem for star-shaped domains] {palka}[Thm V.1.5]

Suppose that a function $`f \colon U \to \bC` is analytic on a
star-shaped open subset $`U \subset \bC`.
Then for any closed contour $`\gamma` in $`U` we have
$$`
\begin{align*}
  \oint_\gamma f(z) \, \ud z = 0 .
\end{align*}
`
:::

:::proof "thm_cauchy_theorem_star_shaped" (uses := "thm_primitive_characterization, lem_primitive_star_shaped")
…
:::

:::corollary "cor_local_cauchy_theorem" (uses := "def_analytic_function, def_contour_integral, def_contractible")
{nodetitle}[Local Cauchy's integral theorem] {palka}[Thm V.5.1]

Suppose that a function $`f \colon U \to \bC` is analytic on a open
set $`U \subset \bC`.
Then for any disk $`B \subset U` contained in the domain $`U`
and any closed contour $`\gamma` in $`B` we have
$$`
\begin{align*}
  \oint_\gamma f(z) \, \ud z = 0 .
\end{align*}
`
:::

:::proof "cor_local_cauchy_theorem" (uses := "lem_goursat, thm_cauchy_theorem_star_shaped")
…
:::

# Cauchy's integral formula

:::theorem "thm_cauchy_formula_star_shaped" (uses := "def_analytic_function, def_contour_integral")
{nodetitle}[Cauchy's integral formula for star-shaped subdomains] {palka}[Thm V.2.3]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
set $`U \subset \bC`, and suppose that $`\gamma` is a closed contour
in $`U` parametrizing the boundary of a star-shaped Jordan subdomain
$`V \subset U` in a counterclockwise orientation.
Then for any point $`z \in V` we have
$$`
\begin{align*}
  f(z) = \frac{1}{2\pi \ii} \oint_\gamma \frac{f(\zeta)}{\zeta - z} \, \ud \zeta .
\end{align*}
`
:::

:::proof "thm_cauchy_formula_star_shaped" (uses := "thm_cauchy_theorem_star_shaped")
…
:::

By far the most commonly used special case of
{bpref "thm_cauchy_formula_star_shaped"}[]
is when the contour $`\gamma` is a circle, encircling a disk
whose closure is contained in the domain of the analytic function
(recall that disks are convex and therefore star-shaped).

:::corollary "cor_cauchy_formula_circle" (uses := "def_analytic_function, def_contour_integral")
{nodetitle}[Cauchy's integral formula for circles]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
set $`U \subset \bC`.
Let $`\CDiskRC{r}{z_0} \subset U` be a closed disk contained in $`U`.
Then for any point $`z \in \DiskRC{r}{z_0}` we have
$$`
\begin{align*}
  f(z) = \frac{1}{2\pi \ii}
      \oint_{\bdry \DiskRC{r}{z_0}} \frac{f(\zeta)}{\zeta - z} \, \ud \zeta
\end{align*}
`
where the circle $`\bdry \DiskRC{r}{z_0}` is parametrized in the
counterclockwise orientation.
:::

:::proof "cor_cauchy_formula_circle" (uses := "thm_cauchy_formula_star_shaped")
…
:::

# Ideas underlying the generalizations

The generalizations of Cauchy's integral theorem and Cauchy's integral
formula are based on the following homotopy invariance property of
contour integrals (whose proof we do not do in detail in this course).

:::lemma_ "lem_homotopy_invariance" (uses := "def_path_homotopy, def_contour_integral")
{nodetitle}[Homotopy invariance of contour integrals]

Let $`f \colon U \to \bC` be an analytic function on an open
set $`U \subset \bC`, and let $`\gamma_0` and $`\gamma_1` be two
closed contours in $`U` which are homotopic to each other in $`U`.
Then we have
$$`
\begin{align*}
  \oint_{\gamma_0} f(z) \, \ud z = \oint_{\gamma_1} f(z) \, \ud z .
\end{align*}
`
:::

This readily implies the following generalization of Cauchy's integral
theorem.

:::theorem "thm_cauchy_theorem" (uses := "def_analytic_function, def_contour_integral, def_contractible")
{nodetitle}[Cauchy's integral theorem] {palka}[Thm V.5.1]

Suppose that a function $`f \colon U \to \bC` is analytic on a open
set $`U \subset \bC`.
Then for any contractible closed contour $`\gamma` we have
$$`
\begin{align*}
  \oint_\gamma f(z) \, \ud z = 0 .
\end{align*}
`

In particular, if $`U` is simply connected, then
for any closed contour $`\gamma` in $`U` we have
$$`
\begin{align*}
  \oint_\gamma f(z) \, \ud z = 0 ,
\end{align*}
`
and the analytic function $`f` has a primitive in $`U`.
:::

:::proof "thm_cauchy_theorem" (uses := "lem_goursat, cor_local_cauchy_theorem, lem_homotopy_invariance")
…
:::

The other ingredient of generalization of Cauchy's integral formula
to arbitrary contours and points not lying on those contours is
the winding number of a contour around a point.

:::definition "def_winding_number" (uses := "def_contour_integral")
{nodetitle}[Winding number]

Let $`z \in \bC`, and let $`\gamma` be a closed contour
in $`\bC \setminus \set{z}`.
The {term}[winding number] of $`\gamma` around $`z` is defined as
$$`
\begin{align*}
  \windN{\gamma}{z} = \frac{1}{2\pi \ii} \oint_\gamma \frac{\ud \zeta}{\zeta - z} .
\end{align*}
`
:::

:::lemma_ "lem_winding_additivity" (uses := "def_winding_number")
{nodetitle}[Winding number concatenation and reversal]

Let $`\gamma` and $`\eta` be closed contours in $`\bC`
both starting and ending at the same point $`z_0 \in \bC`.
Then for any point $`z \in \bC \setminus (\gamma \cup \eta)`
we have
$$`
\begin{align*}
  \windN{\gamma \concat \eta}{z}
  \; = \; \windN{\gamma}{z} + \windN{\eta}{z}
\end{align*}
`
and for any point $`z \in \bC \setminus \gamma` we have
$$`
\begin{align*}
  \windN{\opp{\gamma}}{z}
  \; = \; -\windN{\gamma}{z} .
\end{align*}
`
:::

:::proof "lem_winding_additivity"
…
:::

:::lemma_ "lem_winding_number_properties" (uses := "def_winding_number")
{nodetitle}[Winding number properties]

Let $`\gamma` be a closed contour in $`\bC`. Then the winding
numbers $`\windN{\gamma}{z}` of points $`z \in \bC \setminus \gamma`
satisfy:

* (a) $`z \mapsto \windN{\gamma}{z}` is constant on
  each connected component of $`\bC \setminus \gamma`;
* (b) $`\windN{\gamma}{z} = 0` for all $`z` in the
  unbounded connected component of $`\bC \setminus \gamma`;
* (c) If $`\gamma` is a Jordan contour and
  $`V \subset \bC \setminus \gamma` is the bounded connected
  component of $`\bC \setminus \gamma`, then
  either $`\windN{\gamma}{z} = 1` for all $`z \in V`
  or $`\windN{\gamma}{z} = -1` for all $`z \in V`.
:::

:::proof "lem_winding_number_properties" (uses := "lem_derivative_auxiliary_integral")
…
:::

:::lemma_ "lem_winding_homotopy_invariance" (uses := "def_winding_number, def_path_homotopy")
{nodetitle}[Homotopy invariance of winding numbers]

Let $`z \in \bC` be a point and let $`\gamma` and $`\eta` be two
closed contours in $`\bC \setminus \set{z}` which are homotopic
to each other in $`\bC \setminus \set{z}`. Then we have
$$`
\begin{align*}
  \windN{\gamma}{z} = \windN{\eta}{z} .
\end{align*}
`
:::

:::proof "lem_winding_homotopy_invariance" (uses := "lem_homotopy_invariance")
…
:::

The following is then a version of Cauchy's integral formula
which has no restrictions on the closed contour and
no restrictions on the position of the point with respect to
the contour, except that the point must not lie on the contour
(for otherwise there is a singularity in the integrand).

:::theorem "thm_CAUCHY_FORMULA" (uses := "def_analytic_function, def_contour_integral, def_winding_number")
{nodetitle}[Cauchy's integral formula] {palka}[Thm V.2.3]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
simply connected subset $`U \subset \bC` of the complex plane.
Then for any closed contour $`\gamma`
in $`U` we have
$$`
\begin{align*}
  \oint_\gamma \frac{f(\zeta)}{\zeta - z} \, \ud \zeta
  \; = \; 2\pi \ii \, \windN{\gamma}{z} \, f(z) .
\end{align*}
`
:::

:::proof "thm_CAUCHY_FORMULA" (uses := "thm_cauchy_theorem, thm_cauchy_formula_star_shaped")
…
:::

# Analyticity of derivatives

:::lemma_ "lem_derivative_analytic" (uses := "def_analytic_function")
{nodetitle}[Analyticity of derivatives] {palka}[Thm V.3.1]

If a function $`f \colon U \to \bC` is analytic on an open set $`U \subset \bC`,
then its derivative $`f'` is also analytic on $`U`.
In particular, then $`f` is continuously differentiable,
$`f \in \ContDiff{1}(U)`.
:::

:::proof "lem_derivative_analytic" (uses := "thm_CAUCHY_FORMULA, lem_derivative_auxiliary_integral")
…
:::

:::corollary "lem_higher_derivatives_analytic" (uses := "def_analytic_function")
{nodetitle}[Analyticity of higher derivatives] {palka}[Cor V.3.2]

If a function $`f \colon U \to \bC` is analytic on an open set $`U \subset \bC`,
then its derivatives $`f', f'', \ldots, f^{(k)}, \ldots` of all orders are
also analytic on $`U`.
In particular, then $`f` is infinitely differentiable, $`f \in \Smooth(U)`.
:::

:::proof "lem_higher_derivatives_analytic" (uses := "lem_derivative_analytic, lem_derivative_auxiliary_integral")
Straightforward induction using {bpref "lem_derivative_analytic"}[].
:::

:::theorem "thm_morera" (uses := "def_analytic_function")
{nodetitle}[Morera's theorem] {palka}[Thm V.3.3]

Let $`f \colon U \to \bC` be a continuous function on an open set $`U \subset \bC`.
If $`f` has the property that
$$`
\begin{align*}
  \oint_{\bdry \Tri} f(z) \, \ud z = 0
\end{align*}
`
for any closed triangle $`\Tri \subset U`, then $`f` is analytic on $`U`.
:::

:::proof "thm_morera" (uses := "def_primitive, lem_derivative_analytic")
…
:::

:::theorem "thm_cauchy_formula_derivative" (uses := "def_analytic_function")
{nodetitle}[Cauchy's integral formula for derivatives]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
simply connected subset $`U \subset \bC` of the complex plane.
Then for any closed contour $`\gamma`
in $`U`, any $`n \in \bN`, and any point $`z \in U` we have
$$`
\begin{align*}
  \windN{\gamma}{z} \, f^{(n)}(z)
    = \frac{n!}{2\pi \ii} \oint_\gamma \frac{f(\zeta)}{(\zeta - z)^{n+1}} \, \ud \zeta .
\end{align*}
`
:::

:::proof "thm_cauchy_formula_derivative" (uses := "thm_CAUCHY_FORMULA, lem_derivative_auxiliary_integral")
…
:::

:::lemma_ "lem_cauchy_derivative_estimate" (uses := "def_analytic_function")
{nodetitle}[Cauchy's estimate for derivatives] {palka}[Thm V.3.6]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
set $`U \subset \bC` containing the disk $`\DiskRC{r}{z_0} \subset U`,
and suppose that there exists a constant $`M>0` such that
$`|f(z)| \le M` for all $`z \in \DiskRC{r}{z_0}`.
Then for any $`n \in \bN` and any $`z \in \DiskRC{r}{z_0}` we have
the following bound for the $`n`th derivative $`f^{(n)}` of $`f`:
$$`
\begin{align*}
  \big| f^{(n)}(z) \big| \le \frac{n! \, M \, r}{( r - |z-z_0| )^{n+1}} .
\end{align*}
`
In particular, for the center point $`z_0` of the disk, we have
$$`
\begin{align*}
  \big| f^{(n)}(z_0) \big| \le n! \, M \, r^{-n} .
\end{align*}
`
:::

:::proof "lem_cauchy_derivative_estimate" (uses := "thm_cauchy_formula_derivative, lem_integral_triangle_inequality")
…
:::

# Liouville's theorem

:::theorem "thm_liouville" (uses := "def_analytic_function")
{nodetitle}[Liouville's theorem] {palka}[Thm V.3.7]

If a function $`f \colon \bC \to \bC` on the entire complex plane
is analytic and bounded, then $`f` is a constant function.
:::

:::proof "thm_liouville" (uses := "lem_cauchy_derivative_estimate")
…
:::

# The fundamental theorem of algebra

:::theorem "thm_FUNDAMENTAL_THEOREM_OF_ALGEBRA" (uses := "def_polynomial")
{nodetitle}[Fundamental theorem of algebra] {palka}[Thm V.3.8]

Every non-constant polynomial function $`p \colon \bC \to \bC`
has a root, i.e., there exists a $`z_0 \in \bC` such that $`p(z_0) = 0`.
:::

:::proof "thm_FUNDAMENTAL_THEOREM_OF_ALGEBRA" (uses := "thm_liouville, lem_polynomial_analytic")
…
:::

:::corollary "cor_complex_polynomial_factorization" (uses := "def_polynomial")
{nodetitle}[Polynomial factorization] {palka}[Thm V.3.9]

A complex-coefficient
polynomial $`p(z) = a_0 + a_1 z + a_2 z^2 + \cdots + a_n z^n`
of degree $`n \in \bN` can be factored as
$$`
\begin{align*}
  p(z) = c \, (z - z_1) \, (z - z_2) \, \cdots \, (z - z_n)
\end{align*}
`
where $`c = a_n \ne 0`, and $`z_1 , \ldots, z_n \in \bC`
are the roots of $`p` (with repetition according to the
multiplicities of the roots).
:::

:::proof "cor_complex_polynomial_factorization" (uses := "thm_FUNDAMENTAL_THEOREM_OF_ALGEBRA")
This follows from {bpref "thm_FUNDAMENTAL_THEOREM_OF_ALGEBRA"}[]
by induction on the degree of the polynomial,
using the polynomial division (Euclidean algorithm in the
ring of univariate polynomials, see *MS-C1081 Abstract Algebra*).
:::

# Maximum principle

:::theorem "thm_maximum_principle" (uses := "def_analytic_function, def_connected")
{nodetitle}[Maximum principle for analytic functions] {palka}[Thm V.3.10]

Let $`f \colon \Domain \to \bC` be an analytic function on a
connected open set $`\Domain \subset \bC`.
Suppose that there exists a point $`z_0 \in \Domain`
such that
$$`
\begin{align*}
  |f(z)| \le |f(z_0)| \qquad \text{ for all } z \in \Domain .
\end{align*}
`
Then $`f` is a constant function.
:::

:::proof "thm_maximum_principle" (uses := "thm_CAUCHY_FORMULA")
…
:::

:::corollary "cor_maximum_modulus_on_boundary" (uses := "def_analytic_function, def_connected")
{nodetitle}[Maximum principle for analytic functions continuous up to the boundary] {palka}[Cor V.3.11]

Let $`\Domain \subset \bC` be a bounded connected open set.
Let $`f \colon \closOf{\Domain} \to \bC` be a continuous function
on its closure which is analytic in $`\Domain`.
Then $`z \mapsto |f(z)|` attains its maximum in $`\closOf{\Domain}`
at some point of the boundary $`\bdry \Domain`.
:::

:::proof "cor_maximum_modulus_on_boundary" (uses := "thm_maximum_principle")
…
:::

:::lemma_ "lem_schwarz_lemma" (uses := "def_analytic_function")
{nodetitle}[Schwarz's lemma] {palka}[Thm V.3.14]

Let $`f \colon \DiskRC{1}{0} \to \bC` be an analytic function
on the open unit disk such that $`|f(z)| \le 1`
for all $`z \in \DiskRC{1}{0}` and $`f(0) = 0`.
Then we have
$$`
\begin{align*}
  |f'(0)| \le 1
  \qquad \text{ and } \qquad
  |f(z)| \le |z| \quad \text{ for all } z \in \DiskRC{1}{0} .
\end{align*}
`
Furthermore, unless $`f` is of the form $`f(z) = \lambda z` for
some $`\lambda \in \bC` with $`|\lambda| = 1`, then we have
$$`
\begin{align*}
  |f'(0)| < 1
  \qquad \text{ and } \qquad
  |f(z)| < |z| \quad \text{ for all } z \in \DiskRC{1}{0} \setminus \set{0}.
\end{align*}
`
:::

:::proof "lem_schwarz_lemma" (uses := "cor_maximum_modulus_on_boundary")
…
:::

# The mean value property

:::theorem "thm_mean_value_property" (uses := "def_analytic_function")
{nodetitle}[Mean value property for analytic functions]

Suppose that a function $`f \colon U \to \bC` is analytic on an open
set $`U \subset \bC` containing the closed disk $`\CDiskRC{r}{z} \subset U`.
Then we have
$$`
\begin{align*}
  f(z)
  \, = \; & \frac{1}{2 \pi r} \int_{\bdry \DiskRC{r}{z}}
          f(\zeta)\, |\ud \zeta|
  \, = \, \frac{1}{2 \pi} \int_{0}^{2\pi}
          f(r + r e^{\ii \theta}) \, \ud \theta .
\end{align*}
`
:::

:::proof "thm_mean_value_property" (uses := "cor_cauchy_formula_circle")
…
:::
