import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Isolated singularities and residues" =>
%%%
file := "singularities"
%%%

:::group "grp_singularities"
Isolated singularities and residues
:::

# The extended complex plane

:::definition "def_riemann_sphere" (parent := "grp_singularities") (uses := "lem_metric_on_C, def_limit")
{nodetitle}[The Riemann sphere]

The {term}[extended complex plane] is the set
$$`
\begin{align*}
  \hat{\bC} = \bC \cup \set{\infty} \, ,
\end{align*}
`
where $`\infty` is a symbol added to $`\bC` to represent a single point
at infinity. The set $`\hat{\bC}` is given a topology
in such a way that open sets in $`\bC` remain open in $`\hat{\bC}`,
and sets of the form $`\big\{z \in \bC \; \big| \; |z|>M \big\}` for $`M>0`
form a neighborhood basis at $`\infty`.

(This topology makes $`\hat{\bC}` homeomorphic to the 2-dimensional sphere in
three-dimensional space, and $`\hat{\bC}` is also called the {term}[Riemann sphere].)

For example a function $`f \colon U \to \bC` has limit
$`\lim_{z \to z_0} f(z) = \infty` at $`z_0` if for any $`M>0`
there exists a $`\delta > 0` such that
$`|f(z)|>M` whenever $`0 < |z-z_0| < \delta`.
:::

# Isolated singularities of analytic functions

:::definition "def_isolated_singularity" (parent := "grp_singularities") (uses := "def_analytic_function")
{nodetitle}[Isolated singularity] {palka}[Sec. VIII.2.1]

Let $`f : U \to \bC` be an analytic function on an open set $`U \subset \bC`.
We say that $`f` has an {term}[isolated singularity] at $`z_0 \in \bC` if
$`\BallRC{r}{z_0} \setminus \set{z_0} \subset U` for some $`r>0` but $`z_0 \notin U`.
:::

:::definition "def_singularity_classification" (parent := "grp_singularities") (uses := "def_isolated_singularity, thm_ANALYTIC_FUNCTION_LAURENT_SERIES")
{nodetitle}[Classification of isolated singularities] {palka}[Sec. VIII.2.1]

Let $`z_0 \in \bC` be an isolated singularity of
an analytic function $`f : U \to \bC`.
Let $`r > 0` be such that $`\BallRC{r}{z_0} \setminus \set{z_0} \subset U`,
so that by {bpref "thm_ANALYTIC_FUNCTION_LAURENT_SERIES"}[]
$`f` can be represented in $`\BallRC{r}{z_0} \setminus \set{z_0}`
uniquely as a Laurent series
$$`
\begin{align*}
  f(z) = \sum_{n=-\infty}^\infty a_n (z - z_0)^n .
\end{align*}
`
Depending on the coefficients $`a_n` of negative indices $`n < 0`,
we distinguish three types of singularities:

* $`f` has a {term}[removable singularity] at $`z_0` if $`a_n = 0` for all $`n < 0`;
* $`f` has a {term}[pole of order $`m \in \bN`] at $`z_0`
  if $`a_{-m} \ne 0` and $`a_n = 0` for all $`n < -m`;
* $`f` has an {term}[essential singularity] at $`z_0` if
  $`a_n \ne 0` for infinitely many $`n < 0`.
:::

:::definition "def_residue" (parent := "grp_singularities") (uses := "def_isolated_singularity, thm_ANALYTIC_FUNCTION_LAURENT_SERIES")
{nodetitle}[Residue at an isolated singularity] {palka}[Sec. VIII.2.1]

Let $`z_0 \in \bC` be an isolated singularity of
an analytic function $`f : U \to \bC`.
Let $`r > 0` be such that $`\BallRC{r}{z_0} \setminus \set{z_0} \subset U`,
so that by {bpref "thm_ANALYTIC_FUNCTION_LAURENT_SERIES"}[]
$`f` can be represented in $`\BallRC{r}{z_0} \setminus \set{z_0}`
uniquely as a Laurent series
$$`
\begin{align*}
  f(z) = \sum_{n=-\infty}^\infty a_n (z - z_0)^n .
\end{align*}
`
The coefficient $`a_{-1}` is called the {term}[residue] of $`f` at $`z_0`,
and is denoted $`\ResAtOf{z_0}{f} = a_{-1} \in \bC`.
:::

:::theorem "thm_removable_singularity" (parent := "grp_singularities") (uses := "def_singularity_classification")
{nodetitle}[Removable singularity characterization] {palka}[Thm VIII.2.1 and Thm VIII.2.2]

Let $`z_0 \in \bC` be an isolated singularity of
an analytic function $`f : U \to \bC`.
Then the following conditions are equivalent:

* *(R-1)* The singularity of $`f` at $`z_0` is removable (i.e., all negative
  index Laurent series coefficients of $`f` expanded near $`z_0` vanish).
* *(R-2)* There exists an analytic function $`\tilde{f} \colon U \cup \set{z_0} \to \bC`
  such that $`f(z) = \tilde{f}(z)` for all $`z \in U`.
* *(R-3)* The limit $`\lim_{z \to z_0} f(z)` exists in $`\bC`.
* *(R-4)* The function $`f` is bounded in some punctured disk
  $`\BallRC{r}{z_0} \setminus \set{z_0}` with $`r>0`.
:::

:::proof "thm_removable_singularity"
…
:::

:::theorem "thm_pole" (parent := "grp_singularities") (uses := "def_singularity_classification, def_riemann_sphere")
{nodetitle}[Characterization of poles] {palka}[Thm VIII.2.3 and Thm VIII.2.4]

Let $`z_0 \in \bC` be an isolated singularity of
an analytic function $`f : U \to \bC`.
Then the following conditions are equivalent:

* *(P-1)* The singularity of $`f` at $`z_0` is a pole (i.e.,
  finitely many Laurent series coefficients of $`f` near $`z_0` are nonzero).
* *(P-2)* There exists an $`m \in \bN = \set{1,2,\ldots}`
  such that $`z \mapsto (z-z_0)^m \, f(z)` has a removable singularity
  and a nonzero limit as $`z \to z_0`.
* *(P-3)* The function $`f` has the limit $`\lim_{z \to z_0} f(z) = \infty` at $`z_0`.
:::

:::proof "thm_pole"
…
:::

:::theorem "thm_essential_singularity" (parent := "grp_singularities") (uses := "def_singularity_classification, def_riemann_sphere")
{nodetitle}[Characterization of essential singularities] {palka}[Thm VIII.2.6 and Thm VIII.2.7]

Let $`z_0 \in \bC` be an isolated singularity of
an analytic function $`f : U \to \bC`.
Then the following conditions are equivalent:

* *(E-1)* The singularity of $`f` at $`z_0` is essential (i.e.,
  infinitely many Laurent series coefficients of $`f` near $`z_0` are nonzero).
* *(E-2)* For any small $`\delta > 0`, the image
  $`f \big[ \BallRC{\delta}{z_0} \setminus \set{z_0} \big]` is dense in $`\bC`.
* *(E-3)* The limit $`\lim_{z \to z_0} f(z)` does not exist
  in the extended complex plane $`\hat{\bC} = \bC \cup \set{\infty}`.
:::

:::proof "thm_essential_singularity"
…
:::

# The residue theorem

:::theorem "thm_RESIDUE_THEOREM" (parent := "grp_singularities") (uses := "def_residue")
{nodetitle}[Residue theorem] {palka}[Thm VIII.3.1]

Let $`U \subset \bC` be an open set and $`\gamma` a contractible closed contour in $`U`.
Let $`f : U \setminus S \to \bC` be an analytic function with isolated
singularities at a countable set $`S \subset U` of points.
Then
$$`
\begin{align*}
  \oint_\gamma f(z) \, dz
    = 2 \pi \ii \sum_{w \in S} \windN{w}{\gamma} \, \ResAtOf{w}{f} .
\end{align*}
`
:::

:::proof "thm_RESIDUE_THEOREM" (uses := "thm_CAUCHY_FORMULA")
…
:::

:::corollary "thm_jordan_residue_theorem" (parent := "grp_singularities") (uses := "def_residue")
{nodetitle}[Residue theorem for Jordan contours] {palka}[Cor VIII.3.2]

Let $`U \subset \bC` be an open set and $`S \subset U` a discrete subset of it.
Let $`\Domain` be a Jordan domain such that $`\closOf{\Domain} \subset U`
and $`\bdry \Domain \cap S = \emptyset`.
Let $`\gamma` be a closed contour traversing the boundary $`\bdry \Domain`
of the Jordan domain in the positive orientation.
Let $`f : U \setminus S \to \bC` be an analytic function with isolated
singularities at the points of $`S`.
Then
$$`
\begin{align*}
  \oint_\gamma f(z) \, dz = 2 \pi \ii \sum_{w \in S \cap \Domain} \ResAtOf{w}{f} .
\end{align*}
`
:::

:::proof "thm_jordan_residue_theorem" (uses := "thm_RESIDUE_THEOREM")
…
:::
