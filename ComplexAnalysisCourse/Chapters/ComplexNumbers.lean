import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The complex number system" =>
%%%
file := "complex-numbers"
%%%

# The field of complex numbers

:::definition "def_complex_numbers"
{nodetitle}[Complex numbers and their arithmetic operations] {palka}[Sec. I.1.1]

The set of {term}[complex numbers] is $`\bC = \bR \times \bR`, i.e.,
the set of pairs $`(x,y)` of real numbers $`x,y \in \bR`.

The operations of addition and multiplication on $`\bC` are defined by the formulas
$$`
\begin{align*}
  (x_1,y_2) + (x_2,y_2) = \; & (x_1+x_2, y_1+y_2) \\
  (x_1,y_1) \cdot (x_2,y_2) = \; & (x_1 x_2 - y_1 y_2 , \, x_1 y_2 + y_1 x_2) .
\end{align*}
`

Denote
$`0 = (0,0) \in \bC` and $`1 = (1,0) \in \bC`.

For $`z = (x,y) \in \bC`, denote
$`-z = (-x,-y) \in \bC` and if $`z \ne 0` then denote
$`z^{-1} = \Big(\frac{x}{x^2 + y^2} , \frac{-y}{x^2 + y^2} \Big) \in \bC`.

We write a complex number $`(x,y)` as $`x + \ii \, y`.
The compex number $`\ii = (0,1) \in \bC` is called the {term}[imaginary unit].
:::

Typically used variable names for complex number are $`z,w,\zeta \in \bC` etc.

:::theorem "thm_complex_number_field" (uses := "def_complex_numbers")
{nodetitle}[The field of complex numbers] {palka}[Sec. I.1.1]

The set $`\bC` of compex numbers with its operations of addition and multiplication,
is a {term}[field], i.e., the following properties hold for
all $`z, w, z_1, z_2, z_3 \in \bC`:

* $`z + w = w + z` {term}[(commutativity of addition)]
* $`z w = w z` {term}[(commutativity of multiplication)]
* $`z_1 + (z_2 + z_3) = (z_1 + z_2) + z_3` {term}[(associativity of addition)]
* $`z_1 (z_2 z_3) = (z_1 z_2) z_3` {term}[(associativity of multiplication)]
* $`0 = 0 + 0 \, \ii = (0,0) \in \bC` satisfies $`z + 0 = z`
  {term}[(neutral element for addition)]
* $`1 = 1 + 0 \, \ii = (1,0) \in \bC` satisfies $`z \cdot 1= z`
  {term}[(neutral element for multiplication)]
* $`z + (-z) = 0` for any $`z \in \bC` {term}[(opposite element / additive inverse)]
* $`z \, z^{-1} = 1` for any $`z \in \bC \setminus \set{0}` {term}[(multiplicative inverse)]
* $`(z_1 + z_2) w = z_1 w + z_2 w` {term}[(distributivity)].
:::

:::proof "thm_complex_number_field"
Straightforward calculations using the definitions of the operations
({bpref "def_complex_numbers"}[]).
:::

# Conjugate, modulus, and argument

:::definition "def_complex_conjugate" (uses := "def_complex_numbers")
{nodetitle}[Complex conjugate] {palka}[Sec. I.1.2]

The {term}[complex conjugate] of a complex number $`z = x + \ii y`
(where $`x,y \in \bR`) is the complex number $`\cconj{z} = x - \ii y`.
:::

:::lemma_ "lem_complex_conjugate_properties" (uses := "def_complex_conjugate")
{nodetitle}[Properties of complex conjugate] {palka}[Sec. I.1.2 (1.1)]

For any $`z , w \in \bC`, we have
$$`
\begin{align*}
  \cconj{\cconj{z}} = z , \qquad
  \cconj{z + w} = \cconj{z} + \cconj{w} , \qquad
  \cconj{z w} = \cconj{z} \, \cconj{w} ,
\end{align*}
`
$$`
\begin{align*}
  \re (z) = \frac{z + \cconj{z}}{2} , \qquad
  \im (z) = \frac{z - \cconj{z}}{2 \ii} .
\end{align*}
`
:::

:::proof "lem_complex_conjugate_properties" (uses := "thm_complex_number_field")
Direct calculations.
:::

:::definition "def_absolute_value" (uses := "def_complex_numbers")
{nodetitle}[Absolute value (modulus)] {palka}[Sec. I.1.2]

The {term}[absolute value] (or {term}[modulus]) of a
complex number $`z = x + \ii y` (where $`x,y \in \bR`)
is the nonnegative real number $`|z| = \sqrt{x^2 + y^2} \ge 0`.
:::

:::lemma_ "lem_absolute_value_properties" (uses := "def_absolute_value, def_complex_conjugate")
{nodetitle}[Properties of absolute value] {palka}[Sec. I.1.2 (1.2)]

For any $`z, w \in \bC`, we have
$$`
\begin{align*}
  |z|^2 = z \, \cconj{z} , \qquad
  |z w| = |z| \, |w| ,
\end{align*}
`
$$`
\begin{align*}
  \re(z) \le |z| , \qquad
  \im(z) \le |z| ,
\end{align*}
`
$$`
\begin{align*}
  |z + w| \le |z| + |w| , \qquad
  |z + w| \ge \big| |z| - |w| \big| .
\end{align*}
`
Also, if $`z \ne 0`, then
$$`
\begin{align*}
  z^{-1} = \frac{\cconj{z}}{|z|^2} , \qquad
  \qquad
  \Big| \frac{w}{z} \Big| = \frac{|w|}{|z|} .
\end{align*}
`
:::

:::proof "lem_absolute_value_properties" (uses := "thm_complex_number_field")
Straightforward.
:::

:::definition "def_argument" (uses := "def_complex_numbers, def_absolute_value")
{nodetitle}[Argument] {palka}[Sec. I.1.2]

A real number $`\theta \in \bR` is an {term}[argument] of a complex
number $`z \in \bC` if
$$`
\begin{align*}
  z = |z| \, \Big( \cos (\theta) + \ii \, \sin (\theta) \Big) .
\end{align*}
`

(Note/warning: For a nonzero complex number $`z`,
it is convenient to denote $`\theta = \arg(z)`,
but this is an abuse of notation, the argumentis defined only
modulo addition of integer multiples of $`2 \pi`.)

The {term}[principal argument] of a nonzero complex number $`z \in \bC`
is its unique argument on the interval $`(-\pi, \pi]`, and it is denoted
by $`\Arg(z)`.
:::

:::lemma_ "lem_discontinuity_of_principal_arg" (uses := "def_argument, def_continuous, lem_metric_on_C")
{nodetitle}[Discontinuity of the principal argument]

The principal argument
$`\Arg \colon \bC \setminus \set{0} \to (-\pi,\pi]`
is continuous on the subset $`\bC \setminus (-\infty,0]`, but it is
discontinuous on the negative real axis $`(-\infty,0]`.
:::

# The polar form

:::definition "def_complex_exp" (uses := "def_complex_numbers, thm_complex_number_field")
{nodetitle}[Complex exponential function]

We define the {term}[complex exponential function] $`\exp : \bC \to \bC` by
$$`
\begin{align*}
  \exp(x + \ii y) = e^x \, \big( \cos(y) + \ii \, \sin(y) \big)
  \qquad \text{ for } x,y \in \bR ,
\end{align*}
`
where $`e^x` is the usual real exponential.
We also use the notation $`e^z = \exp(z)` for complex exponentials.

The exponential with purely imaginary argument takes the
form of {term}[Euler's formula]
$$`
\begin{align*}
  e^{\ii \theta} = \cos(\theta) + \ii \, \sin(\theta)
  \qquad \text{ for } \theta \in \bR .
\end{align*}
`
:::

:::lemma_ "lem_complex_exp_properties" (uses := "def_complex_exp")
{nodetitle}[Properties of the complex exponential]

For any $`z,w \in \bC` we have
$$`
\begin{align*}
  e^{z + w} = e^z \, e^w.
\end{align*}
`

For any $`z \in \bC` we have
$$`
\begin{align*}
  e^{\cconj{z}} = \cconj{e^z}, \quad
  |e^z| = e^{\re(z)}, \quad
  \arg(e^z) = \im(z) \modtwopi .
\end{align*}
`

For $`z,w \in \bC` we have
$`e^{z} = e^{w}` if and only if $`z = w + 2 \pi \ii n` for some $`n \in \bZ`.
:::

:::proof "lem_complex_exp_properties" (uses := "lem_trigonometric_angle_sum")
…
:::

:::lemma_ "lem_polar_form" (uses := "def_complex_exp, def_argument, def_absolute_value")
{nodetitle}[Polar form]

Every complex number $`z \in \bC` can be written in the {term}[polar form]
$$`
\begin{align*}
  z = r \, e^{\ii \theta}
  \qquad \text{ where $r \ge 0$ and $\theta \in \bR$.}
\end{align*}
`
The modulus of $`z` is the number $`r = |z|` above.
If $`z \ne 0`, then $`\theta` above is a choice of the argument of $`z`,
i.e., $`\theta = \Arg(z) + 2 \pi m` for some $`m \in \bZ`.
:::

:::proof "lem_polar_form"
…
:::

:::lemma_ "lem_multiplication_polar" (uses := "thm_complex_number_field, lem_polar_form")
{nodetitle}[Multiplication in polar form] {palka}[Sec. I.1.2 (1.6)]

For any $`z,w \in \bC`, written in polar form as
$`z = r e^{\ii \theta}` and $`w = r' e^{\ii \theta'}`, the product
can be written in polar form as
$$`
\begin{align*}
  z w = r r' \, e^{\ii (\theta + \theta')} .
\end{align*}
`
In other words,
$$`
\begin{align*}
  |z w| = |z| \, |w|
  \qquad \text{ and } \qquad
  \arg(z w) = \arg(z) + \arg(w) \modtwopi.
\end{align*}
`
:::

:::proof "lem_multiplication_polar" (uses := "lem_trigonometric_angle_sum")
…
:::

:::theorem "lem_de_moivre" (uses := "thm_complex_number_field")
{nodetitle}[De Moivre's formula] {palka}[Sec. I.1.2 (1.7)]

For any $`\theta \in \bR` and $`n \in \bZ`, we have
$$`
\begin{align*}
  \big( \cos (\theta) + \ii \, \sin (\theta) \big)^n = \cos(n \theta) + \ii \, \sin(n \theta) .
\end{align*}
`
:::

:::proof "lem_de_moivre" (uses := "lem_multiplication_polar")
Induction using {bpref "lem_multiplication_polar"}[].
:::

:::lemma_ "lem_roots_of_unity" (uses := "thm_complex_number_field")
{nodetitle}[Roots of unity]

For any $`n \in \bN`, the solutions $`z \in \bC` to the equation
$$`
\begin{align*}
  z^n = 1
\end{align*}
`
are the $`n` distinct complex numbers
$$`
\begin{align*}
  z_j \, = \, e^{\ii 2 \pi j / n}
      \, = \, \cos \Big( \frac{2 \pi j}{n} \Big) + \ii \, \sin \Big( \frac{2 \pi j}{n} \Big)
  \qquad \text{ where } j = 0, 1, \ldots, n-1 .
\end{align*}
`
These solutions are called the (complex) $`n`th {term}[roots of unity].

In particular, we have the polynomial factorization
$$`
\begin{align*}
  z^n - 1 \, = \, \prod_{j=0}^{n-1} \Big( z - e^{\ii 2 \pi j / n} \Big) .
\end{align*}
`
:::

:::proof "lem_roots_of_unity" (uses := "lem_de_moivre")
…
:::

# Functions of a complex variable

## Polynomials and rational functions

:::definition "def_polynomial" (uses := "thm_complex_number_field")
{nodetitle}[Polynomial]

Polynomial functions are functions $`p : \bC \to \bC` of the form
$$`
\begin{align*}
  p(z) = a_n z^n + a_{n-1} z^{n-1} + \cdots + a_1 z + a_0
\end{align*}
`
where $`a_0,a_1,\ldots,a_{n-1},a_n \in \bC` are coefficients.
:::

:::definition "def_rational_function" (uses := "def_polynomial")
{nodetitle}[Rational function]

Rational functions are functions $`f : D \to \bC` which can be written as
ratios $`f(z) = \frac{p(z)}{q(z)}` of two polynomials
$`p, q \colon \bC \to \bC` on a domain $`D \subset \bC`
where the denominator polynomial $`q` has no zeroes.
:::

## Exponentials and branches of logarithms

:::definition "def_principal_complex_log" (uses := "def_argument")
{nodetitle}[Principal complex logarithm]

The {term}[principal logarithm] is the function
$$`
\begin{align*}
  \Log \colon \; & \bC \setminus \set{0} \to \bC \\
  \Log(z) \, = \; & \log |z| + \ii \, \Arg(z) ,
\end{align*}
`
where $`\log |z|` is the usual natural logarithm of the positive
real number $`|z|>0` and
$`\Arg(z) \in (-\pi,\pi]` is the principal argument of
the nonzero complex number $`z \ne 0`.

(Directly from this definition one sees that for
$`z \in \bC \setminus \set{0}` we have $`e^{\Log(z)} = z`.
All complex solutions $`w` to $`e^w = z` are of the
form $`w = \Log(z) + 2 \pi \ii n` where $`n \in \bZ`.)
:::

:::definition "def_branch_of_log" (uses := "def_complex_exp, def_open_set, def_continuous, def_principal_complex_log")
{nodetitle}[Branches of complex logarithm]

A {term}[branch of the logarithm] is a continuous function
$`\ell \colon U \to \bC` on an open set $`U \subset \bC` such that
$$`
\begin{align*}
  e^{\ell(z)} = z \qquad \text{ for all } z \in U .
\end{align*}
`

For example, the principal logarithm $`\Log`
restricted to the open set $`\bC \setminus (-\infty,0]`
is called the principal branch of the logarithm. Note that
this principal branch cannot be extended continuously to
the negative real axis.

(Note that since $`e^w \ne 0` for all $`w \in \bC`, any branch
of the logarithm must exclude the origin from its domain of
definition, $`0 \notin U`.)
:::

## Complex power functions

:::definition "def_principal_complex_power" (uses := "def_principal_complex_log")
{nodetitle}[Principal complex power function]

Let $`\alpha \in \bC`. The {term}[principal (complex) $`\alpha`th
power function] is the function $`\bC \setminus \set{0} \to \bC`
given by
$$`
\begin{align*}
  z \, \mapsto \, z^\alpha \, := \, e^{\alpha \, \Log(z)} .
\end{align*}
`

(Note: Integer powers have more direct natural definitions.
For $`n \in \bN` we simply define $`z^n` by recursive multiplication
and the function $`z \mapsto z^n` is continuous and defined in
all of $`\bC` and coincides with the principal power function
with $`\alpha = n` on $`\bC \setminus \set{0}`.
We also define $`z^{-n}` by recursive multiplication of the
inverse $`z^{-1}` of $`z`, and the function $`z \mapsto z^{-n}`
is continuous on $`\bC \setminus \set{0}` and coincides with
the principal power function with $`\alpha = -n`.
For $`n = 0` we define $`z^0 = 1` for any $`z \in \bC`, and this
coincides with the principal power function with $`\alpha = 0`
on $`\bC \setminus \set{0}`.)
:::

Given a branch $`\ell \colon U \to \bC` of logarithm on an
open set $`U \subset \bC`, we obtain a branch of the $`\alpha`th power
function on $`U` by the formula $`z \mapsto e^{\alpha \ell(z)}`.
Using the same branch of the logarithm for the
power functions, we have $`z^\alpha z^\beta = z^{\alpha + \beta}`.

## Branches of $`n`th roots

:::definition "def_principal_complex_nth_root" (uses := "def_principal_complex_log, def_principal_complex_power, lem_roots_of_unity")
{nodetitle}[Principal $`n`th root function]

Let $`n \in \bN`. The {term}[principal (complex) $`n`th
root] of $`z \in \bC \setminus \set{0}` is
$$`
\begin{align*}
  \sqrt[n]{z} \; :=  \, z^{1/n} \, = \, e^{\frac{1}{n} \Log(z)} .
\end{align*}
`

(It follows directly from the definition and
the properties of complex exponential that
$`(\sqrt[n]{z})^n = z`.
All complex solutions $`w` to $`w^n = z` are of the
form $`w = \zeta \sqrt[n]{z}` where $`\zeta = e^{2 \pi \ii j / n}`
with $`j = 0, 1, \ldots, n-1`, i.e., $`\zeta` is one of the
$`n` complex $`n`th roots of unity.)
:::
