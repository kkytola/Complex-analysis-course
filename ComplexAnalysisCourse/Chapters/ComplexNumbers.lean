import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The complex number system" =>

:::group "grp_complex_numbers"
The complex number system
:::

# The field of complex numbers

:::definition "def_complex_numbers" (parent := "grp_complex_numbers")
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

:::theorem "thm_complex_number_field" (parent := "grp_complex_numbers") (uses := "def_complex_numbers")
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
