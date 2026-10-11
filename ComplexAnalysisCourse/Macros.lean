import Verso
import VersoManual
import VersoBlueprint

open Informal

/-!
# TeX macros for all formulae of the course skeleton

This is the one place for LaTeX math macros. Every chapter imports this module.
Each `tex_prelude` chunk is passed to KaTeX (HTML) and to the LaTeX preamble (PDF).

* Add or edit macros here and nowhere else; keep one theme per chunk.
* Macros are ordinary LaTeX (`\newcommand`). KaTeX built-ins such as `\set` cannot be redefined with
  `\newcommand`: use `\def` (works in KaTeX and LaTeX). Unsupported things (e.g. `\mathbbm`) are
  reported as `KaTeX rejected blueprint math` by `lake build`.
* A chunk is a raw string `r#"..."#`; it must not contain the character sequence `"#`.
* After editing, run `python3 scripts/gen_macro_gallery.py` and `lake build`: the gallery module
  uses every macro once, so a broken macro is reported there.
-/

-- Number systems, real and imaginary parts, conjugation
tex_prelude
  r#"\newcommand{\bN}{\mathbb{N}}
\newcommand{\bZ}{\mathbb{Z}}
\newcommand{\bQ}{\mathbb{Q}}
\newcommand{\bK}{\mathbb{K}}
\newcommand{\bR}{\mathbb{R}}
\newcommand{\bC}{\mathbb{C}}
\newcommand{\re}{\Re\mathfrak{e}}
\newcommand{\im}{\Im\mathfrak{m}}
\newcommand{\ii}{\mathfrak{i}}
\newcommand{\cconj}[1]{\overline{#1}}"#

-- Sets, balls, discs, annuli, boundaries and closures
tex_prelude
  r#"\def\set#1{\left\{ #1 \right\}}
\newcommand{\Tri}{\triangle}
\newcommand{\Squ}{\mathcal{S}}
\newcommand{\Rect}{\mathcal{R}}
\newcommand{\Ball}{\mathcal{B}}
\newcommand{\CBall}{\overline{\Ball}}
\newcommand{\PBall}{\Ball^\bullet}
\newcommand{\Sphere}{\mathcal{S}}
\newcommand{\BallRC}[2]{\Ball(#2; #1)}
\newcommand{\CBallRC}[2]{\CBall(#2; #1)}
\newcommand{\PBallRC}[2]{\PBall(#2; #1)}
\newcommand{\SphereRC}[2]{\Sphere(#2; #1)}
\newcommand{\Disk}{\Ball}
\newcommand{\CDisk}{\overline{\Ball}}
\newcommand{\PDisk}{\Ball^\bullet}
\newcommand{\DiskRC}[2]{\Disk(#2; #1)}
\newcommand{\CDiskRC}[2]{\CDisk(#2; #1)}
\newcommand{\PDiskRC}[2]{\PDisk(#2; #1)}
\newcommand{\Ann}{\mathcal{A}}
\newcommand{\AnnRRC}[3]{\Ann_{#1,#2}(#3)}
\newcommand{\Domain}{\mathcal{D}}
\newcommand{\bdry}{\partial}
\newcommand{\closOf}[1]{\overline{{#1}}}"#

-- Calculus: differentials, partial derivatives, smoothness classes
tex_prelude
  r#"\newcommand{\ud}{\mathrm{d}}
\newcommand{\eps}{\varepsilon}
\newcommand{\pder}[1]{\frac{\partial}{\partial {#1}}}
\newcommand{\pdder}[1]{\frac{\partial^2}{\partial {#1}^2}}
\newcommand{\pmder}[2]{\frac{\partial^2}{\partial {#1} \, \partial {#2}}}
\newcommand{\pderof}[2]{\frac{\partial {#1}}{\partial {#2}}}
\newcommand{\pdderof}[2]{\frac{\partial^2 {#1}}{\partial {#2}^2}}
\newcommand{\pmderof}[3]{\frac{\partial^2 {#1}}{\partial {#2} \, \partial {#3}}}
\newcommand{\Cont}{\mathcal{C}}
\newcommand{\ContDiff}[1]{\Cont^{{#1}}}
\newcommand{\Smooth}{\ContDiff{\infty}}"#

-- Paths and winding numbers
tex_prelude
  r#"\newcommand{\opp}[1]{\overleftarrow{#1}}
\newcommand{\concat}{\oplus}
\newcommand{\windNsym}{\mathfrak{n}}
\newcommand{\windN}[2]{\mathfrak{n}_{{#1}}(#2)}"#

-- Residues
tex_prelude
  r#"\newcommand{\Res}{\mathrm{Res}}
\newcommand{\ResAt}[1]{\Res_{{#1}}}
\newcommand{\ResAtOf}[2]{\Res_{{#1}}({#2})}"#

-- Branches of argument and logarithm
tex_prelude
  r#"\newcommand{\Arg}{\mathrm{Arg}}
\newcommand{\Log}{\mathrm{Log}}
\newcommand{\modtwopi}{\;\;(\mathrm{mod}~2\pi)}"#

-- Uniform convergence on compacts and metric spaces
tex_prelude
  r#"\newcommand{\UOC}{\mathrm{UOC}}
\newcommand{\genmet}{\mathsf{d}}
\newcommand{\genspace}{\mathfrak{X}}"#

-- Not used by the current text (left over from an earlier project); kept so that old formulae keep working - prune freely
tex_prelude
  r#"\newcommand{\gLie}{\mathfrak{g}}
\newcommand{\hLie}{\mathfrak{h}}
\newcommand{\aLie}{\mathfrak{a}}
\newcommand{\wittLie}{\mathfrak{witt}}
\newcommand{\virLie}{\mathfrak{vir}}
\newcommand{\cohomology}[3]{H^{{#1}}(#2,#3)}
\newcommand{\cobdries}[3]{B^{{#1}}(#2,#3)}
\newcommand{\cocycles}[3]{C^{{#1}}(#2,#3)}"#
