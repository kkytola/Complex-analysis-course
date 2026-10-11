import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles
import ComplexAnalysisCourse.Chapters.ComplexNumbers
import ComplexAnalysisCourse.Chapters.ComplexDerivative
import ComplexAnalysisCourse.Chapters.ContourIntegration
import ComplexAnalysisCourse.Chapters.CauchyTheorem
import ComplexAnalysisCourse.Chapters.PowerSeries
import ComplexAnalysisCourse.Chapters.Singularities
import ComplexAnalysisCourse.Chapters.TopologyBackground
import ComplexAnalysisCourse.Chapters.CalculusBackground

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "MS-C1300 Complex Analysis" =>
%%%
authors := ["Kalle Kytölä"]
%%%

This document is a skeleton of the theoretical content of
the Fall 2024 course MS-C1300 Complex Analysis at Aalto University.
The skeleton includes statements of results and their
logical interdependencies, but no proofs, no examples, and no
visualizations.

Instead, the hand-written lecture notes on the course home page correspond
to the contents of the lectures. They include discussions of examples and
informal ideas as well as the main theorems and their proofs.
This theory skeleton is meant to complement the lectures as
an organizational document: to indicate the flow of the theory
development, and to clarify the main goals of the course and the
purposes of the intermediate results.

An attempt is made to provide references to corresponding parts of
the textbook: _An Introduction to Complex Function Theory_
(Undergraduate Texts in Mathematics) by Bruce Palka.

This skeleton is work in progress. It is guaranteed to contain mistakes,
the number and severity of which will be reduced with updates
during the course. Please inform the lecturer Kalle Kytölä of
errors that you notice!

{include 0 ComplexAnalysisCourse.Chapters.ComplexNumbers}

{include 0 ComplexAnalysisCourse.Chapters.ComplexDerivative}

{include 0 ComplexAnalysisCourse.Chapters.ContourIntegration}

{include 0 ComplexAnalysisCourse.Chapters.CauchyTheorem}

{include 0 ComplexAnalysisCourse.Chapters.PowerSeries}

{include 0 ComplexAnalysisCourse.Chapters.Singularities}

{include 0 ComplexAnalysisCourse.Chapters.TopologyBackground}

{include 0 ComplexAnalysisCourse.Chapters.CalculusBackground}

{blueprint_graph}
