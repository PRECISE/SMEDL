Coq Formalization of SMEDL
==========================

This directory contains a Coq formalization of the SMEDL monitoring language. At
the moment, the language formalized here is only a fragment of what is available
using the `mgen` tool or as part of the LaTeX formalization available in the
rings repository. The fragment includes local monitors, with an expression
language with some basic boolean and arithmetic operations, and a command
language that can raise events and assign to global variables.

File structure
--------------

Types.v contains the basic types available for programming in SMEDL. At the
moment, those types consist of products of integers, floats, and booleans.

AST.v contains the syntax for
* expressions,
* commands,
* transitions and scenarios,
* global variable declarations, and
* event declarations.
Input, output, and internal events are not currently distinguished.

VarEnv.v and EventEnv.v contain machinery for managing type environments.

Typing.v contains the definition of a well-typed SMEDL local monitor.

TypingFacts.v contains some basic facts about the well-typed SMELD monitors.

Machine.v contains a very general Mealy machine definition. It is used in
Semantics.v to assign Mealy machine semantics to the local monitors.

These.v is a helper for implementing an error-reporting type-checker for SMEDL
monitors. It is not currently used because there is not currently a type-checker implementation.
