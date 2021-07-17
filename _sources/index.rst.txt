SMEDL
=====

Scenario-based Meta Event Language (SMEDL) is a `runtime verification`_
framework for specifying monitors using an EFSM-style formalism, generating C
executable monitor code from specifications, and deploying the monitors in
centralized or distributed settings.

* The monitor specification language is suitable for both high-level temporal
  properties and low-level properties described as explicit state transitions
  with imperative actions such as logic or arithmetic computations.
* Multiple monitors can be instantiated during runtime to form a
  dynamically-scaling monitor network.
* Users can flexibly specify that monitors in a network be deployed with
  synchronous or asynchronous event passing between each other and the target
  system.

This notion of monitor networks provides a unified way to compose verdicts of
properties and allows for monitoring parametric properties. It is flexible
enough to adapt to a variety of software systems, such as single-process
programs or distributed software.

.. _runtime verification: https://runtime-verification.github.io/

User Manual
-----------

This manual consists of two parts. The first part describes how to write a
monitor system in the SMEDL specification language. The second part is about
integrating monitors into your existing code.

.. toctree::
   :maxdepth: 2

   language/index
   api/index

Index
-----

* :ref:`genindex`
* :ref:`search`
