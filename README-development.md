Development Notes
=================

This document contains notes to help future developers get up to speed on the
project.

Best Practices
--------------

The practices below are not necessarily specific to this project, but will help
make future usage and maintenance easier and should not generally be ignored.

### General

- Make liberal use of comments. Six-month future you will thank you. In
  particular:
    * Each C function should have a comment describing what it does, its
      parameters, and its return value. Python functions should have the same
      information in a docstring.
    * Each source code file and class should typically have a comment or
      docstring, as well.
    * Class members should often receive comments describing what they are and
      how they are used.
- Use descriptive names. Abbreviations are okay if they are painfully obvious,
  but consider whether they really will be *painfully* obvious when you return
  to the code six months later.
- DRY (Don't Repeat Yourself). Any time you find yourself writing substantially
  similar code more than once, or especially if you are copying and pasting,
  consider whether the code can be spun off into a function, stored in a
  local variable, etc.
- Clever hacks are satisfying to write, but require a lot of mental capacity
  six months down the line when you (or the next person) is trying to figure out
  how they work again. Consider whether they really add value. In particular:
    * Python's list comprehensions and generator expressions are ripe for this
      kind of abuse. Don't go overboard with them.
    * C provides plenty of opportunities to write terse, difficult to read code.
      It is especially tempting when you know it can cut out a few operations.
      Resist the urge. Modern compilers have great optimizers.
- Keep clean code. Indent properly, follow case conventions, wrap long lines of
  code manually. Python provides a style guide in
  [PEP 8](https://www.python.org/dev/peps/pep-0008/).
- Generated code should adhere to these rules as well. Machine generation is not
  an excuse to be sloppy. The purpose of this tool is to generate code for other
  people, so readability is important.

### Releases

When making a release:

1. Pick an appropriate version number. [Semantic
   versioning](https://semver.org/) is strongly encouraged: "Major.minor.patch".
   Bump the major version whenever backward compatibility breaks. Bump the
   minor version whenever adding new features. Bump the patch version when
   simply making a bugfix release.

2. Make sure the documentation is up-to-date. A new feature is not complete
   until it is fully documented. More on documentation in the next section.

3. Update the changelog. Ideally, this should be done during development, adding
   details under the [Unreleased] section. But in either case, make sure all the
   relevant details are there, change [Unreleased] to the version number, and
   add the date of release. Start a new [Unreleased] section after the release.

TODO semantic versioning, changelog, metadata and version stuff to update, other
info on how to do releases

### Documentation

TODO

Design of mgen
--------------
