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

Design of Mgen
--------------

Mgen is split into a few major parts:

### Data Structures and Types

Located in "smedl/structures".

These are all the classes and types for the internal representations of
monitors, monitoring systems, and all their parts, such as expressions,
monitor declarations, actions, and so on. These are important as they act as the
intermediate representation between the parsers and the code generators.

These are split roughly into three categories, each with their own Python
module:

- **monitor.py** - Classes related to .smedl files
- **arch.py** - Classes related to .a4smedl files
- **expr.py** - Classes related to SMEDL expressions and type checking

### Parsers

Located in "smedl/parser"

The parsers are responsible for reading the input .smedl and .a4smedl files and
generating the data structures in the previous section.

Mgen uses TatSu (formerly Grako) for parsing. With TatSu, the developer writes a
**grammar** in a variant of extended Backus–Naur form (EBNF) specifying the
syntax of the language. The developer then feeds that grammer into TatSu, which
generates Python code to parse the language.

For example, the grammar for .smedl files is "smedl.ebnf", and the parser,
"smedl\_parser.py", is generated from that with
`tatsu -o smedl_parser.ebnf smedl.ebnf`. Then, "smedl\_parser.py" contains a
class `SmedlParser` that can be used to parse .smedl files.

The parser alone simply generates an abstract syntax tree (AST), but the
developer can also create a "semantic actions" class. When provided, this class
can perform extra validations and transformations on the AST, like type
checking. In our case, these semantic actions are what transforms the AST into
the data structures in "smedl/structures", and they work closely with the code
there to accomplish that.

For more information on how TatSu works and how to use it, see "README-tatsu.md"
in the same directory and [the TatSu documentation](https://tatsu.readthedocs.io/en/stable/index.html).

For mgen, there are two parsers, "semdl\_parser.py" and "a4smedl\_parser.py",
generated respectively from "smedl.ebnf" and "a4smedl.ebnf". These both have
their own semantic actions, "smedl\_semantics.py" and "a4smedl\_semantics.py".
Both parsers share some elements, so there is a common grammer, "common.ebnf",
that they both include and both semantic actions inherit from
"common\_semantics.py".

Finally, there is a Python module containing exceptions for use while parsing.
These are for semantic issues like type mismatches, using events that were not
declared, etc.

### Code Generation

Located in "smedl/codegen"

This contains everything responsible for taking the structures from
"smedl/structures" and transforming them into C code for monitors and monitoring
systems. "\_\_init\_\_.py" is the only Python file in this directly (look up
[Python Packages](https://docs.python.org/3/tutorial/modules.html#packages) if
you are unsure why it is named like that). It contains a class, `CodeGenerator`,
that (surprise) manages code generation.

Mgen uses the [Jinja](https://jinja.palletsprojects.com/) templating library
for code generation. Jinja is normally used to generate HTML for web
applications, but it is perfectly suitable for other templating needs, so we
use it to generate C code from templates. Upon initialization, `CodeGenerator`
in turn initializes a new Jinja `Environment` with the appropriate options.
It then provides the appropriate structures (from "semdl/structures") to fill
each template.

The templates reside directly in "smedl/codegen" as .c and .h files. Open them
and you will find they contain many Jinja placeholders and directives in curly
braces. For information on how to read and edit these files, see the [Jinja
Template Designer Documentation](https://jinja.palletsprojects.com/en/2.11.x/templates/).

Please refer also to "README-templates.md" for some tips and important best
practices for template writing.

### "mgen.py" Itself

"mgen.py" is the main driver module. It really has two jobs: 1) parsing command
line options and 2) making calls to the other modules to handle the bulk of the
work.

After parsing the command line options, it initializes the code generator,
calls either the SMEDL parser or the A4SMEDL parser depending on what type of
input file was provided, and then passes the output (which will be objects from
"smedl/structures") to the code generator for transformation to C code.
