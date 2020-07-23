Development Notes
=================

This document contains notes to help future developers get up to speed on the
project. Some of these are general best practices, others are notes specific
to this project.

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

### Documentation

TODO

Git Branching and Tagging
-------------------------

Git branches are often underutilized, but they can make managing the project
far easier.

We have two main branches in our repository:
- `master`: Should always be at the latest release, which should be tagged
- `develop`: Contains the latest updates, but *should always be in a working
  state.* Meaning, all tests should be passing. If they are not, they should be
  fixed immediately, or the changes rolled back until they can be.

Commits to these two branches will always trigger CI, running the automated
tests, so if there is a problem, you can fix it immediately.

### Adding a new feature

When developing a new feature, *always* start a new branch from `develop`. This
way, you can freely make commits that might break the code without interfering
with other features you might be developing at the same time. Once your new
feature is tested and working, you can merge it back into `develop` and delete
the branch if you like. Or, if the feature doesn't work out, you can delete the
branch without ever merging it. Here are some commands that might help with
this:

```sh
# Start from the develop branch
git checkout develop
# Check out a newly-created (-b) branch for your new feature
git checkout -b my-new-feature
# Make some changes, add some commits, then...
# Push the branch to GitLab (you can do this at any time if you like, e.g.
# to sync your work between multiple computers, as a backup, or to share
# your progress, but it's only required when the feature is ready)
git push -u origin my-new-feature
# If you make more commits, you can push again like normal
git push
```

To test your feature, you can run tests on your own computer (see the "Testing"
section here and in the main README), but also, any commit you push that
contains "run ci" will have the full tests run on the server. Be sure also to
add the new feature to the changelog and update the documentation. When your
new feature is ready to merge into `develop`, you have two options:

- [Create a merge request on the GitLab website.][merge-request] This gives
  other people a chance to review the changes if that would be helpful.
- Merge in your own repository and then push the `develop` branch:

  ```sh
  git checkout develop
  git merge my-new-feature
  git push
  ```

Once the changes are merged (if if you decide to abandon the feature without
merging), you can delete the branch if you like (or you can also delete from
gitLab without deleting from your own computer):

```sh
# Delete from GitLab
git push -d origin my-new-feature
# Delete from your own computer
git branch -d my-new-feature
```

### Fixing a Bug

TODO

- Create a branch from `master`, `bugfix-<something>` (the `bug*` prefix
tells CI to run with every push)
- Add new tests for the bug, if at all possible
- Make the fixes
- Bump the version number and update the changelog
- Push
- Merge into `master` and `develop`, tag the `master` commit and add release
  notes if desired

### Making a release

- Bump the version number and update the changelog to contain the new version
- Merge `develop` into `master`
- Tag the `master` commit and add release notes if desired
- Add a new "unreleased" section to the changelog

Releases
--------

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

New Python Versions
-------------------

[Roughly every October, a new major version of Python is released. From time to
time, old Python versions reach end-of-life, as well.][python-cycle] An ideal
goal would be to support all active Python versions, or at least all versions
currently receiving bugfixes. Our CI tools help with this greatly by testing
against multiple Python versions when we merge into the main development
branch.

When a new Python version is released (or an old version reaches end-of-life),
there are two lists of Python versions that need to be updated: the list in
`tox.ini` and the list in `tests/docker/Dockerfile`. The latter then needs to
be used to build a new Docker image: see "Updating the Docker Image."

There may be certain workarounds or version-dependent hacks that can be removed
when old Python versions reach end-of-life, such as dependencies in `setup.py`
that are only required for old versions of Python.

Testing and CI
--------------

TODO Note different examples of useful commands and techniques for testing

### Updating the Docker Image

GitLab CI/CD uses Docker to provide the environment for CI/CD scripts. Docker
images are pulled from Docker Hub.

In a perfect world, we would use one of the official `python` docker images,
but unfortunately, they only contain one version of Python each, and we want to
test against all active Python versions. So, we have a Dockerfile,
`tests/docker/Dockerfile`, to build a custom image that includes multiple
Python versions and all the build dependencies for our monitors.

Ideally, GitLab CI would let you use a Dockerfile instead of just an image. [It
currently does not.](https://gitlab.com/gitlab-org/gitlab/-/issues/22801) Next
best thing would be using GitLab's built-in [Container Registry](https://docs.gitlab.com/ee/user/packages/container_registry/index.html).
Unfortunately, that's not enabled, either. So, we are just using an image
uploaded to Docker Hub on a personal account.

TODO when to do this?

    docker login
    docker build -t <username>/<repo> - < Dockerfile
    docker tag <username>/<repo> <username>/<repo>:YYYY.MM.DD
    docker push <username>/<repo>

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

[python-cycle]: https://www.python.org/dev/peps/pep-0602/
[merge-request]: https://docs.gitlab.com/ee/user/project/merge_requests/creating_merge_requests.html
