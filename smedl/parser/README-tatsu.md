TatSu Notes
===========

The TatSu homepage can be found [on GitHub](https://github.com/neogeny/TatSu)
and the docs can be found at [ReadTheDocs.io](https://tatsu.readthedocs.io/).
Here, we have some additional notes to explain aspects of TatSu that may not be
immediately clear from those docs.

Note: TatSu is the replacement for the Grako project. There may be references to
Grako scattered about the code or docs, but they should be interchangeable with
TatSu.

TatSu ASTs
----------

A TatSu AST can actually be one of four types:

* **An `AST` proper** - This is a tree node with named children.
* **A `list`** - This is a tree node with unnamed children.
* **A `string`** - This is a leaf node.
* **`None`** - This is a leaf node where nothing was matched (when the grammar
allows that).

For the sake of clarity, the rest of this document will use "parse tree" to
refer to the abstract syntax tree a TatSu parser generates, i.e. a tree
consisting of any of the above types. `AST` will refer specifically to the `AST`
type.

When using a TatSu parser, you specify which rule from the .ebnf file to start
with as the top-level rule. If you do not explicitly specify, TatSu assumes you
have a rule named `start` and uses that. (Thus, it will raise an exception if
there is no rule named `start` and you don't explicity specify another!)
Whichever rule you specify represents the root of the parse tree and the
resulting parsed object will be one of the three types above.

Which of the three types is determined as follows:

1. If the rule has any matching components that are named (that is, the
component has a colon `:` except for `@:`, e.g. `event_id:identifier`), the
result will be an `AST` containing only the named components.

2. If the rule has no matching components and that is permitted by the rule, the
result will be `None`.

3. If the matching components of the rule are all unnamed, then the result will
be a list, unless there is only one component.

4. If there is only one component matched (e.g. `"foo"`, a single word), the
result will simply be that matched component as a singleton, not a list. If that
component is a string, the result will be a string. If it is a subrule, it will
be whatever the result of that subrule is.

`AST` Type
----------

The `AST` type is similar to a dict. It contains named values representing its
children in the tree. The values can be accessed using regular dict notation:

    some_ast['child_name']

However, ASTs also allow access using object-member notation:

    some_ast.child_name

Finally, when accessing a child that does not exist, rather than raising
`ValueError` like a normal dict, an `AST` will simply return `None`. This is
useful because it means if a rule has an optional portion, trying to access
components from that portion will simply return None instead of raising an
exception.

Semantic Actions
----------------

This is a very powerful feature of TatSu providing for easy processing of the
AST as it is being parsed. See the section of the TatSu docs on this for more
information.

The idea is that you provide to TatSu a semantics class with methods for the
various rules in the grammar. When a rule parses, TatSu will call the matching
method if it exists. This is useful for any number of post-processing tasks,
but we use it for extra validations (e.g. that a target monitor or event exists)
and to transform the AST into more useful data structures, like synchronous set
lists and symbol tables.

The result is that instead of the parser returning the AST directly, it passes
the AST to these methods, and then whatever these methods return is returned by
the parser. That can be the same AST, a transformed AST, or a totally different
object altogether.
