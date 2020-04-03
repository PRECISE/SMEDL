Template Writer's README
========================

Templates all reside in the current directory and become part of the
`smedl.codegen` package. The templating engine SMEDL uses is Jinja. See [the
Jinja docs](https://jinja.palletsprojects.com/) for information on the
template syntax.

Contained within this document are further hints and guidelines to assist in
maintaining the templates.

Identifiers
-----------

Identifiers in C and C++ sometimes follow some common conventions (though this
is certainly not always the case--the rules are far from standardized, unlike
other languages):

* Constants (including enum constants) and macros in `ALL_CAPS`
* Enum, union, and struct names in `TitleCase`
* Function, variable, and member names in `snake_case`

These are the conventions used by the generated code where possible; however,
in cases where a C identifier derives from a SMEDL/A4SMEDL identifier, the case
will be preserved precisely from the SMEDL/A4SMEDL identifier. This is because
SMEDL/A4SMEDL identifiers are case-sensitive, requiring it to be preserved.
Otherwise, for example, state variables named `myvar` and `myVar` would collide.

Furthermore, identifiers that would normally be `TitleCase` will sometimes
contain underscores when there are multiple placeholders back-to-back. For
example, from "mon.h", `{{spec.name}}_{{scenario.name}}_State`. Without an
underscore between back-to-back placeholders, names could collide, such as
spec.name=`abc`/scenario.name=`de` and spec.name=`ab`/scenario.name=`cde`.

Finally, care must be taken that no C identifier starts with double-underscore
and no C identifier with external visibility starts with an underscore at all.
Both are reserved by the C standard. This generally should not be difficult.
Identifiers appearing in SMEDL/A4SMEDL specs cannot start with underscore, but
some automatically generated names (such as implicit state names) will start
with underscore.

Whitespace
----------

Jinja provides two methods to control whitespace:

* `trim_blocks` and `lstrip_blocks` options - When set to true, this causes
  leading whitespace and a trailing newline to be stripped from any line with
  a block opening or closing (`{% ... %}`).

* Plus and minus signs - When a minus sign is added after the opening percent
  or before the closing percent in a block delimiter (`{%-` or `-%}`), that
  will cause *all* preceding or trailing whitespace to be trimmed, respectively.
  This includes any newlines. Plus signs cancel the effects of `trim_blocks` or
  `lstrip_blocks`.

The `trim_blocks` and `lstrip_blocks` options are turned on for SMEDL code
generation, so most block openings and closings should go on their own line and
be indented properly. The contents of blocks will retain their indentation and
for loop iterations will be separated by a line break. For example:

    if (test == 1) {
        {% for func in functions %}
        {{func}}();
        {% endfor %}
    }

If `functions` is `["foo", "bar", "baz"]`, the result will look like:

    if (test == 1) {
        foo();
        bar();
        baz();
    }

If each item should not get its own line, consider using minus signs to strip
more whitespace than `trim_blocks` and `lstrip_blocks` do by default, or simply
placing the block opener, body, and closer all inline.

Template logic vs. Python logic
-------------------------------

Jinja templates are quite flexible and can do a certain amount of processing on
their own, but take care not to have the templates doing more computation than
necessary. The line to draw is this: Python code should not be handling C code
directly. If logic cannot be moved out of the template without breaking that
rule, then the logic belongs in the template. Otherwise, it belongs somewhere in
the Python code.

For example, the expression and action generation macros in the "mon.c" template
are very complex and logic-heavy. That is a sign to consider whether some of
that logic should be moved to Python code instead. However, in this case, the
logic directly handles C code. There would be no way to move it to the
`Expression` and `Action` classes without having those classes handle snippets
of C code, so placing the logic in the template is in fact the correct decision.

A good test for this is to ask yourself the question, "If we wanted to generate
a language other than C, would we be able to accomplish that purely with a new
set of templates?" If the answer is no, then that is a sign that the Python code
is doing something that should be the templates' job.
