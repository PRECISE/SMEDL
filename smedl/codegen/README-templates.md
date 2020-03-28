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

    {% for item in items %}
        {{item}}
    {% endfor %}

If `items` is `["foo", "bar", "baz"]`, the result will look like:

    foo
    bar
    baz

If each item should not get its own line, consider using minus signs to strip
more whitespace than `trim_blocks` and `lstrip_blocks` do by default or simply
placing the block opener, body, and closer all inline.
