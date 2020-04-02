Changelog
=========

[Unreleased] - Future 2.0.0
---------------------------

This is a major rewrite of SMEDL to add several new features and fix various
issues with the code.

### Added

- A full synchronous communication API is now available, both at the monitor
  level (for single monitors) and the global wrapper level (for monitoring
  systems). RabbitMQ transport is still available for asynchronous
  communication, now via an optional, auto-generated adapter built on top of
  said API.
- The same monitor specification can be used multiple times in one architecture
  file.
- A new type of connection target is available in architecture files: monitor
  creation. This differs from creation events (which are no longer explicit, see
  below) because:
  1. The monitor is simply created and left in its initial state. No event need
     be sent to it.
  2. It provides a mechanism for state variables to be initialized to custom
     values.
- Type checking for expressions and monitor/event parameters

### Changed

- The architecture file format (.a4smedl) has seen major changes:
  * Monitors' imported and exported events are no longer added directly into the
    architecture file. Rather, an `import "somemonitor.smedl"` statement
    references the monitor specification directly.
  * The syntax for connections between events is significantly changed. The new
    syntax is more flexible and intuitive.
  * The "creation" keyword has been removed. All events can be creation events,
    and will be if the monitor identity parameters are all non-wildcards.
- Monitor identities are now specified exclusively in the architecture file. The
  `identity` section has been removed from monitor specifications.
- Names differing only in case will no longer result in uncompileable output
- The parser has been fixed to allow complete expressions in places where they
  used to trigger errors.
- Command line options for `mgen` have changed. Input may be either an
  architecture file (.a4smedl) or a single monitor specification (.smedl). When
  an architecture file is provided, all monitors it imports will be generated
  automatically.

### Removed

- Final states. This will be reimplemented soon.
- PEDL. This was rarely used in its old form, if at all. It is not clear that it
  was even fully implemented. Further design planning and discussion will be
  necessary before reimplementation.
