Changelog
=========

[Unreleased]
------------

[2.0.1] - 2021-07-07
--------------------

### Fixed

- Updated MANIFEST.in to include docs and tests in source distributions

[2.0.0] - 2021-07-06
--------------------

This is a major rewrite of SMEDL to add several new features and fix various
issues with the code.

### Added

- A full synchronous communication API is now available, both at the monitor
  level (for single monitors) and the global wrapper level (for monitoring
  systems). RabbitMQ transport is still available for asynchronous
  communication, now via an optional, auto-generated adapter.
- In addition to the RabbitMQ adapter, a ROS adapter is available. This
  generates a complete ROS package with a node for each syncset instead of a
  simple set of .c/.h files.
- The same monitor specification can be used multiple times in one architecture
  file.
- A new type of connection target is available in architecture files: monitor
  creation. This differs from creation events (which are no longer explicit, see
  below) because:
  1. The monitor is simply created and left in its initial state. No event need
     be sent to it.
  2. It provides a mechanism for state variables to be initialized to custom
     values.
- Exported PEDL events can be given names
- Type checking for expressions and monitor/event parameters
- Makefiles are generated with the monitor code. These can be used as-is or
  provide inspiration for integrating monitors into a larger build system.

### Changed

- The architecture file format (.a4smedl) has seen major changes:
  * Monitors' imported and exported events are no longer added directly into the
    architecture file. Rather, an `import "somemonitor.smedl"` statement
    references the monitor specification directly.
  * The syntax for connections between events is significantly changed. The new
    syntax is more flexible and intuitive.
  * The "creation" keyword has been removed. All events can be creation events,
    and will be if the monitor identity parameters are all non-wildcards.
  * PEDL events can be added to specific synchronous sets
  * Exported PEDL events can be routed to explicitly
- The C API has seen major changes as well:
  * PEDL events now sit inside the global wrapper they belong to. They use the
    same API as monitors importing and exporting events.
  * There is a new manager level to the SMEDL design, sitting outside the
    global wrapper and managing the communication between it and the transport
    adapters (e.g. RabbitMQ). This allows for a future update where a global
    wrapper may communicate with other global wrappers through different
    transports simultaneously (e.g. one syncset uses RabbitMQ, another uses
    ROS).
  * The target program must call `run_manager()` explicitly. SMEDL no longer
    processes PEDL events as soon as they are raised.
- Monitor identities are now specified exclusively in the architecture file. The
  `identity` section has been removed from monitor specifications.
- Names differing only in case will no longer result in uncompileable output
- The parser has been fixed to allow complete expressions in places where they
  used to trigger errors.
- Command line options for `mgen` have changed. Input may be either an
  architecture file (.a4smedl) or a single monitor specification (.smedl). When
  an architecture file is provided, all monitors it imports will be generated
  automatically.
- A better hashmap implementation for monitor instance management brings
  massive performance improvements, especially for monitors with more than one
  identity parameter.
- Various bugs and memory leaks have been fixed.

### Removed

- PEDL, in its old form. "PEDL events" live on as the events to and from the
  target program, but it is up to the user to instrument the target program or
  otherwise tie them in to the target system as necessary.
- Thread type for variables and parameters.

[1.1.1] - 2019-12-13
--------------------

This is the first version in the changelog, and the last version of SMEDL 1.x.

### Changed

- Parts of the API have been updated for easier integration with other code
- A synchronous interface to the global wrapper was added for less overhead
  between the monitoring system and the target system

[Unreleased]: https://gitlab.precise.seas.upenn.edu/smedl/smedl/compare/master...v2.0.1
[2.0.1]: https://gitlab.precise.seas.upenn.edu/smedl/smedl/compare/v2.0.1...v2.0.0
[2.0.0]: https://gitlab.precise.seas.upenn.edu/smedl/smedl/compare/v2.0.0...v1.1.1
[1.1.1]: https://gitlab.precise.seas.upenn.edu/smedl/smedl/-/tags/v1.1.1
