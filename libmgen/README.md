# libmgen

This package contains the C library and header files necessary to compile and
run mgen-generated SMEDL monitors.

* `actions.h` is a stack specialized for SMEDL monitor actions.
* `monitor_map.h` is a dictionary for tracking SMEDL monitor identities.
* `utils.h` contains helper functions for communicating with RabbitMQ.

## Installation

If you are building from the repository, create the build scripts with

```bash
./bootstrap
```

If you are building from a distribution, this has already been done for you.

To build and install, run

```bash
./configure
make
sudo make install
```

This will install `libmgen.so` and `libmgen.a` in `/usr/local/lib` and the
header files in `/usr/local/include`. To modify the installation location, use
the `--prefix` option to `./configure`.

## Dependencies

Monitors created with `mgen` will also depend on other libraries, such as
[`libconfig`](https://github.com/hyperrealm/libconfig) and
[`librabbitmq`](https://github.com/rabbitmq/rabbitmq-c), which can be found in
your system's package manager.

## Static linking

When linking `mgen`-generated monitor C code, include `libmgen.a` to link
statically. For example,

```bash
gcc -o mymonitor mymonitor.c mymonitor_mon.c -lmgen -lrabbitmq -lconfig
```

## Developing

See `DEVELOPING` to get started.
