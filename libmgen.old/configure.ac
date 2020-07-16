AC_PREREQ(2.69)
AC_INIT([mgen], [0.1], [pgeb@seas.upenn.edu])
AM_INIT_AUTOMAKE([-Wall -Werror foreign])
AC_CONFIG_SRCDIR([src/monitor_map.h])
AC_CONFIG_HEADERS([config.h])

AC_PROG_CC
AM_PROG_AR

AC_CHECK_HEADERS([stdint.h stdlib.h sys/time.h])

AC_TYPE_SIZE_T
AC_TYPE_UINT64_T

AC_FUNC_MALLOC
AC_CHECK_FUNCS([gettimeofday])

AC_PROG_RANLIB
AC_CONFIG_FILES([
Makefile
src/Makefile
])
AC_OUTPUT
