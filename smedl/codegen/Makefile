# Uncomment to customize these variables
#CC=cc
#CXX=g++
#CPPFLAGS:=$(CPPFLAGS)
#CFLAGS:=$(CFLAGS)
#LDFLAGS:=$(LDFLAGS)
#LDLIBS:=$(LDLIBS)
#RM=rm -f

# If any monitors use helper functions, add the C/C++ source code files to the
# variable(s) below (must be .c, .cc, .cpp, or .C files)
{% for spec in spec_names %}
EXTRA_SOURCES_{{spec}}=
{% endfor %}

# The syncset(s) named below contain PEDL events (i.e. events to/from the
# target system). A basic stub to interface with these events is included, but
# chances are, it will need to be modified to plug in to the rest of your
# application. (By default, it reads input events from a basic CSV file and
# prints output events to stdout, primarily for demonstration purposes.)
#
# If the only syncset listed below is "pedl", all PEDL events are asynchronous.
# You may wish to ignore the "pedl" executable produced by this Makefile and
# integrate pedl*.c/.h into your application's normal build system. Or you can
# ignore them entirely and interface with the underlying message transport
# directly (this is particularly useful with ROS, where the generated
# configuration header allows you to specify the particular topic and fields
# for each event).
#
# If there are syncsets besides "pedl" listed, this Makefile may be of limited
# use to you, since those syncsets all need tighter integration with your
# existing application.
#
{% for syncset in pedl_syncsets %}
# * {{syncset}}
{% endfor %}

# Uncomment the first for a debug build. Uncomment the second for a release
# (optimized) build. DEBUG flag can be adjusted as necessary:
# -DDEBUG=0: Debug off (same as not defining DEBUG at all)
# -DDEBUG=1: Errors only (Serious errors will be printed even with debug off)
# -DDEBUG=2: Warnings (Non-serious abnormal conditions)
# -DDEBUG=3: Notice (Significant but normal occurrences)
# -DDEBUG=4: Debug (All debug messages on)
CFLAGS:=-g -DDEBUG=4 $(CFLAGS)
#CFLAGS:=-O2 -DNDEBUG $(CFLAGS)

# Where to place all object files, dependency makefiles, and executables.
# For example, to place everything in a "build" directory:
#BUILD_DIR=./build
BUILD_DIR=.

# Changes below this line not recommended
###############################################################################

{% if transport == 'rabbitmq' %}
LDLIBS:=$(LDLIBS) -lrabbitmq
{% endif %}

COMMON_SOURCES=smedl_types.c event_queue.c monitor_map.c global_event_queue.c
{%- if not all_sync %}
{%- if transport == 'rabbitmq' %}
 cJSON.c
{%- endif %}
{% endif %}

{% for syncset in syncsets %}
SOURCES_{{syncset}}=
{%- for spec in syncset_specs[syncset] %}{% if not loop.first %} {%+ endif %}{{spec}}_mon.c{% endfor %}
{%- for mon in syncset_mons[syncset] %} {{mon}}_local_wrapper.c{% endfor %}
 {{syncset}}_global_wrapper.c {{syncset}}_manager.c
{%- if not syncset.pure_sync %}
{% if transport == 'rabbitmq' %} {{syncset}}_rabbitmq.c{% endif %}
{%- endif %}
{%- if syncset in pedl_syncsets %} {{syncset}}_stub.c{% endif %}

{% endfor %}
SMEDL_SOURCES=$(COMMON_SOURCES)
{%- for syncset in syncsets %} $(SOURCES_{{syncset}}){% endfor %}


SMEDL_OBJS=$(SMEDL_SOURCES:.c=.o)
SMEDL_OBJS:=$(SMEDL_OBJS:%=$(BUILD_DIR)/%)

{% for syncset in syncsets %}
OBJS_{{syncset}}=$(COMMON_SOURCES){% for spec in syncset_specs[syncset] %} $(EXTRA_SOURCES_{{spec}}){% endfor %} $(SOURCES_{{syncset}})
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.c=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.cc=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.cpp=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.C=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:%=$(BUILD_DIR)/%)
{% endfor %}

EXTRA_SOURCES=
{%- for spec in spec_names %}
{% if not loop.first %} {% endif %}$(EXTRA_SOURCES_{{spec}})
{%- endfor %}

EXTRA_SOURCES:=$(sort $(EXTRA_SOURCES))
EXTRA_OBJS=$(EXTRA_SOURCES)
EXTRA_OBJS:=$(EXTRA_OBJS:.c=.o)
EXTRA_OBJS:=$(EXTRA_OBJS:.cc=.o)
EXTRA_OBJS:=$(EXTRA_OBJS:.cpp=.o)
EXTRA_OBJS:=$(EXTRA_OBJS:.C=.o)
EXTRA_OBJS:=$(EXTRA_OBJS:%=$(BUILD_DIR)/%)

SOURCES=$(SMEDL_SOURCES) $(EXTRA_SOURCES)
OBJS=$(SMEDL_OBJS) $(EXTRA_OBJS)
DEPS=$(OBJS:.o=.d)

.PHONY: all clean

all:{% for syncset in syncsets %} $(BUILD_DIR)/{{syncset}}{% endfor %}
{% for syncset in syncsets %}

$(BUILD_DIR)/{{syncset}}: $(OBJS_{{syncset}})
	mkdir -p $(@D)
	$(CC) $(LDFLAGS) $+ $(LDLIBS) -o $@
{% endfor %}

$(SMEDL_OBJS): $(BUILD_DIR)/%.o: %.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) -MMD -MP $(CFLAGS) -std=c99 -c $< -o $@

$(BUILD_DIR)/%.o: %.c
	mkdir -p $(@D)
	$(CC) $(CPPFLAGS) -MMD -MP $(CFLAGS) -c $< -o $@

$(BUILD_DIR)/%.o: %.cc
	mkdir -p $(@D)
	$(CXX) $(CPPFLAGS) -MMD -MP $(CXXFLAGS) -c $< -o $@

$(BUILD_DIR)/%.o: %.cpp
	mkdir -p $(@D)
	$(CXX) $(CPPFLAGS) -MMD -MP $(CXXFLAGS) -c $< -o $@

$(BUILD_DIR)/%.o: %.C
	mkdir -p $(@D)
	$(CXX) $(CPPFLAGS) -MMD -MP $(CXXFLAGS) -c $< -o $@

clean:
	$(RM) $(OBJS) $(DEPS)
	{%- for syncset in syncsets %} $(BUILD_DIR)/{{syncset}}{% endfor %}

-include $(DEPS)
