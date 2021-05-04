# Uncomment to customize these variables
#CC=cc
#CXX=g++
#CPPFLAGS:=$(CPPFLAGS)
#CFLAGS:=$(CFLAGS)
#LDFLAGS:=$(LDFLAGS)
#LDLIBS:=$(LDLIBS)
#RM=rm -f

# Extra C/C++ source code files to be linked in with the monitors (must be .c,
# .cc, .cpp, or .C files)
{% if transport == 'file' %}
EXTRA_SOURCES=
{% else %}
{% for spec in spec_names %}
EXTRA_SOURCES_{{spec}}=
{% endfor %}
{% endif %}

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
{%- if transport == 'file' %}
 file.c json.c
{% elif transport == 'rabbitmq' %}
 cJSON.c
{% endif %}
{% for syncset in syncsets %}
SOURCES_{{syncset}}=
{%- for spec in syncset_specs[syncset] %}{% if not loop.first %} {%+ endif %}{{spec}}_mon.c{% endfor %}
{%- for mon in syncset_mons[syncset] %} {{mon}}_local_wrapper.c{% endfor %}
 {{syncset}}_global_wrapper.c
{%- if transport == 'rabbitmq' %} {{syncset}}_rabbitmq.c{% endif %}

{% endfor %}
SMEDL_SOURCES=$(COMMON_SOURCES){% if transport == 'file' %} {{system}}_file.c{% endif %}
{%- for syncset in syncsets %} $(SOURCES_{{syncset}}){% endfor %}


SMEDL_OBJS=$(SMEDL_SOURCES:.c=.o)
SMEDL_OBJS:=$(SMEDL_OBJS:%=$(BUILD_DIR)/%)
{% if transport != 'file' %}

{% for syncset in syncsets %}
OBJS_{{syncset}}=$(COMMON_SOURCES) $(EXTRA_SOURCES_{{syncset}}) $(SOURCES_{{syncset}})
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.c=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.cc=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.cpp=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:.C=.o)
OBJS_{{syncset}}:=$(OBJS_{{syncset}}:%=$(BUILD_DIR)/%)
{% endfor %}
{% endif %}

{% if transport != 'file' %}
EXTRA_SOURCES=
{%- for syncset in syncsets %}
{% if not loop.first %} {% endif %}$(EXTRA_SOURCES_{{syncset}})
{% endfor %}
EXTRA_SOURCES:=$(sort $(EXTRA_SOURCES))
{% endif %}
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

{% if transport == 'file' %}
all: $(BUILD_DIR)/{{system}}

$(BUILD_DIR)/{{system}}: $(OBJS)
	mkdir -p $(@D)
	$(CC) $(LDFLAGS) $+ $(LDLIBS) -o $@
{% else %}
all:{% for syncset in syncsets %} $(BUILD_DIR)/{{syncset}}{% endfor %}
{% for syncset in syncsets %}

$(BUILD_DIR)/{{syncset}}: $(OBJS_{{syncset}})
	mkdir -p $(@D)
	$(CC) $(LDFLAGS) $+ $(LDLIBS) -o $@
{% endfor %}
{% endif %}

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
{%- if transport == 'file' %}
 $(BUILD_DIR)/{{system}}
{% else %}
{% for syncset in syncsets %} $(BUILD_DIR)/{{syncset}}{% endfor %}
{% endif %}

-include $(DEPS)
