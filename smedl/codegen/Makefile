CC=cc
CPPFLAGS=
CFLAGS=
LDFLAGS=
LDLIBS=

# Uncomment the first for a debug build. Uncomment the second for a release
# (optimized) build.
CFLAGS:=-g -DDEBUG $(CFLAGS)
#CFLAGS:=-O2 $(CFLAGS)

# Changes below this line not recommended
###############################################################################

#CPPFLAGS:=-D_XOPEN_SOURCE=500 $(CPPFLAGS)
CFLAGS:=-std=c99 $(CFLAGS)
{% if transport == 'rabbitmq' %}
LDLIBS:=$(LDLIBS) -lrabbitmq
{% endif %}
COMMONOBJS=smedl_types.o event_queue.o monitor_map.o global_event_queue.o
{%- if transport == 'file' %}
 file.o json.o
{% elif transport == 'rabbitmq' %}
 cJSON.o
{% endif %}
SOURCES:=smedl_types.c event_queue.c monitor_map.c global_event_queue.c
{%- for spec in spec_names %} {{spec}}_mon.c{% endfor %}
{%- for mon in mon_names %} {{mon}}_local_wrapper.c{% endfor %}
{%- for syncset in syncsets %} {{syncset}}_global_wrapper.c{% endfor %}
{%- if transport == 'file' %} file.c json.c {{system}}_file.c
{% elif transport == 'rabbitmq' %} cJSON.c
{%- for syncset in syncsets %} {{syncset}}_rabbitmq.c{% endfor %}
{% endif %}

{% if transport == 'file' %}
all: {{system}}
{% elif transport == 'rabbitmq' %}
all:{% for syncset in syncsets %} {{syncset}}{% endfor %}
{% endif %}

.PHONY: all clean

clean:
	rm -f *.d *.d.* *.o
{%- if transport == 'file' %}
{{system}}

{{system}}: $(SOURCES:.c=.o)
	$(CC) $(CFLAGS) $(LDFLAGS) $+ $(LDLIBS) -o $@
{% elif transport == 'rabbitmq' %}
{% for syncset in syncsets %} {{syncset}}{% endfor %}
{% for syncset in syncsets %}

{{syncset}}: $(COMMONOBJS)
{%- for spec in syncset_specs[syncset] %} {{spec}}_mon.o
{%- endfor %}
{%- for mon in syncset_mons[syncset] %} {{mon}}_local_wrapper.o
{%- endfor %} {{syncset}}_global_wrapper.o {{syncset}}_rabbitmq.o
	$(CC) $(CFLAGS) $(LDFLAGS) $+ $(LDLIBS) -o $@
{% endfor %}
{% endif %}

%.d: %.c
        @set -e; rm -f $@; \
        $(CC) -M $(CPPFLAGS) $< > $@.$$$$; \
        sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
        rm -f $@.$$$$

$(info ** Note: Messages saying "*.d: No such file or directory" are okay. The files will)
$(info **       be automatically generated.)
include $(SOURCES:.c=.d)
