#ifndef {{sys.name}}_DEFS_H
#define {{sys.name}}_DEFS_H

//TODO Add to generator.py

/* Uniquely identifies any connection in the architecture */
typedef enum {
    {% for channel in sys.imported_connections.keys() %}
    CHANNEL_{{channel}},
    {% endfor %}
    {% for decl in sys.monitor_decls.values() %}
    {% for channel in decl.connections.keys() %}
    CHANNEL_{{channel}},
    {% endfor %}
    {% endfor %}
} {{sys.name}}ChannelID;

#endif /* {{sys.name}}_DEFS_H */
