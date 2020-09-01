{% for param in params %}
{% if param is sameas SmedlType.INT %}
int32 param{{loop.index0}}
{% elif param is sameas SmedlType.FLOAT %}
float64 param{{loop.index0}}
{% elif param is sameas SmedlType.CHAR %}
uint8 param{{loop.index0}}
{% elif param is sameas SmedlType.STRING %}
string param{{loop.index0}}
{% elif param is sameas SmedlType.POINTER %}
string param{{loop.index0}}
{% elif param is sameas SmedlType.THREAD %}
{% unsupported "'thread' type cannot be transported over ROS" %}
{% elif param is sameas SmedlType.OPAQUE %}
uint8[] param{{loop.index0}}
{% endif %}
{% endfor %}
{% for id in ids %}
{% if id is sameas SmedlType.INT %}
int32 id{{loop.index0}}
{% elif id is sameas SmedlType.FLOAT %}
float64 id{{loop.index0}}
{% elif id is sameas SmedlType.CHAR %}
uint8 id{{loop.index0}}
{% elif id is sameas SmedlType.STRING %}
string id{{loop.index0}}
{% elif id is sameas SmedlType.POINTER %}
string id{{loop.index0}}
{% elif id is sameas SmedlType.THREAD %}
{% unsupported "'thread' type cannot be transported over ROS" %}
{% elif id is sameas SmedlType.OPAQUE %}
uint8[] id{{loop.index0}}
{% endif %}
{% endfor %}
