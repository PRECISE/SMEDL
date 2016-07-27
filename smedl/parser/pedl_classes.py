#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals

from grako.model import Node
from grako.model import ModelBuilderSemantics


__version__ = '2016.07.27.16'


class pedlModelBuilderSemantics(ModelBuilderSemantics):
    def __init__(self):
        types = [
            t for t in globals().values()
            if type(t) is type and issubclass(t, ModelBase)
        ]
        super(pedlModelBuilderSemantics, self).__init__(types=types)


class ModelBase(Node):
    pass


class Object(ModelBase):
    def __init__(self, *args,
                 object=None,
                 monitors=None,
                 event_defs=None,
                 **kwargs):
        super(Object, self).__init__(
            *args,
            object=object,
            monitors=monitors,
            event_defs=event_defs,
            **kwargs
        )

    def getTargetMonitorPoints(self):
        return ','.join([e.getMonitorPoint() for e in self.event_defs])


class MonitorConstructor(ModelBase):
    def __init__(self, *args,
                 monitor=None,
                 monitor_params=None,
                 struct=None,
                 **kwargs):
        super(MonitorConstructor, self).__init__(
            *args,
            monitor=monitor,
            monitor_params=monitor_params,
            struct=struct,
            **kwargs
        )


class MonitorStruct(ModelBase):
    def __init__(self, *args,
                 struct_id=None,
                 fields=None,
                 **kwargs):
        super(MonitorStruct, self).__init__(
            *args,
            struct_id=struct_id,
            fields=fields,
            **kwargs
        )


class Field(ModelBase):
    def __init__(self, *args,
                 variable=None,
                 value=None,
                 **kwargs):
        super(Field, self).__init__(
            *args,
            variable=variable,
            value=value,
            **kwargs
        )


class Event(ModelBase):
    def __init__(self, *args,
                 monitor=None,
                 monitor_params=None,
                 event=None,
                 event_params=None,
                 update_param=None,
                 call_param=None,
                 when=None,
                 **kwargs):
        super(Event, self).__init__(
            *args,
            monitor=monitor,
            monitor_params=monitor_params,
            event=event,
            event_params=event_params,
            update_param=update_param,
            call_param=call_param,
            when=when,
            **kwargs
        )

    def getMonitorPoint(self):
        if self.update_param:
            return str(self.update_param)
        else:
            return self.call_param


class UpdateParam(ModelBase):
    def __init__(self, *args,
                 update_fn=None,
                 update_var=None,
                 **kwargs):
        super(UpdateParam, self).__init__(
            *args,
            update_fn=update_fn,
            update_var=update_var,
            **kwargs
        )

    def __str__(self):
        if self.update_fn:
            return self.update_fn + '.' + self.update_var
        else:
            return self.update_var

class StateUpdate(ModelBase):
    def __init__(self, *args,
                 target=None,
                 expression=None,
                 **kwargs):
        super(StateUpdate, self).__init__(
            *args,
            target=target,
            expression=expression,
            **kwargs
        )
