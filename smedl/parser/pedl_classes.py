#!/usr/bin/env python
# -*- coding: utf-8 -*-

# CAVEAT UTILITOR
#
# This file was automatically generated by Grako.
#
#    https://pypi.python.org/pypi/grako/
#
# Any changes you make to it will be overwritten the next time
# the file is generated.

from __future__ import print_function, division, absolute_import, unicode_literals

from grako.model import Node
from grako.model import ModelBuilderSemantics


__version__ = '2016.07.27.14'


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
                 call_param=None,
                 when=None,
                 **kwargs):
        super(Event, self).__init__(
            *args,
            monitor=monitor,
            monitor_params=monitor_params,
            event=event,
            event_params=event_params,
            call_param=call_param,
            when=when,
            **kwargs
        )


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


class Expression(ModelBase):
    def __init__(self, *args,
                 or_ex=None,
                 **kwargs):
        super(Expression, self).__init__(
            *args,
            or_ex=or_ex,
            **kwargs
        )
