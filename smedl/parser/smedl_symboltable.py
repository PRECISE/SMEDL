#!/usr/bin/env python
# -*- coding: utf-8 -*-

#-------------------------------------------------------------------------------
#
# smedl_symboltable.py
#
# Peter Gebhard (pgeb@seas.upenn.edu)
#
# A custom symbol table class for the SMEDL code generator
#
#-------------------------------------------------------------------------------

from collections import OrderedDict

class SmedlSymbolTable(OrderedDict):

    generated = 0

    def __init__(self):
        super(SmedlSymbolTable, self).__init__()


    def add(self, symbol, attributes=None):
        if not isinstance(symbol, str):
            raise TypeError('Symbol must be a string')
        elif attributes is not None and not isinstance(attributes, dict):
            raise TypeError('Attributes must be a dictionary')
        elif symbol in self.keys():
            if self[symbol] == attributes:
                return
            else:
                raise ValueError('Symbol %s already exists in the table. Maybe you have a name conflict? Or you can use the update() method instead.' % symbol)
        elif attributes is None:
            self[symbol] = {}
        else:
            self[symbol] = attributes


    def get(self, symbol, attribute=None):
        if not isinstance(symbol, str):
            raise TypeError('Symbol must be a string')
        elif attribute is None:
            return super(SmedlSymbolTable, self).get(symbol)
        elif not isinstance(attribute, str):
            raise TypeError('Attribute must be a string')
        else:
            return super(SmedlSymbolTable, self).get(symbol).get(attribute)


    def getSymbolsByType(self, type):
        out = []
        for s in list(self.keys()):
            if 'type' in self[s] and self[s]['type'] == type:
                out.append(s)
        return out


    def getEvents(self):
        return self.getSymbolsByType('imported_events') + \
            self.getSymbolsByType('internal_events') + \
            self.getSymbolsByType('exported_events')


    def update(self, symbol, attribute, value):
        if not isinstance(symbol, str):
            raise TypeError('Symbol must be a string')
        elif not isinstance(attribute, str):
            raise TypeError('Attribute must be a string')
        self[symbol][attribute] = value


    def delete(self, symbol, attribute=None):
        if attribute is None:
            self[symbol] = None
        else:
            self[symbol][attribute] = None


    def generateSymbol(self, attributes=None):
        """
        This method generates a new symbol representing an implicit state,
        ensuring that its name is unique.
        """
        symbol = "Gen%d" % SmedlSymbolTable.generated
        self.add(symbol, attributes)
        SmedlSymbolTable.generated += 1
        return symbol
