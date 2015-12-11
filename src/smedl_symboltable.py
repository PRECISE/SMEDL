#!/usr/bin/env python
# -*- coding: utf-8 -*-


class SmedlSymbolTable(dict):

    generated = 0

    def __init__(self):
        super(SmedlSymbolTable, self).__init__()

    def add(self, symbol, attributes=None):
        if not isinstance(symbol, str):
            raise TypeError
        elif attributes is None:
            self[symbol] = {}
        elif not isinstance(attributes, dict):
            raise TypeError
        else:
            self[symbol] = attributes

    def get(self, symbol, attribute=None):
        if not isinstance(symbol, str):
            raise TypeError
        elif attribute is None:
            return super(SmedlSymbolTable, self).get(symbol)
        elif not isinstance(attribute, str):
            raise TypeError
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
        self[symbol][attribute] = value

    def delete(self, symbol, attribute=None):
        if attribute is None:
            self[symbol] = None
        else:
            self[symbol][attribute] = None

    # This method makes an implicit state, ensuring that its name is unique
    def generateSymbol(self, attributes=None):
        symbol = "Gen%d" % SmedlSymbolTable.generated
        self.add(symbol, attributes)
        SmedlSymbolTable.generated += 1
        return symbol
