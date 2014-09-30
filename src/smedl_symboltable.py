#!/usr/bin/env python
# -*- coding: utf-8 -*-

class smedlSymbolTable(dict):

    def __init__(self):
        super(smedlSymbolTable, self).__init__()

    def add(self, symbol, attributes=None):
        if attributes is None:
            self[symbol] = {}
        else:
            self[symbol] = attributes

    def get(self, symbol, attribute=None):
        if attribute is None:
            return self[symbol]
        else:
            return self[symbol][attribute]

    def getSymbolsByType(self, type):
        out = []
        for s in self.keys():
            if 'type' in self[s] and self[s]['type'] == type :
                out.append(s)
        return out

    def update(self, symbol, attribute, value):
        self[symbol][attribute] = value

    def delete(self, symbol, attribute=None):
        if attribute is None:
            self[symbol] = None
        else:
            self[symbol][attribute] = None
