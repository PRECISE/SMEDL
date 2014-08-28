#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals
from smedl_parser import smedlParser
from grako.ast import AST
import os

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


def main(filename, startrule, trace=False, whitespace=None):
    import json
    with open(filename) as f:
        text = f.read()
    parser = smedlParser(parseinfo=False)
    ast = parser.parse(
        text,
        startrule,
        filename=filename,
        trace=trace,
        whitespace=whitespace)
    print('AST:')
    print(ast)
    print()
    symbolTable = smedlSymbolTable()
    parseToSymbolTable('top', ast, symbolTable)
    print()
    print('Symbol Table:')
    print(symbolTable)
    print()
    outputSource(symbolTable, filename)

def parseToSymbolTable(label, object, symbolTable):
    if isinstance(object, AST):
        print('1')
        for k, v in object.iteritems():
            if isinstance(v, list):
                for vi in v:
                    parseToSymbolTable(k, vi, symbolTable)
            if isinstance(v, AST):
                print('ast: ' + k)
                parseToSymbolTable(k, v, symbolTable)
            else:
                print('2 ' + k)
                if ('_id' in k) and (v not in symbolTable):
                    print('ADD: ' + k + '   ' + v)
                    symbolTable.add(v, {'type' : label})
    if isinstance(object, list):
        print('2')
        for elem in object:
            print('list: ' + label)
            parseToSymbolTable(label, elem, symbolTable)
            
def outputSource(symbolTable, filename):
    out = open(os.path.splitext(filename)[0] + '_generated.c', 'w')
    
    stateset = symbolTable.getSymbolsByType('traces')
    stateset_str = ''
    for s in stateset:
        if s is not stateset[0]:
            stateset_str += ','
        stateset_str += string.upper(s)
    
    out.write('enum { ' + stateset_str + ' } stateset;\n\n')
    out.write('stateset currentState = ' + string.upper(stateset[0]) + ';\n\n')
    
    methods = symbolTable.getSymbolsByType('imported_events')
    for m in methods:
        out.write('void ' + m + '() {\n')
        if len(stateset) > 1:
            out.write('switch (currentState) {\n')
            for s in stateset:
                out.write('case ' + string.upper(s) + ':\n')
                out.write('currentState = ' + string.upper(s) + ';\n')
        else:
            out.write('currentState = ' + string.upper(stateset[0]) + ';\n')
        out.write('}\n\n')
    
    out.close()

if __name__ == '__main__':
    import argparse
    import string
    import sys

    class ListRules(argparse.Action):
        def __call__(self, parser, namespace, values, option_string):
            print('Rules:')
            for r in smedlParser.rule_list():
                print(r)
            print()
            sys.exit(0)

    parser = argparse.ArgumentParser(description="Simple parser for smedl.")
    parser.add_argument('-l', '--list', action=ListRules, nargs=0,
                        help="list all rules and exit")
    parser.add_argument('-t', '--trace', action='store_true',
                        help="output trace information")
    parser.add_argument('-w', '--whitespace', type=str, default=string.whitespace,
                        help="whitespace specification")
    parser.add_argument('file', metavar="FILE", help="the input file to parse")
    parser.add_argument('startrule', metavar="STARTRULE",
                        help="the start rule for parsing")
    args = parser.parse_args()

    main(args.file, args.startrule, trace=args.trace, whitespace=args.whitespace)
