from pygments.lexer import RegexLexer, include, bygroups, words
from pygments.token import *

class SmedlLexer(RegexLexer):
    name = 'Smedl'
    aliases = ['smedl', 'SMEDL']
    filenames = ['*.smedl']

    tokens = {
        'root': [
            (r'\s+', Whitespace),
            (r'/\*.*?\*/', Comment.Multiline),
            (r'//.*?\n', Comment.Single),
            (words(('object',
                    'imported',
                    'exported',
                    'internal',
                    'finalstate'), suffix=r'\b'), Keyword.Declaration),
            (r'#include\b', Comment.Preproc),
            (words(('state:',
                    'events:',
                    'scenarios:'), suffix=r'\b'), Keyword),
            (words(('int',
                    'float',
                    'double',
                    'char',
                    'string',
                    'pointer',
                    'opaque'), suffix=r'\b'), Keyword.Type),
            (words(('when',
                    'else',
                    'raise'), suffix=r'\b'), Keyword),
            (words(('true',
                    'false',
                    'null',
                    'NULL'), suffix=r'\b'), Keyword.Constant),
            (r'[a-zA-Z][A-Za-z0-9_]*\s*:', Name.Label),
            (r'([a-zA-Z][A-Za-z0-9_]*)(\s*)(\()',
             bygroups(Name.Function, Whitespace, Punctuation)),
            (r'<[a-zA-Z][A-Za-z0-9_]*>:', Name.Entity),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name),
            (r'[-+]?[0-9]+', Number.Integer),
            (r'[-+]?[0-9]*\.[0-9]+(?:[Ee][+-]?[0-9]+)?|[0-9]+\.(?:[Ee][+-]?[0-9]+)?|[0-9]+[Ee][+-]?[0-9]+', Number.Float),
            (r"""'(?:[^'\\\n]|\\[0-7]{1,3}|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\U[0-9a-fA-F]{8}|\\['"?\\abfnrtv])'""", String.Char),
            (r'"[^"\\\n]*(?:\\.[^"\\\n]*)*"', String),
            (r'<.*?[>\n\r\v\f]', String),
            (r'[-+~!*/%<>=&|^]', Operator),
            (r'[(){},;]', Punctuation),
            (r'[][]', Text),
        ],
    }

class SmedlLexer2(RegexLexer):
    name = 'Smedl'
    aliases = ['smedl', 'SMEDL']
    filenames = ['*.smedl']

    tokens = {
        'whitespace': [
            (r'\s+', Whitespace),
            (r'/\*.*?\*/', Comment.Multiline),
            (r'//.*?\n', Comment.Single),
        ],
        'literal': [
            (r'true\b', Keyword.Constant),
            (r'false\b', Keyword.Constant),
            (r'null\b', Keyword.Constant),
            (r'NULL\b', Keyword.Constant),
            (r'[0-9]+', Number.Integer),
            (r'[0-9]*\.[0-9]+(?:[Ee][+-]?[0-9]+)?|[0-9]+\.(?:[Ee][+-]?[0-9]+)?|[0-9]+[Ee][+-]?[0-9]+', Number.Float),
            (r"""'(?:[^'\\\n]|\\[0-7]{1,3}|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\U[0-9a-fA-F]{8}|\\['"?\\abfnrtv])'""", String.Char),
            (r'"[^"\\\n]*(?:\\.[^"\\\n]*)*"', String),
        ],
        'signed_literal': [
            include('literal'),
            (r'[-+][0-9]+', Number.Integer),
            (r'[-+][0-9]*\.[0-9]+(?:[Ee][+-]?[0-9]+)?|[0-9]+\.(?:[Ee][+-]?[0-9]+)?|[0-9]+[Ee][+-]?[0-9]+', Number.Float),
        ],
        'root': [
            include('whitespace'),
            (r'object\b', Keyword.Declaration, 'object'),
            (r'#include\b', Comment.Preproc, 'include'),
            (r'state:', Keyword.Label, 'state'),
            (r'events:', Keyword.Label, 'events'),
        ],
        'object': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Class, 'semicolon'),
        ],
        'include': [
            include('whitespace'),
            (r'".*?["\n\r\v\f]', String.Other, '#pop'),
            (r'<.*?[>\n\r\v\f]', String.Other, '#pop'),
        ],
        'state': [
            include('whitespace'),
            (words(('int',
                    'float',
                    'double',
                    'char',
                    'string',
                    'pointer',
                    'opaque'), suffix=r'\b'), Keyword.Type, 'state_var'),
            (r'events:', Keyword.Label, 'events'),
        ],
        'state_var': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Variable),
            (r'=', Operator),
            include('signed_literal'),
            (r';', Punctuation, '#pop'),
        ],
        'events': [
            include('whitespace'),
            (words(('imported', 'internal', 'exported'),
                   suffix=r'\b'), Keyword.Declaration, 'event_decl1'),
            (r'scenarios:', Keyword.Label, 'scenarios'),
        ],
        'event_decl1': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Function, 'event_decl2'),
            (r';', Error, '#pop:1'),
        ],
        'event_decl2': [
            include('whitespace'),
            (r'\(', Punctuation),
            (words(('int',
                    'float',
                    'double',
                    'char',
                    'string',
                    'pointer',
                    'opaque'), suffix=r'\b'), Keyword.Type),
            (r',', Punctuation),
            (r'\)', Punctuation),
            (r';', Punctuation, '#pop:2'),
        ],
        'scenarios': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*\s*:', Name.Label, 'scenario'),
        ],
        'scenario': [
            include('whitespace'),
            (r'finalstate\b', Keyword.Declaration, 'finalstate'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, 'transition'),
        ],
        'finalstate': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, 'semicolon'),
        ],
        'transition': [
            include('whitespace'),
            (r'->', Operator),
            (r'else\b', Keyword),
            (r'when\b', Keyword),
            (r'([a-zA-Z][A-Za-z0-9_]*)(\s*)(\()',
             bygroups(Name.Function, Whitespace, Punctuation), 'parens'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name),
            (r'\(', Punctuation, 'parens'),
            (r'\{', Punctuation, 'actions'),
            (r';', Punctuation, '#pop'),
        ],
        'expr_or_statement': [
            (r'raise\b', Keyword, 'raise'),
            include('literal'),
            (r'[-+~!*/%<>=|^]', Operator),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Variable),
            (r'\(', Punctuation, 'parens'),
        ],
        'raise': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Function, '#pop'),
        ],
        'parens': [
            include('whitespace'),
            include('expr_or_statement'),
            (r',', Punctuation),
            (r'\)', Punctuation, '#pop'),
        ],
        'actions': [
            include('whitespace'),
            include('expr_or_statement'),
            (r';', Punctuation),
            (r'\}', Punctuation, '#pop'),
        ],
        'semicolon': [
            include('whitespace'),
            (r';', Punctuation, '#pop:2'),
        ],
    }


class A4smedlLexer(RegexLexer):
    name = 'A4smedl'
    aliases = ['a4smedl', 'A4SMEDL']
    filenames = ['*.a4smedl']

    tokens = {
        'whitespace': [
            (r'\s+', Whitespace),
            (r'/\*.*?\*/', Comment.Multiline),
            (r'//.*?\n', Comment.Single),
        ],
        'root': [
            include('whitespace'),
            (r'system\b', Keyword.Declaration, 'system'),
            (r'import\b', Keyword.Declaration, 'import'),
            (r'monitor\b', Keyword.Declaration, 'monitor'),
            (r'imported\b', Keyword.Declaration, 'event'),
            (r'exported\b', Keyword.Declaration, 'event'),
            (r'syncset\b', Keyword.Declaration, 'syncset'),
            (r'[a-zA-Z][A-Za-z0-9_]*\s*:', Name.Label, 'connection'),
            (r'(pedl)(\s*)(\.)',
             (Name.Builtin, Whitespace, Punctuation), 'connection1'),
            (r'([a-zA-Z][A-Za-z0-9_]*)(\s*)(\.)',
             (Name, Whitespace, Punctuation), 'connection1'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, 'connection2'),
        ],
        'system': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Class, 'semicolon'),
        ],
        'import': [
            include('whitespace'),
            (r'"[^"\n\r\v\f]*"', String.Other, 'semicolon'),
        ],
        'monitor': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Class, ('#pop', 'monitor1')),
        ],
        'monitor1': [
            include('whitespace'),
            (r'\(', Punctuation, ('#pop', 'monitor2')),
        ],
        'monitor2': [
            include('whitespace'),
            (words(('int',
                    'float',
                    'double',
                    'char',
                    'string',
                    'pointer',
                    'opaque'), suffix=r'\b'), Keyword.Type),
            (r',', Punctuation),
            (r'\)', Punctuation, ('#pop', 'monitor3')),
        ],
        'monitor3': [
            include('whitespace'),
            (r'as\b', Keyword.Declaration, ('#pop', 'monitor4')),
            (r';', Punctuation, '#pop'),
        ],
        'monitor4': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Class, 'semicolon'),
        ],
        'event': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Function, ('#pop', 'event1')),
        ],
        'event1': [
            include('whitespace'),
            (r'\(', Punctuation, ('#pop', 'event2')),
        ],
        'event2': [
            include('whitespace'),
            (words(('int',
                    'float',
                    'double',
                    'char',
                    'string',
                    'pointer',
                    'opaque'), suffix=r'\b'), Keyword.Type),
            (r',', Punctuation),
            (r'\)', Punctuation, 'semicolon'),
        ],
        'syncset': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Class, ('#pop', 'syncset1')),
        ],
        'syncset1': [
            include('whitespace'),
            (r'\{', Punctuation, ('#pop', 'syncset2')),
        ],
        'syncset2': [
            include('whitespace'),
            (r'imported\b', Keyword.Declaration, 'syncset3'),
            (r'exported\b', Keyword.Declaration, 'syncset3'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Class),
            (r',', Punctuation),
            (r'\}', Punctuation, 'semicolon'),
        ],
        'syncset3': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name.Function, '#pop'),
        ],
        'connection': [
            include('whitespace'),
            (r'(pedl)(\s*)(\.)',
             (Name.Builtin, Whitespace, Punctuation), ('#pop', 'connection1')),
            (r'([a-zA-Z][A-Za-z0-9_]*)(\s*)(\.)',
             (Name, Whitespace, Punctuation), ('#pop', 'connection1')),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, ('#pop', 'connection2')),
        ],
        'connection1': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, ('#pop', 'connection2')),
        ],
        'connection2': [
            include('whitespace'),
            (r'=>', Operator, ('#pop', 'connection3')),
        ],
        'connection3': [
            include('whitespace'),
            (r'(pedl)(\s*)(\.)',
             (Name.Builtin, Whitespace, Punctuation), ('#pop', 'connection7')),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, ('#pop', 'connection4')),
        ],
        'connection4': [
            include('whitespace'),
            (r';', Punctuation, '#pop'),
            (r'\[', Punctuation, ('#pop', 'connection5')),
            (r'\.', Punctuation, ('#pop', 'connection7')),
            (r'\(', Punctuation, ('#pop', 'connection9')),
        ],
        'params': [
            include('whitespace'),
            (r'Id\b', Name.Builtin),
            (r'Param\b', Name.Builtin),
            (r'\.', Punctuation),
            (r'[0-9]+', Number),
            (r'#', Number),
            (r'$', Number),
        ],
        'connection5': [
            include('whitespace'),
            include('params'),
            (r'\]', Punctuation, ('#pop', 'connection6')),
        ],
        'connection6': [
            include('whitespace'),
            (r'\.', Punctuation, ('#pop', 'connection7')),
        ],
        'connection7': [
            include('whitespace'),
            (r'[a-zA-Z][A-Za-z0-9_]*', Name, ('#pop', 'connection8')),
        ],
        'connection8': [
            include('whitespace'),
            (r';', Punctuation, '#pop'),
            (r'\(', Punctuation, ('#pop', 'connection9')),
        ],
        'connection9': [
            include('whitespace'),
            include('params'),
            (r'\)', Punctuation, 'semicolon'),
        ],
        'semicolon': [
            include('whitespace'),
            (r';', Punctuation, '#pop:2'),
        ],
    }
