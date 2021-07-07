from pygments.lexer import RegexLexer, bygroups, words
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
                    'scenarios:'), suffix=r'\b'), Keyword.Label),
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
            (r'[-+]?(?:[0-9]+|0[Xx][0-9A-Fa-f]+)', Number.Integer),
            (r'[-+]?[0-9]*\.[0-9]+(?:[Ee][+-]?[0-9]+)?|[0-9]+\.(?:[Ee][+-]?[0-9]+)?|[0-9]+[Ee][+-]?[0-9]+|0[Xx][0-9A-Fa-f]*\.[0-9A-Fa-f]+[Pp][+-]?[0-9A-Fa-f]+|0Xx[0-9A-Fa-f]+\.?[Pp][+-]?[0-9A-Fa-f]+', Number.Float),
            (r"""'(?:[^'\\\n]|\\[0-7]{1,3}|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\U[0-9a-fA-F]{8}|\\['"?\\abfnrtv])'""", String.Char),
            (r'"[^"\\\n]*(?:\\.[^"\\\n]*)*"', String),
            (r'<.*?[>\n\r\v\f]', String),
            (r'[-+~!*/%<>=&|^]', Operator),
            (r'[(){},;]', Punctuation),
            (r'[][.]', Text),
        ],
    }


class A4smedlLexer(RegexLexer):
    name = 'A4smedl'
    aliases = ['a4smedl', 'A4SMEDL']
    filenames = ['*.a4smedl']

    tokens = {
        'root': [
            (r'\s+', Whitespace),
            (r'/\*.*?\*/', Comment.Multiline),
            (r'//.*?\n', Comment.Single),
            (words(('system',
                    'import',
                    'monitor',
                    'imported',
                    'exported',
                    'syncset',
                    'as'), suffix=r'\b'), Keyword.Declaration),
            (words(('int',
                    'float',
                    'double',
                    'char',
                    'string',
                    'pointer',
                    'opaque'), suffix=r'\b'), Keyword.Type),
            (r'pedl\b', Name.Builtin),
            (r'(?:Id\.|Param\.|#|\$)[0-9]+', Number),
            (r'\*', Number),
            (r'[a-zA-Z][A-Za-z0-9_]*\s*:', Name.Label),
            (r'[A-Z][A-Za-z0-9_]*', Name.Class),
            (r'[a-z][A-Za-z0-9_]*', Name),
            (r'"[^"\n\r\v\f]*"', String.Other),
            (r'=>', Operator),
            (r'=', Operator),
            (r'[][(){}.,;]', Punctuation),
        ],
    }
