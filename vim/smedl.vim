" Vim syntax file
" Language: SMEDL

" Remove any old syntax stuff hanging around
if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syntax iskeyword @,48-57,192-255,.,_

syntax match smedlInclFile      /\v".*"/ contained
syntax match smedlInclFile      /\v\<.*\>/ contained
highlight default link smedlInclFile    String

syntax match smedlEventDef      "\v<[a-zA-Z][0-9a-zA-Z_]*>"
syntax keyword smedlEvType      imported internal exported nextgroup=smedlEventDef skipwhite skipempty
highlight default link smedlEventDef    Function
highlight default link smedlEvType      Type

syntax match smedlIdentifier    "\v<[a-zA-Z][0-9a-zA-Z_]*>"

syntax match smedlInt           "\v[-+]?<\d+>"
syntax match smedlFloat         "\v[-+]?<\d+[Ee][-+]?\d+>"
syntax match smedlFloat         "\v[-+]?<\d+\.([Ee][-+]?\d+)?>"
syntax match smedlFloat         "\v[-+]?<\d*\.\d+([Ee][-+]?\d+)?>"
highlight default link smedlInt         Number
highlight default link smedlFloat       Float

syntax match smedlEscape        /\v\\\o{1,3}/ contained
syntax match smedlEscape        /\v\\x\x{2}/ contained
syntax match smedlEscape        /\v\\u\x{4}/ contained
syntax match smedlEscape        /\v\\U\x{8}/ contained
syntax match smedlEscape        /\v\\['"?\\abfnrtv]/ contained
syntax region smedlChar         start=/\v'/ skip=/\v\\./ end=/\v"/ oneline contains=smedlEscape
syntax region smedlString       start=/\v"/ skip=/\v\\./ end=/\v"/ oneline contains=smedlEscape
highlight default link smedlEscape      Special
highlight default link smedlChar        Character
highlight default link smedlString      String

syntax keyword smedlTodo        TODO XXX FIXME NOTE contained
syntax match smedlComment       "\v\/\/.*$" contains=smedlTodo
syntax match smedlComment       "\v\/\*\_.{-}\*\/" contains=smedlTodo
highlight default link smedlTodo        Todo
highlight default link smedlComment     Comment

syntax match smedlLabel         "\v<[a-zA-Z][0-9a-zA-Z_]*[ \t\r\n]*:"
"syntax region smedlScenario matchgroup=smedlLabel start="\v<[0-9a-zA-Z_]+[ \t\r\n]*:"ms=e end="\v<[0-9a-zA-Z_]+[ \t\r\n]*:"me=s,he=s contains=ALL keepend fold
highlight default link smedlLabel       Identifier

syntax match smedlTransition    "\v-\>"
syntax match smedlState         "\v<[a-zA-Z][0-9a-zA-Z_]*[ \t\r\n]*-\>"me=e-2,he=e-2
syntax match smedlState         "\v-\>[ \t\r\n]*[a-zA-Z][0-9a-zA-Z_]*[ \t\r\n]*;"hs=s+2,me=e-1,he=e-1 contains=smedlTransition
highlight default link smedlTransition  Delimiter
highlight default link smedlState       Identifier

syntax match smedlInclude       "\v#include" nextgroup=smedlInclFile skipwhite skipempty
syntax keyword smedlType        int float double char string pointer thread opaque
syntax keyword smedlKeyword     object when else raise
syntax keyword smedlConstant    true false null NULL
highlight default link smedlInclude     Include
highlight default link smedlType        Type
highlight default link smedlKeyword     Keyword
highlight default link smedlConstant    Boolean

syntax match smedlSection       "\v<state:"
"syntax region smedlStates   matchgroup=smedlSection start="\v<state:"ms=e end="\v<events:"me=s,he=s contains=ALL fold keepend
syntax match smedlSection       "\v<events:"
"syntax region smedlEvents   matchgroup=smedlSection start="\v<events:"ms=e end="\v<scenarios:"me=s,he=s contains=ALL fold keepend
syntax match smedlSection       "\v<scenarios:"
"syntax region smedlScenarios matchgroup=smedlSection start="\v<scenarios:"ms=e end="\v\%$" contains=ALL fold keepend
highlight default link smedlSection     Label

let b:current_syntax = "smedl"
