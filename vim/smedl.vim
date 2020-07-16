" Vim syntax file
" Language: SMEDL

" Remove any old syntax stuff hanging around
if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syntax iskeyword @,48-57,192-255,-,+,.,_

syntax match smedlInt       "\v\<[-+]?\d+\>" contained
syntax match smedlFloat     "\v\<\d+[Ee][-+]?\d+\>" contained
syntax match smedlFloat     "\v\<\d+\.([Ee][-+]?\d+)?\>" contained
syntax match smedlFloat     "\v\<\d*\.\d+([Ee][-+]?\d+)?\>" contained
highlight link smedlInt     Number
highlight link smedlFloat   Number

syntax match smedlEscape    /\v\\\o{1,3}/ contained
syntax match smedlEscape    /\v\\x\x{2}/ contained
syntax match smedlEscape    /\v\\u\x{4}/ contained
syntax match smedlEscape    /\v\\U\x{8}/ contained
syntax match smedlEscape    /\v\\['"?\\abfnrtv]/ contained
syntax region smedlChar     start=/\v'/ skip=/\v\\./ end=/\v"/ oneline contains=smedlEscape
syntax region smedlString   start=/\v"/ skip=/\v\\./ end=/\v"/ oneline contains=smedlEscape
highlight link smedlEscape  Special
highlight link smedlChar    Character
highlight link smedlString  String

syntax keyword smedlTodo    TODO XXX FIXME NOTE contained
syntax match smedlComment   "\v\/\/.*$" contains=smedlTodo
syntax match smedlComment   "\v\/\*\_.{-}\*\/" contains=smedlTodo
highlight link smedlTodo    Todo
highlight link smedlComment Comment

syntax match smedlEventDef  "\v\<[0-9a-zA-Z_]+\>" contained nextgroup=smedlTypeList skipwhite skipempty
highlight link smedlEventDef Function

syntax region smedlScenario matchgroup=smedlLabel start="\v\<[0-9a-zA-Z_]+[ \t\r\n]*:"ms=e end="\v\<[0-9a-zA-Z_]+[ \t\r\n]*:"me=s,he=s contains=smedlScenarioKeyword,smedlInt,smedlFloat,smedlChar,smedlString,smedlConstant,smedlComment contained keepend fold
highlight link smedlLabel Identifier

syntax match smedlInclude   "\v#include"
syntax keyword smedlEvType  imported internal exported contained nextgroup=smedlEventDef skipwhite skipempty
syntax keyword smedlType    int float double char string pointer thread opaque
syntax keyword smedlKeyword object
syntax keyword smedlScenarioKeyword when else raise contained
syntax keyword smedlConstant true false null NULL contained
highlight link smedlInclude Include
highlight link smedlEvType Type
highlight link smedlType Type
highlight link smedlKeyword Keyword
highlight link smedlConstant Boolean

syntax region smedlTypeList start='(' end=')' contains=smedlType,smedlComment contained

syntax region smedlStates   matchgroup=smedlSection start="\v\<state:"ms=e end="\vevents:"me=s,he=s contains=smedlType,smedlInt,smedlFloat,smedlChar,smedlString,smedlConstant,smedlComment fold keepend

syntax region smedlEvents   matchgroup=smedlSection start="\v\<events:"ms=e end="\vscenarios:"me=s,he=s contains=smedlEvType,smedlComment fold keepend

syntax region smedlScenarios matchgroup=smedlSection start="\v\<scenarios:"ms=e end="\v\%$" contains=smedlScenario,smedlComment fold keepend

highlight link smedlSection Label

let b:current_syntax = "smedl"
