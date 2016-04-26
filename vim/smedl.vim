" Vim syntax file for SMEDL

" Remove any old syntax stuff hanging around
if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syn match   smedlNumber      "\<[0-9]\+\>"
syn match   smedlFloat       "\<[0-9]\+\.[0-9]\+\([eE][-+]\=[0-9]\+\)\=\>"
syn keyword smedlConstant    Error
syn keyword smedlBoolean     true false

syn keyword smedlSection     state events scenarios
syn keyword smedlKeywords    object imported exported when else raise
syn keyword smedlTypes       int float

syn match   smedlScenario    "^\s*\w\+\(:\s*\)\@="
syn match   smedlSrcState    "^\s*\w\+\(\s*->\)\@="
syn match   smedlDestState   "\(->\s*\)\@<=\w\+\s*$"

hi def link smedlNumber              Number
hi def link smedlFloat               Float
hi def link smedlConstant            Constant
hi def link smedlBoolean             Boolean

hi def link smedlSection             Keyword
hi def link smedlKeywords            Keyword
hi def link smedlTypes               Type

hi def link smedlSrcState            Identifier
hi def link smedlDestState           Identifier
hi def link smedlScenario            Function

let b:current_syntax = "smedl"

