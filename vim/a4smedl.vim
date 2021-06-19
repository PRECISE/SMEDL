" Vim syntax file
" Language: A4SMEDL

" Remove any old syntax stuff hanging around
if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syntax iskeyword @,48-57,192-255,_

syntax match a4smedlImportFile  /\v"[^"\n\r]*"/ contained
highlight default link a4smedlImportFile String

syntax match a4smedlMonitor     "\v<[a-zA-Z][0-9a-zA-Z_]*>" contained
syntax match a4smedlSyncset     "\v<[a-zA-Z][0-9a-zA-Z_]*>" contained
highlight default link a4smedlMonitor   Function
highlight default link a4smedlSyncset   Identifier

syntax match a4smedlLabel       "\v<[a-zA-Z][0-9a-zA-Z_]*[ \t\r\n]*:"
syntax match a4smedlConnector   "\v\=\>"
syntax match a4smedlParam       "\v\$[ \t\r\n]*\d+>"
syntax match a4smedlParam       "\v\#[ \t\r\n]*\d+>"
syntax match a4smedlParam       "\vId[ \t\r\n]*\.[ \t\r\n]*\d+>"
syntax match a4smedlParam       "\vParam[ \t\r\n]*\.[ \t\r\n]*\d+>"
highlight default link a4smedlLabel     Identifier
highlight default link a4smedlConnector Delimiter
highlight default link a4smedlParam     Constant

syntax keyword a4smedlTodo      TODO XXX FIXME NOTE contained
syntax match a4smedlComment     "\v\/\/.*$" contains=smedlTodo
syntax match a4smedlComment     "\v\/\*\_.{-}\*\/" contains=smedlTodo
highlight default link a4smedlTodo      Todo
highlight default link a4smedlComment   Comment

syntax keyword a4smedlKeyword   import nextgroup=a4smedlImportFile skipwhite skipempty
syntax keyword a4smedlKeyword   monitor as nextgroup=a4smedlMonitor skipwhite skipempty
syntax keyword a4smedlKeyword   syncset nextgroup=a4smedlSyncset skipwhite skipempty
syntax keyword a4smedlKeyword   system pedl imported exported
syntax keyword a4smedlType      int float double char string pointer opaque
highlight default link a4smedlType      Type
highlight default link a4smedlKeyword   Keyword

let b:current_syntax = "a4smedl"
