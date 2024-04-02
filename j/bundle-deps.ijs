NB. program to find all dependent j files
NB. and merge them into one big .ijs file
NB.
NB. (the goal was to bundle jprez for running
NB. with WASM, but the resulting file caused
NB. out of memory errors in the wasm runtime,
NB. and I didnt pursue it any further.)

deps =: ''
src =: ''

NB. find 'odd' lines that reference load/require but not
NB. at the start of the line
odd =: ,:'source';'line';'text'

find_deps =: {{
  lines =. LF cut freads y
  loads =. I. {{*#I. +/('load';'require')E.S:0 y}} S:0 lines
  for_line. loads{lines do.
    toks =. ;: > line
    if. ({.toks) e. 'load';'require' do.
      find_deps each getscripts_j_ }.}:>1{toks
    else. odd=:~.odd,(y;line_index;line) end.
  end.
  src =: src,<'NB. ',60#'-'
  src =: src,<'NB. ', y
  src =: src,<'cocurrent''base'''
  src =: src,<'NB. ',60#'-'
  src =: src,(loads-.~i.#lines){lines
  deps =: ~.(<y),deps }}

find_deps'jprez.ijs'
echo '## dependencies:'
echo >deps
echo '## odd lines:'
echo odd

(LF joinstring src) fwrites 'all.ijs'
