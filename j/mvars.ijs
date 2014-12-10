NB. memory mapped variables
load'jmf'

mdir_z_ =:'~/mvars'
mvar_z_ =: verb define
  NB. usage: (sizes:int+)? mvar names:str → ''
  NB. creates memory mapped variables in the calling locale.
  16 mvar y  NB. reserve 2^16 bytes (64 kib) by default.
:
  path =. jpath mdir,'/',cn=.>coname''
  if. -. fexist path do. fpathcreate path end.
  for_box. ;:y do. fullvar =. ; (var=.>box);'_';cn;'_'
    if. fexist fn=.path,'/',var,'.mvar' do.
    else. createjmf_jmf_ fn ; size=.2^x end.
    map_jmf_ fullvar ; fn
  end.
)
