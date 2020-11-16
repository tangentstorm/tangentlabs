NB. 
NB. jGSL: GameSketchLib for J
NB.
NB. ======================================================================
coclass 'GsMouse'

xy =: start_xy =: adj_xy =: off_xy =: 0 0
dragging =: 0
subjects =: 0$a:
observers =: 0$a:



coclass 'GsProto'
NB. ----------------------------------------------------------------------
mouse =: conew 'GsMouse'

coclass 'IGsGridMember'
NB. ----------------------------------------------------------------------
gxy =: _1 _1


coclass 'IGsBox'  NB. was GsSpatial
NB. ----------------------------------------------------------------------

xy =: wh =: 0 0

x0  =: verb : '{. xy'
y0  =: verb : '{: xy'
xy0 =: verb : 'xy'
xy1 =: verb : 'xy + wh'

contains =: [: *./^:2 (>: xy0) , (<: xy1) 

overlaps =: verb define
  NB. does this box overlap box y?
  *./ (xy < xy1__y'') *. (xy+wh) > xy__y
)

covers =: verb define
  NB. does this box completely cover/surround box y?
  *./ (xy <: xy__y) *. (xy+wh) > xy1__y''
)


coclass 'IGsInteractive'
NB. ----------------------------------------------------------------------

click =: [
drag  =: verb define
  xy =: adjusted_xy__mouse
)
mouseAt =: [


NB. skipped GsIterable... !! Do I need this?




coclass 'GsBasic'
NB. ----------------------------------------------------------------------

coinsert each 'IGsGridMember';'IGsBox';'IGsInteractive'
isNull =: 0:

NB. defaults
visible =: 1
active  =: 1
exists  =: 1
alive   =: 1

update =: [
render =: [



coclass ''
NB. ----------------------------------------------------------------------




NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
NB. ----------------------------------------------------------------------
