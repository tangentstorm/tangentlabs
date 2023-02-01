Red [ "timeline ui mockup for 1010data w/ api2 client" ]

api2: https://mwallace.dev.edge.1010data.com/mjw/api
if unset? :api2-cookie [api2-cookie: ""]

jp: function ["json post" url [url!] data ][
  headers: copy [content-type: "application/json"]
  if api2-cookie <> "" [append headers compose [cookie: (api2-cookie)]]
  write/info url compose/deep [post [(headers)] (to-json to-map data)]]

xp: function ["xml post" url [url!] q [block!] ][
  write/info url compose/deep [post [
    content-type: "application/xml"
    cookie: (api2-cookie)]
    (to-xml q)]]

login-form: layout compose [
  image https://www.1010data.com/wp-content/uploads/2022/08/1010data_Logo-1.png return
  text "url:"  api-field: field (to-string api2) return
  text "uid: " uid-field: field "michal" return
  text "pw:  " pw-field: field password return
  button "submit" [
    print "attempting login..."
    probe res: jp api2/!login compose [uid: (uid-field/text) pw: (pw-field/text)]
    api2-cookie: res/2/Set-Cookie/1
    unview]]

login: does [view/options login-form [text: "1010data"]]
if api2-cookie = "" [login]

; -- ren -> xml ------------------------------------------

q: [
  [base table: "default.test.solar"]
;  [link table2: "*" [{<!-- Have to fall back to strings for tag bodies... :/ -->}]]
  [sort col: "dist"]
  [sel value: "orbits='Sun'"]
  [colord cols: "name,rkm,dist"]
]

xml-attrs: function [elem [block!]] [
  collect compose [ o: next head elem
      while [set-word? o/1] [keep rejoin [" " o/1 "=" mold to-string o/2]
      o: next next o] ]]

xml-tail: function [el [block!]] [
    end: last el
    either (block! = type? end)
      [rejoin [">" end/1 "</" el/1 ">^/"]]  ; TODO: (to-xml end)
      ["/>^/"]]

to-xml: function [ops [block!]] [
  rejoin collect [foreach op ops [
    keep rejoin ["<" (op/1) (xml-attrs op) (xml-tail op)]]]]


xp-xml: []
xp-res: [none none none]
refresh-v-tbl: does [
    xp-xml: take/part copy q v-tag/selected
    xp-res: xp api2/run?_fmt=text xp-xml
    v-tbl/text: xp-res/3]
tags: compose [collect [foreach op q [keep to-string op/1]]]
win: view/no-wait compose [
  below
  v-tag: text-list 320x220 data (tags) [refresh-v-tbl]
  v-ops: area 320x240 react [
    face/text: to-xml take/part copy q v-tag/selected ]
  return
  v-tbl: area 640x480 "..." font [name: "consolas" size: 10]
  do [self/text: "TRS.red"
      v-tag/selected: length? q
      refresh-v-tbl ]]

'ok
