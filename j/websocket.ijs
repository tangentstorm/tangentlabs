NB. minimal example for talking to JQt over a websocket

port =: 3000

wssvr_handler_z_ =: monad define
  NB. global handler for all websocket events
  'e sock' =: y
  if. e = jws_onMessage_jqtide_ do.  wss1_jrx_ on_wsmsg wss0_jrx_
  elseif. e = jws_onOpen_jqtide_ do. on_wsopen''
  else. smoutput y end.
)


ws_send =: monad define
  wd 'ws send',(":sock),' *',":y
)

ws_state =: verb define
  wd 'ws state ',":sock
)

on_wsopen =: verb define
  smoutput ws_state''    NB. echo websocket parameters (uri, port, etc) to console
)

on_wsmsg =: dyad define
  ws_send y              NB. echo request back to the socket
  smoutput y             NB. echo request payload to console
  if. x -: 'text' do.    NB. what to do if x -: 'text'
  else.                  NB. what to do if x -: 'binary'
  end.
)

wd 'ws listen ',":port

NB. example javascript client
js =. noun define
var ws = (function() {
  let ws = new WebSocket("ws://localhost:3000/some-uri/")
  ws.addEventListener('message', x=>console.log(x))
  ws.send('echo?')
  return ws })();
)
