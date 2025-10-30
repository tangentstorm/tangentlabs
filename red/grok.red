Red [ "talk to grok over xai api" ]

xai-key: trim/lines read %.xai-key
xai-url: https://api.x.ai/v1/chat/completions
xai-model: "grok-4-fast-reasoning"

sys-prompt: trim {
You are a highly intelligent question answering bot.
If you don't know the answer to a question, you truthfully say you don't know.}

pj: function [x] [print to-json/pretty to-map x " "]
jp: function ["json post" url [url!] data ][
  write/info url compose/deep [post
    [content-type: "application/json"
     authorization: (append copy "Bearer " xai-key)]
    (to-json to-map data)]]

grok-req: function [qq [string!]] [
  compose/deep [
    model: (xai-model) stream: (false)
    messages: [
      (to-map compose [role: "system" content: (sys-prompt)])
      (to-map compose [role: "user" content: (qq)])]]]

grok: function [qq [string!]] [
  set [grok-status grok-headers grok-body]
    jp xai-url grok-req qq
  set 'grok-body load-json grok-body]
