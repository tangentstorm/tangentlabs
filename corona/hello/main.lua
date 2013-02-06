local textObject = display.newText( "Hello World!", 50, 50, nil, 24 )
textObject:setTextColor( 255, 0, 0 )

-- C:\Program Files (x86)\Ansca\Corona SDK\Sample Code

local button = display.newImage( "button.png" )
button.x = display.contentWidth / 2
button.y = display.contentHeight - 50

function button:tap (event)
   local r = math.random(0, 255)
   local g = math.random(0, 255)
   local b = math.random(0, 255)
   textObject:setTextColor(r, g, b)
end

button:addEventListener("tap", button)
transition.to( textObject, { time=1000, y=textObject.y+100 } )
transition.to( button, { time=1000, y=button.y-100 } )