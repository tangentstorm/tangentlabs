"use strict"
var net = require('net'),
    readline = require('readline')

var server = net.createServer(function(client) {
    var rl = readline.createInterface(client, client)
    rl.question("what up, homie?", function(whatup) {
        console.log(whatup)
        client.end("good talk. seeya.\r\n")
    })
})

server.listen(1313, function () {
    console.log('listening...')
})
