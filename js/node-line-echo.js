"use strict"
var net = require('net')

class LineQueue {
    constructor(cb) {
        this.cb = cb;
        this.buffer = '';
    }
    flush() {
        this.cb(this.buffer);
        this.buffer = '';
    }
    push(data) {
        for (var ch of data) {
            if (typeof(ch) == 'number') ch = String.fromCharCode(ch);
            if (ch=='\r') {}
            else if (ch=="\n") this.flush()
            else this.buffer += ch;
        }
    }
}

var server = net.createServer(function(client) {
    console.log('connected!');
    var q = new LineQueue(function(line) {
        if (line == 'bye') client.end()
        else {
            console.log('> ' + line);
            client.write(`ECHO: ${line}\r\n`);
        }
    })
    client.on('data', (data)=> q.push(data));
});

server.listen(1313, function () {
    console.log('listening...');
});
