"""
basic RabbitMQ usage

this is a refoctored version of the code from here:

    http://blogs.digitar.com/jjww/2009/01/rabbits-and-warrens/
"""
from amqplib import client_0_8 as amqp
import sys

def create_channel():
    """
    connects to the server and creates a channel.
    """
    conn = amqp.Connection(
        host="localhost:5672 ",
        userid="guest",
        password="guest",
        virtual_host="/",
        insist=False)
    chan = conn.channel()
    return conn, chan


def create_binding(chan):
    """
    Sets up the queue, echange, and bindings.

    @param chan:
    @return: None
    """
    chan.queue_declare(
        queue="the-queue",
        durable=True,
        exclusive=False,
        auto_delete=False)
    chan.exchange_declare(
        exchange="the-exchange",
        type="direct",
        durable=True,
        auto_delete=False, )
    chan.queue_bind(
        queue="the-queue",
        exchange="the-exchange",
        routing_key="the-key")


def check_messages(chan):
    """
    Prints the message, or "no messages"

    @param chan:
    @return:
    """
    msg = chan.basic_get("the-queue")
    if msg:
        print msg.body
        chan.basic_ack(msg.delivery_tag)
    else:
        print "no messages."


def message_loop(chan):
    """
    loop until a message is received,
    then exit.

    @param chan:
    """
    class Heard: something = False

    def recv_callback(msg):
        Heard.something = True
        print 'Received: ' + msg.body

    chan.basic_consume(
        queue='the-queue',
        no_ack=True,
        callback=recv_callback,
        consumer_tag="test-tag")

    while not Heard.something:
        chan.wait()
    chan.basic_cancel("test-tag")


if __name__=="__main__":

    print "setting up..."

    conn, chan = create_channel()

    print "done..."

    if "--check" in sys.argv or "--loop" in sys.argv:
        create_binding(chan)

        if "--check" in sys.argv:
            print "checking..."
            check_messages(chan)

        if "--loop" in sys.argv:
            print "looping..."
            message_loop(chan)
    else:
        print "sending message..."

        msg = amqp.Message("hello world!")
        msg.properties["delivery_mode"] = 2
        chan.basic_publish(
            msg,exchange="the-exchange",
            routing_key="the-key")

    chan.close()
    conn.close()
