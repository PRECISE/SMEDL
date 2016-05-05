//  Simple message queuing broker
//  Same as request-reply broker but using shared queue proxy
//  See: http://zguide.zeromq.org/page:all#ZeroMQ-s-Built-In-Proxy-Function
//  Compile (OS X): gcc broker.c -L/usr/local/lib -lzmq -I/usr/local/include -o broker

#include "zhelpers.h"

int main (void)
{
    void *context = zmq_ctx_new ();

    //  Socket facing publishers
    void *frontend = zmq_socket (context, ZMQ_XSUB);
    int rc = zmq_bind (frontend, "tcp://*:5559");
    assert (rc == 0);

    //  Socket facing subscribers
    void *backend = zmq_socket (context, ZMQ_XPUB);
    rc = zmq_bind (backend, "tcp://*:5560");
    assert (rc == 0);

    //  Start the proxy
    zmq_proxy (frontend, backend, NULL);

    //  We never get here…
    zmq_close (frontend);
    zmq_close (backend);
    zmq_ctx_destroy (context);
    return 0;
}