//  Simple message queuing broker
//  Same as request-reply broker but using shared queue proxy
//  See: http://zguide.zeromq.org/page:all#ZeroMQ-s-Built-In-Proxy-Function
//  Compile (OS X): gcc broker.c -L/usr/local/lib -lczmq -I/usr/local/include -o broker

#include "czmq.h"

static int
capture_event (zloop_t *loop, zsock_t *reader, void *arg)
{
    zmsg_t *msg = zmsg_recv (reader);
    assert (msg);
    char *msg_str = zmsg_popstr (msg);
    printf ("CAPTURED: %s\n", msg_str);
    free (msg_str);
    zmsg_destroy (&msg);
    return 0;
}

int main (void)
{
    bool verbose = true;

    // Create and configure our proxy
    zactor_t *proxy = zactor_new (zproxy, NULL);
    assert (proxy);
    if (verbose) {
     zstr_sendx (proxy, "VERBOSE", NULL);
     zsock_wait (proxy);
    }
    zstr_sendx (proxy, "FRONTEND", "XSUB", "tcp://*:5559", NULL);
    zsock_wait (proxy);
    zstr_sendx (proxy, "BACKEND", "XPUB", "tcp://*:5560", NULL);
    zsock_wait (proxy);

    // Test capture functionality
    zsock_t *capture = zsock_new_pull ("inproc://capture");
    assert (capture);

    // Switch on capturing, check that it works
    zstr_sendx (proxy, "CAPTURE", "inproc://capture", NULL);
    zsock_wait (proxy);

    // Setup loop for captures
    zloop_t *loop = zloop_new ();
    assert (loop);
    zloop_set_verbose (loop, verbose);

    // Set up reader for captures
    int rc = zloop_reader (loop, capture, capture_event, NULL);
    assert (rc == 0);
    zloop_reader_set_tolerant (loop, capture);
    zloop_start (loop);

    // Loop indefinitely
    //while (1) {}

    // cleanup (never reached)
    zloop_destroy (&loop);
    assert (loop == NULL);
    zsock_destroy (&capture);
    assert (capture == NULL);
    zactor_destroy (&proxy);
    assert (proxy == NULL);

    return 0;
}