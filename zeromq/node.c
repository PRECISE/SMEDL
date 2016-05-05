//  Pub/Sub node
//  Connects PUB socket to tcp://localhost:5559
//  Connects SUB socket to tcp://localhost:5560
//  Compile (OS X): gcc node.c -L/usr/local/lib -lzmq -I/usr/local/include -o node

#include "zhelpers.h"

int main (void)
{
    //  Prepare our context, subscriber, and publisher
    void *context = zmq_ctx_new ();

    void *publisher = zmq_socket (context, ZMQ_PUB);
    int rc = zmq_connect (publisher, "tcp://localhost:5559");
    assert (rc == 0);

    void *subscriber = zmq_socket (context, ZMQ_SUB);
    rc = zmq_connect (subscriber, "tcp://localhost:5560");
    assert (rc == 0);

    zmq_setsockopt (subscriber, ZMQ_SUBSCRIBE, "A", 1);

    while (1) {
        printf ("Before Send\n");
        s_sendmore (publisher, "A");
        s_send (publisher, "Hello from Node 1!");
        printf ("Sent\n");
        sleep (5);

        //  Read envelope with address
        char *address = s_recv (subscriber);
        //  Read message contents
        char *contents = s_recv (subscriber);
        printf ("[%s] %s\n", address, contents);
        free (address);
        free (contents);
    }

    zmq_close (publisher);
    zmq_close (subscriber);
    zmq_ctx_destroy (context);
    return 0;
}