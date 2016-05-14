//  Pub/Sub node
//  Connects PUB socket to tcp://localhost:5559
//  Connects SUB socket to tcp://localhost:5560
//  Compile (OS X): gcc node.c -L/usr/local/lib -lczmq -I/usr/local/include -o node

#include "zhelpers.h"
#include <sched.h>
//#include "czmq.h"


/*static int
capture_event (zloop_t *loop, zsock_t *reader, void *arg)
{
    zmsg_t *msg = zmsg_recv (reader);
    assert (msg);
    char *msg_str = zmsg_popstr (msg);
    printf ("CAPTURED: %s\n", msg_str);
    free (msg_str);
    zmsg_destroy (&msg);
    return 0;
}*/


int main (void)
{
    
    //bool verbose = true;
    
    /*zactor_t *proxy = zactor_new (zproxy, NULL);
    assert (proxy);
    if (verbose) {
       zstr_sendx (proxy, "VERBOSE", NULL);
       zsock_wait (proxy);
    }
     
    zstr_sendx (proxy, "FRONTEND", "XSUB", "tcp://*:5560", NULL);
    zsock_wait (proxy);*/

    // Test capture functionality
    /*zsock_t *capture = zsock_new_pull (">tcp://localhost:5560");
    assert (capture);
    
    // Setup loop for captures
    zloop_t *loop = zloop_new ();
    assert (loop);
    zloop_set_verbose (loop, verbose);
    
    // Set up reader for captures
    int rc = zloop_reader (loop, capture, capture_event, NULL);
    assert (rc == 0);
    zloop_reader_set_tolerant (loop, capture);
    zloop_start (loop);

    zloop_destroy (&loop);
    assert (loop == NULL);
    zsock_destroy (&capture);
    assert (capture == NULL);*/

    
    
    //  Prepare our context, subscriber, and publisher
    void *context = zmq_ctx_new ();


    void *subscriber = zmq_socket (context, ZMQ_SUB);
    int rc = zmq_connect (subscriber, "tcp://localhost:5560");
    assert (rc == 0);

    zmq_setsockopt (subscriber, ZMQ_SUBSCRIBE, "/", 1);

    while (1) {
        
        //  Read envelope with address
        //char *address = s_recv (subscriber);
        //  Read message contents
        char *contents = s_recv (subscriber);
        if(contents !=NULL){
            printf ("[%s]\n", contents);
        }
        //free (address);
        free (contents);
    }

    zmq_close (subscriber);
    zmq_ctx_destroy (context);
    return 0;
}