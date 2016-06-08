//  Simple message queuing broker
//  See: http://api.zeromq.org/CZMQ3-0:zproxy
//  Compile (OS X): gcc broker.c -L/usr/local/lib -lczmq -I/usr/local/include -o broker

#include "czmq.h"

//  --------------------------------------------------------------------------
//  The self_t structure holds the state for one actor instance

typedef struct {
    zsock_t *pipe;              //  Actor command pipe
    zpoller_t *poller;          //  Socket poller
    zsock_t *rep;               //  Reply 'REP' socket
    bool terminated;            //  Did caller ask us to quit?
    bool verbose;               //  Verbose logging enabled?
} self_t;

static void
s_self_destroy (self_t **self_p)
{
    assert (self_p);
    if (*self_p) {
        self_t *self = *self_p;
        zsock_destroy (&self->rep);
        zpoller_destroy (&self->poller);
        free (self);
        *self_p = NULL;
    }
}

static self_t *
s_self_new (zsock_t *pipe)
{
    self_t *self = (self_t *) zmalloc (sizeof (self_t));
    if (self) {
        self->pipe = pipe;
        self->poller = zpoller_new (self->pipe, NULL);
        if (!self->poller)
            s_self_destroy (&self);
    }
    return self;
}

//  --------------------------------------------------------------------------
//  Handle a command from calling application

static int
s_self_handle_pipe (self_t *self)
{
    //  Get the whole message off the pipe in one go
    zmsg_t *request = zmsg_recv (self->pipe);
    if (!request)
        return -1;                  //  Interrupted

    char *command = zmsg_popstr (request);
    assert (command);
    if (self->verbose)
        zsys_info ("checkin_actor: API command=%s", command);

    if (streq (command, "PAUSE")) {
        zpoller_destroy (&self->poller);
        self->poller = zpoller_new (self->pipe, NULL);
        assert (self->poller);
        zsock_signal (self->pipe, 0);
    }
    else
    if (streq (command, "RESUME")) {
        zpoller_destroy (&self->poller);
        self->poller = zpoller_new (self->pipe, self->rep, NULL);
        assert (self->poller);
        zsock_signal (self->pipe, 0);
    }
    else
    if (streq (command, "VERBOSE")) {
        self->verbose = true;
        zsock_signal (self->pipe, 0);
    }
    else
    if (streq (command, "$TERM"))
        self->terminated = true;
    else {
        zsys_error ("checkin_actor: - invalid command: %s", command);
        assert (false);
    }
    zstr_free (&command);
    zmsg_destroy (&request);
    return 0;
}

//  --------------------------------------------------------------------------
//  checkin_actor() implements the checkin actor interface

void
checkin_actor (zsock_t *pipe, void *unused)
{
    self_t *self = s_self_new (pipe);
    assert (self);

    // Initialize REP socket
    assert (self->rep == NULL);
    self->rep = zsock_new_rep ("@tcp://*:5561");
    assert (self->rep);
    zpoller_add (self->poller, self->rep);

    //  Signal successful initialization
    zsock_signal (pipe, 0);


    while (!self->terminated) {
        zsock_t *which = (zsock_t *) zpoller_wait (self->poller, -1);
        if (zpoller_terminated (self->poller))
            break;          //  Interrupted
        else
        if (which == self->pipe)
            s_self_handle_pipe (self);
        else
        if (which == self->rep) {
            zsock_send (self->rep, "i", 1);
        }
    }
    s_self_destroy (&self);
}

//  --------------------------------------------------------------------------

static int
capture_event (zloop_t *loop, zsock_t *reader, void *arg)
{
    zmsg_t *msg = zmsg_recv (reader);
    assert (msg);
    char *msg_str = zmsg_popstr (msg);
    const char * EVENTSTR = "output";
    if(strstr(msg_str,EVENTSTR) != NULL){
        printf ("CAPTURED: %s\n", msg_str);
    }
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
