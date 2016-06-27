//  Pub/Sub node
//  Compile (OS X): gcc node.c -L/usr/local/lib -lrabbitmq -I/usr/local/include -o bin/node

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>

#include "utils.h"

static void send_rabbit(amqp_connection_state_t conn,
                       char const *queue_name)
{
  int i;
  char message[256];
  amqp_bytes_t message_bytes;

  for (i = 0; i < (int)sizeof(message); i++) {
    message[i] = i & 0xff;
  }

  message_bytes.len = sizeof(message);
  message_bytes.bytes = message;

  die_on_error(amqp_basic_publish(conn,
                                    1,
                                    amqp_cstring_bytes("amq.direct"),
                                    amqp_cstring_bytes(queue_name),
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                 "Publishing");

  printf("SENT\n");
}

int main(int argc, char const *const *argv)
{
  char const *hostname;
  char const *username;
  char const *password;
  int port, status;
  amqp_socket_t *socket = NULL;
  amqp_connection_state_t conn;

  if (argc < 5) {
    fprintf(stderr, "Usage: node host port username password\n");
    return 1;
  }

  hostname = argv[1];
  port = atoi(argv[2]);
  username = argv[3];
  password = argv[4];

  conn = amqp_new_connection();

  socket = amqp_tcp_socket_new(conn);
  if (!socket) {
    die("creating TCP socket");
  }

  status = amqp_socket_open(socket, hostname, port);
  if (status) {
    die("opening TCP socket");
  }

  die_on_amqp_error(amqp_login(conn, "/", 0, 131072, 0, AMQP_SASL_METHOD_PLAIN, username, password),
                    "Logging in");

  amqp_channel_open(conn, 1);
  die_on_amqp_error(amqp_get_rpc_reply(conn), "Opening channel");

  send_rabbit(conn, "test queue");

  die_on_amqp_error(amqp_channel_close(conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
  die_on_amqp_error(amqp_connection_close(conn, AMQP_REPLY_SUCCESS), "Closing connection");
  die_on_error(amqp_destroy_connection(conn), "Ending connection");
  return 0;
}