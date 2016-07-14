#include <stdio.h>
#include "distance.h"
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <assert.h>

char const *hostname="stability.cis.upenn.edu";
char const *username="brass";
char const *password="NeJa3EdoR";
char const *exchange="smedl.topic";
int port=5672;
int const maxAttributeNum = 255;

amqp_socket_t *send_socket;
amqp_connection_state_t send_conn;

void send_message(char* message, char* routing_key){
    amqp_bytes_t message_bytes;
    
    message_bytes.len = strlen(message)+1;
    message_bytes.bytes = message;
    
    amqp_bytes_t key_bytes;
    
    key_bytes.len = strlen(routing_key)+1;
    key_bytes.bytes = routing_key;
    
    
    die_on_error(amqp_basic_publish(send_conn,
                                    1,
                                    amqp_cstring_bytes(exchange),
                                    key_bytes,
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                 "Publishing");
    
}


int main(int argc, char * argv[])
{
  
    //initialization
    send_conn = amqp_new_connection();
    send_socket = amqp_tcp_socket_new(send_conn);
    if (!send_socket) {
        die("creating TCP socket");
    }
    
    int status = amqp_socket_open(send_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    
    die_on_amqp_error(amqp_login(send_conn, "/", 0, 131072, 0, AMQP_SASL_METHOD_PLAIN, username, password),
                      "Logging in");
    
    amqp_channel_open(send_conn, 1);
    die_on_amqp_error(amqp_get_rpc_reply(send_conn), "Opening channel");
    
    amqp_exchange_declare(send_conn, 1, amqp_cstring_bytes(exchange), amqp_cstring_bytes("topic"),
                          0, 0, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(send_conn), "Declaring exchange");
    

    float total_dist = total_distance();
    
    printf("abc\n");

    char message[256];
    sprintf(message, "spv_total_distance %f", total_dist);
    char routing_key[256] = "spv-spv_total_distance.0.spv_total_distance";
    send_message(message,routing_key);
    printf("Total Manhattan Distance: %f\n", total_dist);
    

    //end
    die_on_amqp_error(amqp_channel_close(send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(send_conn), "Ending connection");
    
    return 0;
}
