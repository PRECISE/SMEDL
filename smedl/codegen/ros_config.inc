// vim: set ft=cpp :

//TODO For each incoming channel:
std::string {{channel}}_ros_topic = "/smedl/{{sys.name}}/channels/{{channel}}";

//TODO For each (only) outgoing channel:
std::string {{channel}}_ros_topic = "/smedl/{{sys.name}}/channels/{{channel}}";

//TODO For each channel that is directed to another monitor (and potentially
// also outgoing):
std::string {{channel}}_ros_topic = "/smedl/{{sys.name}}/channels/{{channel}}";

/* Number of messages that can be awaiting publishing for a given topic before
 * further messages will be dropped */
const uint32_t queue_size = 1000;
