//TODO ROS includes

extern "C" {
#include "{{syncset}}_global_wrapper.h"
}

#include "{{syncset}}_ros_config.h"

/* Do all SMEDL initialization. Return nonzero on success, zero on failure. */
int smedl_init() {
    /* Initialize the synchronous set */
    init_{{syncset}}_syncset();
    //TODO callbacks
}

/* Do all ROS initialization. Return nonzero on success, zero on failure. */
int ros_init(int argc, char **argv) {
    ros::NodeHandle n;

    //TODO error checking?
    ros::init(argc, argv, "smedl_{{sys.name}}_{{syncset}}_node");
    
}

int main(int argc, char **argv) {
    //TODO
}
