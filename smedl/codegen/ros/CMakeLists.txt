cmake_minimum_required(VERSION 3.0.2)
project(smedl_{{sys.name}})

## Compile as C++11, supported in ROS Kinetic and newer
# set(CMAKE_CXX_STANDARD 11)

## Find catkin macros and libraries
find_package(catkin REQUIRED COMPONENTS
  roscpp
  message_generation
)

################################################
## Declare ROS messages, services and actions ##
################################################

## Generate messages in the 'msg' folder
add_message_files(
  FILES
  {% for conn in connections %}
  {{conn.channel}}Msg.msg
  {% endfor %}
)

## Generate added messages and services with any dependencies listed here
generate_messages(
  DEPENDENCIES
)

###################################
## catkin specific configuration ##
###################################
## The catkin_package macro generates cmake config files for your package
catkin_package(
  CATKIN_DEPENDS message_runtime
)

###########
## Build ##
###########

## Specify additional locations of header files
## Your package locations should be listed before other locations
include_directories(
# include
  ${catkin_INCLUDE_DIRS}
)
{% for syncset in sys.syncsets.values() %}

{% if syncset.name == 'PEDL' %}
# The following node is for the PEDL syncset. This syncset only contains the
# "PEDL" events that are asynchronous to the rest of the monitor system.
# Generally speaking, these events will come from ROS messages originating from
# an existing node, so it is rare that the node for the PEDL syncset should
# actually be built. Nonetheless, the code is included, but disabled by default
# with "if(FALSE)".
#
# If for some reason you would like to enable it, remove the "if(FALSE)" and
# "endif()", uncomment the node from the install section at the bottom of this
# file, and uncomment the node from the .launch file.
if(FALSE)
{% endif %}
add_executable(${PROJECT_NAME}_{{syncset.name}}_node
  src/{{syncset.name}}_node.cpp
  src/{{syncset.name}}_global_wrapper.c
  src/{{syncset.name}}_manager.c
  {% for decl in syncset %}
  src/{{decl.name}}_local_wrapper.c
  {% endfor %}
  {% for spec in sys.syncset_spec_names(syncset.name) %}
  src/{{spec}}_mon.c
  {% endfor %}
  src/smedl_types.c
  src/event_queue.c
  src/monitor_map.c
  src/global_event_queue.c
)
set_target_properties(${PROJECT_NAME}_{{syncset.name}}_node PROPERTIES
  OUTPUT_NAME {{syncset.name}}_node
  PREFIX ""
)
add_dependencies(${PROJECT_NAME}_{{syncset.name}}_node
  ${${PROJECT_NAME}_EXPORTED_TARGETS}
  ${catkin_EXPORTED_TARGETS}
)
target_link_libraries(${PROJECT_NAME}_{{syncset.name}}_node
  ${catkin_LIBRARIES}
)
{% if syncset.name == 'PEDL' %}
endif()
{% endif %}
{% endfor %}

#############
## Install ##
#############

## Mark executables for installation
## See http://docs.ros.org/melodic/api/catkin/html/howto/format1/building_executables.html
install(TARGETS
  {% for syncset in sys.syncsets.values() %}
  {%+ if syncset.name == 'PEDL'}#{% endif %}${PROJECT_NAME}_{{syncset.name}}_node
  {% endfor %}
  RUNTIME DESTINATION ${CATKIN_PACKAGE_BIN_DESTINATION}
)
