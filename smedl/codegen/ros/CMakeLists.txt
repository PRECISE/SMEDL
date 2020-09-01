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
  {% for conn in connection %}
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
{% for syncset in sys.syncsets %}

add_executable(${PROJECT_NAME}_{{syncset.name}}_node
  {{syncset.name}}_ros.cpp
  {{syncset.name}}_global_wrapper.c
  {% for decl in syncset %}
  {{decl.name}}_local_wrapper.c
  {% endfor %}
  {% for spec in sys.syncset_spec_names(syncset) %}
  {{spec}}_mon.c
  {% endfor %}
  smedl_types.c
  event_queue.c
  monitor_map.c
  global_event_queue.c
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
{% endfor %}

#############
## Install ##
#############

## Mark executables for installation
## See http://docs.ros.org/melodic/api/catkin/html/howto/format1/building_executables.html
install(TARGETS
  {% for syncset in sys.syncsets %}
  ${PROJECT_NAME}_{{syncset.name}}_node
  {% endfor %}
  RUNTIME DESTINATION ${CATKIN_PACKAGE_BIN_DESTINATION}
)
