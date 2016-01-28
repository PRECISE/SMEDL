#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>
#include <time.h>
#include "race.h"

typedef enum { CAR_THREAD_ID } car_identity_tag;
const identity_type car_identity_types[CAR_MONITOR_IDENTITIES] = { THREAD };

CarMonitor* init_car_monitor(pthread_t *thread_id) {
    CarMonitor* monitor = (CarMonitor*)malloc(sizeof(CarMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[CAR_THREAD_ID] = init_monitor_identity(THREAD, thread_id);
    monitor->laps = 0;
    monitor->total = 0;
    put_car_monitor(monitor);
    return monitor;
}

int init_car_monitor_maps() {
    if (pthread_mutex_init(&car_monitor_maps_lock, NULL) != 0) {
        printf("\n Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < CAR_MONITOR_IDENTITIES; i++) {
        car_monitor_maps[i] = (CarMonitorMap*)malloc(sizeof(CarMonitorMap));
    }
    return 1;
}

int add_car_monitor_to_map(CarMonitor *monitor, int identity) {
    CarMonitorMap* map = car_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type, 
        monitor->identities[identity]->value, CAR_MONITOR_MAP_SIZE);
    CarMonitorRecord* record = (CarMonitorRecord*)malloc(sizeof(CarMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&car_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&car_monitor_maps_lock);
    return 1; 
}

int put_car_monitor(CarMonitor *monitor) {
    return add_car_monitor_to_map(monitor, CAR_THREAD_ID);
}

CarMonitorRecord* get_car_monitors() {
    CarMonitorRecord* results = NULL;
    CarMonitorMap* map = car_monitor_maps[0];
    for(int i = 0; i < CAR_MONITOR_MAP_SIZE; i++) {
        CarMonitorRecord* current = map->list[i];
        while(current != NULL) {
            CarMonitorRecord* record = (CarMonitorRecord*)malloc(sizeof(CarMonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;  
            current = current->next;        
        }   
    }
    return results; 
}

CarMonitorRecord* get_car_monitors_by_identity(int identity, int type, void *value) {
    CarMonitorRecord* results = NULL;
    CarMonitorMap* map = car_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, CAR_MONITOR_MAP_SIZE);
    CarMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            CarMonitorRecord* record = (CarMonitorRecord*)malloc(sizeof(CarMonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;       
        }
        current = current->next;
    }
    return results;
}

CarMonitorRecord* filter_car_monitors_by_identity(CarMonitorRecord* before, int identity, void  *value) {
    CarMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            CarMonitorRecord* record = (CarMonitorRecord*)malloc(sizeof(CarMonitorRecord)); 
            record->monitor = before->monitor;
            record->next = results;
            results = record;               
        }
        before = before->next;
    }
    return results;
}

void print_results(pthread_t thread_id) {
    CarMonitorRecord *results = get_car_monitors_by_identity(CAR_THREAD_ID, THREAD, &thread_id);
    if(results == NULL) {
        printf("No results\n");
        return;
    }
    while(results != NULL) {
        printf("Car %d:\tLaps %d, Total %d\n", (int)thread_id, results->monitor->laps, results->monitor->total);
        results = results->next;
    }
}

void lap_increment(pthread_t thread_id) {
    CarMonitorRecord *results = get_car_monitors_by_identity(CAR_THREAD_ID, THREAD, &thread_id);
    CarMonitorRecord *current = results;
    while(current != NULL) {
        pthread_mutex_lock(&current->monitor->monitor_lock);
        current->monitor->laps = current->monitor->laps + 1;
        pthread_mutex_unlock(&current->monitor->monitor_lock);
        current = current->next;
    } 
}

void total_increment() {
    CarMonitorRecord *results = get_car_monitors();
    CarMonitorRecord *current = results;
    while(current != NULL) {
        pthread_mutex_lock(&current->monitor->monitor_lock);
        current->monitor->total = current->monitor->total + 1;
        pthread_mutex_unlock(&current->monitor->monitor_lock);
        current = current->next;
    } 
}

void *run(void *p) {
  int laps = *(int*)p;
  pthread_t *thread_id = (pthread_t*)malloc(sizeof(pthread_t));
  *thread_id = pthread_self(); 
  init_car_monitor(thread_id);
  sleep(1);
  for(int i = 0; i < laps; i++) {
    lap_increment(*thread_id);
    total_increment();
    print_results(pthread_self());
    sleep(1);
    if(rand() % 12 == 0) {
        printf("Car %d crashed.\n", (int)*thread_id);
        break;
    }
  }
  pthread_exit(thread_id);
}

int main() {
  if(init_car_monitor_maps() == 0) return 0;
  srand(time(NULL));
  printf("Start\n");
  int laps1 = 10;
  int laps2 = 15;
  pthread_t t1;
  pthread_t t2;
  pthread_create(&t1, NULL, &run, &laps1);
  pthread_create(&t2, NULL, &run, &laps2);
  void *retval1;
  void *retval2;
  pthread_join(t1, &retval1);
  pthread_join(t2, &retval2);
  printf("\nFinal:\n");
  print_results(*(pthread_t*)retval1);
  print_results(*(pthread_t*)retval2);
  return 1;
}

