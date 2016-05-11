#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include "explorer_mon.h"
#include "explorer_multi.h"
#include <time.h>


typedef enum { up, left, down, right } Direction;
pthread_mutex_t print_lock;
pthread_mutex_t checker_lock;

__thread int explorer_id;
__thread int map[10][20];
__thread int multiview[3][3];
__thread int location[2];
__thread Direction scan_direction;
__thread Direction facing;
__thread struct ExplorerData *data;
__thread struct ExplorerMonitor *mon;

int target_route[9] = {6, 7, 8, 5, 4, 3, 0, 1, 2};

ThreadList *thread_head = NULL;
ExplorerInput *input_head = NULL;

void add_thread() {
  ThreadList *temp = thread_head;
  thread_head = (ThreadList*)malloc(sizeof(ThreadList));
  thread_head->next = temp;
}

void add_input(int id, char **args) {
  ExplorerInput *temp = input_head;
  input_head = (ExplorerInput*)malloc(sizeof(ExplorerInput));
  input_head->id = id;
  input_head->args = args;
  input_head->next = temp;
}

int make_map(ExplorerInput *input) {
	int offset = 202 * input->id;
	if(sscanf(input->args[offset + 1], "%i", &location[0]) != 1 || sscanf(input->args[offset + 2], "%i", &location[1]) != 1) {
		return 1;
	}
	for(int i = 3; i < 203; i++) {
		if(sscanf(input->args[offset + i], "%i", &map[(i-3)/20][(i-3)%20]) != 1) {
			return 1;
		}
	}
	return 0;
}

int count_targets() {
	int targets = 0;
	for(int i = 0; i < 10; i++) {
		for(int j = 0; j < 20; j++) {
			if(map[i][j] > 0) {
				targets++;
			}
		}
	}
	return targets;
}

int** make_temp_view() {
    int** view;
    view = (int**) malloc(3 * sizeof(int*));
    for (int i = 0; i < 3; i++) {
        view[i] = (int*) malloc(3 * sizeof(int));
    }
    return view;
}

void free_temp_view(int **view) {
    for (int i = 0; i < 3; i++) {
    	free(view[i]);
    }
    free(view);
}

int** rotate_temp_view(int **before) {
	int **rotated = make_temp_view();
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			rotated[i][j] = before[2 - j][i];
		}
	}
	free_temp_view(before);
	return rotated;
}

void set_rotated_view(int **temp_view) {
	for(int i = 0; i < facing; i++) {
		temp_view = rotate_temp_view(temp_view);
	}
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			multiview[i][j] = temp_view[i][j];
		}
	}
    explorer_view(mon,multiview);
	free_temp_view(temp_view);
	return;
}

void get_view() {
	int y_view;
	int x_view;
	int **temp_view = make_temp_view();
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			if(facing == right) {
				y_view = location[0] - 1 + i;
				x_view = location[1] + 1 + j;
			} else if(facing == left) {
				y_view = location[0] - 1 + i;
				x_view = location[1] - 3 + j;
			} else if(facing == up) {
				y_view = location[0] - 3 + i;
				x_view = location[1] - 1 + j;
			} else if(facing == down) {
				y_view = location[0] + 1 + i;
				x_view = location[1] - 1 + j;
			}
			if(y_view >= 0 && y_view < 10 && x_view >= 0 && x_view < 20) {
				temp_view[i][j] = map[y_view][x_view];
			} else {
				temp_view[i][j] = -1;
			}
		}
	}
	set_rotated_view(temp_view);
	return;
}

int get_view_spot(int spot) {
	return multiview[spot / 3][spot % 3];
}

void update_map(int y_delta, int x_delta) {
	explorer_drive(mon, location[1] + y_delta, location[0] + x_delta, facing);
    location[0] += y_delta;
	location[1] += x_delta;
	if(map[location[0]][location[1]] > 0) {
		map[location[0]][location[1]] = 0;
	}
	pthread_mutex_lock(&print_lock);
	printf("{%d:[%d,%d]},\n", explorer_id, y_delta, x_delta);
	pthread_mutex_unlock(&print_lock);
}

void move(int forward, int side) {
    if(facing == up) {
		update_map(-forward, side);
	} else if(facing == left) {
		update_map(-side, -forward);
	} else if(facing == down) {
		update_map(forward, -side);
	} else if(facing == right) {
		update_map(side, forward);
	}
}

void move_to_spot(int spot) {
	move(3 - (spot / 3), -1 + (spot % 3));
}

void move_within_view(int start, int finish) {
	int forward = (start / 3) - (finish / 3);
	int side = (finish % 3) - (start % 3);
	move(forward, side);
}

int get_targets_in_view() {
	int location = -1;
	int targets = 0;
	for(int i = 0; i < 9; i++) {
		int spot = target_route[i];
		if(get_view_spot(spot) > 0) {
			if(targets == 0) {
				if(spot == 1 && (get_view_spot(4) < 0 || get_view_spot(7) < 0)) {
					pivot();
					return 1;
				} else if(spot == 4 && get_view_spot(7) < 0) {
					pivot();
					return 1;
				} else {
					move_to_spot(spot);
				}
			} else {
				move_within_view(location, spot);
			}
			location = spot;
			targets++;
		}
	}
	return targets;
}

int move_max_straight() {
	int distance = 0;
	for(int i = 2; i >= 0; i--) {
		if(multiview[i][1] > 0) {
			distance++;
			break;
		} else if(multiview[i][1] == 0) {
			distance++;
		} else {
			break;
		}
	}
	move(distance, 0);
	return distance;
}

int pivot() {
	int target = -1;
	int apex = -1;
	//4,1
	if(get_view_spot(4) >= 0) {
		target = 4;
	} else if(get_view_spot(1) >= 0) {
		target = 1;
	}
	//6,8,3,5,0,2
	if(get_view_spot(6) >= 0) {
		apex = 6;
	} else if(get_view_spot(8) >= 0) {
		apex = 8;
	} else if(get_view_spot(3) >= 0) {
		apex = 3;
	} else if(get_view_spot(4) >= 0) {
		apex = 5;
	}
	if(apex >= 0) {
		move_to_spot(apex);
		if(target >= 0) {
			move_within_view(apex,target);
		}
		return 1;
	} else {
		return 0;
	}
}

int is_wall() {
	for(int i = 0; i < 9; i++) {
		if(get_view_spot(i) >= 0) {
			return 0;
		}
	}
	return 1;
}

void rotate_facing() {
	if(facing == scan_direction) {
		facing = (facing - 1) % 4;
		get_view();
		if(is_wall()) {
			scan_direction = (scan_direction + 2) % 4;
			facing = (facing + 2) % 4;
		}
		if(move_max_straight() == 0) {
			pivot();
		}
		facing = (facing - 1) % 4;
		get_view();
	} else {
		facing = (facing + 1) % 4;
		get_view();
		if(is_wall()) {
			scan_direction = (scan_direction + 2) % 4;
			facing = (facing + 2) % 4;
		}
		if(move_max_straight() == 0) {
			pivot();
		}
		facing = (facing + 1) % 4;
		get_view();
		explorer_turn(mon, facing);
	}

}

int lawnmower() {
	get_view();
	// scan_view(get_checker(data), location[1], location[0], facing, map); //weird instrumentation placement;
	if(get_targets_in_view() > 0) {
		return 1;
	}
	if(is_wall()) {
		rotate_facing();
		return 1;
	}
	if(move_max_straight()) {
		return 1;
	} else {
		return pivot();
	}
}

void print_view() {
	for(int i = 0; i < 3; i++) {
		printf("\n");
		for(int j = 0; j < 3; j++) {
			printf("%d ", multiview[i][j]);
		}
	}
	printf("\n");
}

void *run(void* input) {
	explorer_id = ((ExplorerInput*)input)->id;
	data = (ExplorerData*)malloc(sizeof(ExplorerData));

	if(make_map(input) == 1) {
		printf("Invalid non-int args\n");
		pthread_exit(NULL);
	}
	scan_direction = right;
	facing = right;
	pthread_mutex_lock(&print_lock);
	pthread_mutex_unlock(&print_lock);
	data->mon_y = location[0];
	data->mon_x = location[1];
	data->mon_heading = facing;
    //data->id = explorer_id;

	pthread_mutex_lock(&checker_lock);
    mon = init_explorer_monitor(data);
	pthread_mutex_unlock(&checker_lock);
	print_map();

	int move_count = 0;
	while(move_count < 200 && count_targets() > 0) {
		lawnmower();
		move_count++;
		explorer_count(mon);
	}
	lawnmower();
	print_map();
	free(data);
	free_monitor(mon);
	pthread_exit(NULL);
}

int main(int argc, char *argv[]) {
        clock_t timer;
        timer = clock();
	if((argc - 203) % 202 != 0) {
		printf("{\"Status\":\"Failed - Invalid number of args %i\n\"}]}", argc);
		return 1;
	}
	if (pthread_mutex_init(&print_lock, NULL) != 0 || pthread_mutex_init(&checker_lock, NULL) != 0) {
        printf("{\"Status\":\"Failed - Mutex init failed %i\n\"}]}", argc);
        return 1;
    }
       //
       init_explorer_monitor_maps();
       //
	printf("{\"Data\":[\n");
	int explorer_count = (argc - 1) / 202;
	for(int i = 0; i < explorer_count; i++) {
		add_input(i, argv);
	}
	while(input_head != NULL) {
		add_thread();
		pthread_create(&thread_head->id, NULL, &run, input_head);
		input_head = input_head->next;
	}
  	while(thread_head != NULL) {
    	pthread_join(thread_head->id, NULL);
    	thread_head = thread_head->next;
  	}
       timer = clock() - timer;
       printf ("It took me %lu clicks (%f seconds).\n",timer,((float)timer)/CLOCKS_PER_SEC);

  	printf("{\"Status\":\"Success\"}]}\n");
	return 0;
}

void print_map() {
	pthread_mutex_lock(&print_lock);
	printf("{\"ExplorerID\":%d, \"Map\":\n\"", explorer_id);
	for(int i = 0; i < 10; i++) {
		for(int j = 0; j < 20; j++) {
			if(location[0] == i && location[1] == j) {
				printf("x");
			} else printf("%d", map[i][j]);
			if(j < 19) printf(" ");
		}
		if(i == 9) printf("\",");
		printf("\n");
	}
	//printf("\"Coords\":[%d, %d], \"Facing\":%d}\n", mon->mon_y, mon->mon_x, mon->heading);
	pthread_mutex_unlock(&print_lock);
}
