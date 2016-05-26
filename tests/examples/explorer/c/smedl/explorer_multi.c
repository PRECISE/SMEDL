#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include "explorer_mon.h"
#include "explorer_multi.h"
#include <time.h>

//input size
#define ROWNUM 60
#define COLUMNNUM 120

typedef enum { up, left, down, right } Direction;
pthread_mutex_t print_lock;
pthread_mutex_t checker_lock;
pthread_mutex_t eventAdder_lock;
pthread_mutex_t moveAdder_lock;


__thread int explorer_id;
__thread int map[ROWNUM][COLUMNNUM];
__thread int multiview[3][3];
__thread int location[2];
__thread Direction scan_direction;
__thread Direction facing;
__thread char** robotData;
__thread struct ExplorerData *data;
__thread struct ExplorerMonitor *mon;
__thread int eventNum;

int target_route[9] = {6, 7, 8, 5, 4, 3, 0, 1, 2};

int overAllEventNum = 0;
int overAllMoves = 0;

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


int make_map(char **input) {
    if(sscanf(input[0], "%i", &location[0]) != 1 || sscanf(input[1], "%i", &location[1]) != 1) {
        return 1;
    }

    for(int i = 3; i < ROWNUM*COLUMNNUM + 2; i++) {
        if(sscanf(input[i], "%i", &map[(i-3)/COLUMNNUM][(i-3)%COLUMNNUM]) != 1) {
            return 1;
        }
    }
    return 0;
}


int count_targets() {
	int targets = 0;
	for(int i = 0; i < ROWNUM; i++) {
		for(int j = 0; j < COLUMNNUM; j++) {
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
        //instrumenation point for event view
        //explorer_view(mon,multiview);
        //eventNum++;
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
			if(y_view >= 0 && y_view < ROWNUM && x_view >= 0 && x_view < COLUMNNUM) {
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
    location[0] += y_delta;
    location[1] += x_delta;
    //instrumentation point for event drive and view
    //explorer_drive(mon, location[1], location[0], facing, map);
    //explorer_view(mon,multiview);
    //eventNum+=2;
    if(map[location[0]][location[1]] > 0) {
        map[location[0]][location[1]] = 0;
    }
    pthread_mutex_lock(&print_lock);
    //printf("{%d:[%d,%d]},\n", explorer_id, y_delta, x_delta);
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
                //instrumentation point for event turn
		//explorer_turn(mon, facing);
                //eventNum++;
	}

}

int lawnmower() {
	get_view();
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

    const int LENGTH = ROWNUM * COLUMNNUM + 2;
    const int TARGETNUM = 5;
    const int OBSTACLENUM = 5;
    const int CHANGENUM = TARGETNUM + OBSTACLENUM;
    int chosen[CHANGENUM];
    int chosenNum=0;
    int y,x ;
    char xstr[15]; char ystr[15];

    robotData =  (char **)malloc(LENGTH*sizeof(char*));

        for(int i=0;i< LENGTH;i++){
            robotData[i]="0";
        }
        for(int i=0;i<CHANGENUM;i++){
            chosen[i]=-2;
        }

        while(chosenNum < CHANGENUM){
            int mark = 0;
            int temp;
            temp = rand()%(ROWNUM * COLUMNNUM) + 2;
            for(int k=0;k<CHANGENUM;k++){
                if(chosen[k]==temp){
                    mark = 1; break;
                }
            }
            if(mark == 1){
                continue;
            }
            chosen[chosenNum++]=temp;
        }

        for(int i = 0; i < CHANGENUM; i++){
            if(i<TARGETNUM){
                robotData[chosen[i]] = "1";
            }else{
                robotData[chosen[i]] = "-1";
            }
        }

        y = rand()%ROWNUM;
        sprintf(ystr,"%d",y);
        x = rand()%COLUMNNUM;
        sprintf(xstr,"%d",x);
        robotData[0]=ystr;robotData[1]=xstr;



    if(make_map(robotData) == 1) {
        printf("Invalid non-int args\n");
        pthread_exit(NULL);
    }
    free(robotData);
    scan_direction = right;
    facing = right;
    pthread_mutex_lock(&print_lock);
    pthread_mutex_unlock(&print_lock);

    //instantiation of the monitor instance
    /*explorer_id = *((int*)input);
    data = (ExplorerData*)malloc(sizeof(ExplorerData));
    data->mon_y = location[0];
    data->mon_x = location[1];
    data->mon_heading = facing;
    data->id = &explorer_id;
    data->move_count = 0;
    pthread_mutex_lock(&checker_lock);
    mon = init_explorer_monitor(data);
    pthread_mutex_unlock(&checker_lock);*/

    //print_map();


    int move_count = 0;

    while(move_count < 10000 && count_targets() > 0) {
        //instrumentation point for event count
        //explorer_count(mon);
        //eventNum++;
        usleep(3000);
        lawnmower();
        move_count++;

    }
    lawnmower();


    //print_map();
    //free(data);
    //free_monitor(mon);
    pthread_mutex_lock(&eventAdder_lock);
    overAllEventNum += eventNum;
    eventNum = 0;
    overAllMoves += move_count + 1;
    pthread_mutex_unlock(&eventAdder_lock);

    pthread_exit(NULL);
}


int main(int argc, char *argv[]) {
    if(argc < 2){
         printf("number of parameters is wrong\n");
         return 0;
    }
    int k = 30;
    long time_all = 0;
    float aveTimeAll = 0;
    int aveEventAll = 0;
    int aveMoveAll = 0;
    while(k>0){
    clock_t timer;
    timer = clock();
    //instantiation of monitor maps
    //init_explorer_monitor_maps();
    //
    printf("{\"Data\":[\n");

    for(int i = 0; i < atoi(argv[1]); i++) {
        add_thread();
        pthread_create(&thread_head->id, NULL, &run, &i);
    }


    while(thread_head != NULL) {
        pthread_join(thread_head->id, NULL);
        thread_head = thread_head->next;
    }
    timer = clock() - timer;
    time_all += timer;
    if(overAllEventNum > 0)
        aveTimeAll += (timer + 0.0)/overAllEventNum;
    aveEventAll += overAllEventNum;
    aveMoveAll += overAllMoves;
    overAllMoves = 0;
    overAllEventNum = 0;
    printf ("It took me %lu clicks (%f seconds).\n",timer,((float)timer)/CLOCKS_PER_SEC);
    printf("{\"Status\":\"Success\"}]}\n");

    k--;

    sleep(1);
    }
    printf("average time:%lu,event num:%d,time per event:%f, overall moves:%d\n",time_all/30,aveEventAll/30,aveTimeAll/30, aveMoveAll/30);
    return 0;
}


void print_map() {

	pthread_mutex_lock(&print_lock);
	printf("{\"ExplorerID\":%d, \"Map\":\n\"", explorer_id);
	for(int i = 0; i < ROWNUM; i++) {
		for(int j = 0; j < COLUMNNUM; j++) {
			if(location[0] == i && location[1] == j) {
				printf("x");
			} else printf("%d", map[i][j]);
			if(j < COLUMNNUM - 1) printf(" ");
		}
		if(i == ROWNUM - 1) printf("\",");
		printf("\n");
	}
	pthread_mutex_unlock(&print_lock);

}
