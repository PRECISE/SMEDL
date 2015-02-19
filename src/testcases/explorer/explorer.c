#include <stdio.h>

int map[10][10];
int view[3][3];

int make_map(char *data[]) {
	for(int i = 1; i < 101; i++) {
		if(sscanf(data[i], "%i", &map[(i-1)/10][(i-1)%10]) != 1) {
			return 1;
		}
	} 
	return 0;
}

void get_view(int y_coord, int x_coord, char direction) {
	int y_view;
	int x_view;
	for(int i = 0; i < 3; i++) {
		for(int j = 0; j < 3; j++) {
			if(direction == 'r') {
				y_view = y_coord - 1 + i;
				x_view = x_coord + 1 + j;
			} else if(direction == 'l') {
				y_view = y_coord - 1 + i;
				x_view = x_coord - 3 + j;
			} else if(direction == 'u') {
				y_view = y_coord - 3 + i;
				x_view = x_coord - 1 + j;
			} else if(direction == 'd') {
				y_view = y_coord + 1 + i;
				x_view = x_coord - 1 + j;
			}
			if(y_view >= 0 && y_view < 10 && x_view >= 0 && x_view < 10) {
				view[i][j] = map[y_view][x_view];
			} else {
				view[i][j] = -1;
			}
		}
	}
	return;
}

void print_view() {
	for(int i = 0; i < 3; i++) {
		printf("\n");
		for(int j = 0; j < 3; j++) {
			printf("%d ", view[i][j]);
		}
	}
	printf("\n");
}

int main(int argc, char *argv[]) {
	if(argc == 101) {
		if(make_map(argv) == 1) {
			printf("Invalid non-int args");
			return 1;
		}
	} else {
		printf("Invalid number of args %i", argc);
		return 1;
	}
	printf("\n");
	for(int i = 0; i < 10; i++) {
		for(int j = 0; j < 10; j++) {
			printf("%d ", map[i][j]);
		}
		printf("\n");
	}
	get_view(0,0,'r');
	print_view();
	return 0;
}
