#ifndef EXPLORER_H
#define EXPLORER_H

int make_map(char*[]);

int** make_temp_view();

void free_temp_view(int**);

int** rotate_temp_view(int**);

void set_rotated_view(int**);

void get_view();

int get_view_spot(int);

void update_map(int, int);

void move(int, int);

void move_to_spot(int);

void move_within_view(int, int);

int get_targets_in_view();

int move_max_straight();

int pivot();

int is_wall();

void rotate_facing();

int lawnmower();

void print_view();

#endif