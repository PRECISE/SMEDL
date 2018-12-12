#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "auctionmonitor_global_wrapper.h"

void call_global_wrapper(char **ev) {
    char *var1 = NULL;
    double var2 = 0;
    double var3 = 0;

    if (ev == NULL)
        return;
    char * evname = ev[0];
    if (strcmp("create_auction", evname) == 0) {
        var1 = ev[1];
        var2 = atof(ev[2]);
        var3 = atof(ev[3]);
        param *p_head = NULL;
        push_param(&p_head, NULL, NULL, NULL, &var1);//, NULL);
        push_param(&p_head, NULL, NULL, &var2, NULL);//, NULL);
        push_param(&p_head, NULL, NULL, &var3, NULL);//, NULL);
        auctionmonitor_global_import(AUCTIONMONITOR_CH1_CONNECTION, p_head);
    } else if (strcmp("bid", evname) == 0) {
        var1 = ev[1];
        var2 = atof(ev[2]);
        param *p_head = NULL;
        push_param(&p_head, NULL, NULL, NULL, &var1);//, NULL);
        push_param(&p_head, NULL, NULL, &var2, NULL);//, NULL);
        auctionmonitor_global_import(AUCTIONMONITOR_CH2_CONNECTION, p_head);
    } else if (strcmp("sold", evname) == 0) {
        var1 = ev[1];
        param *p_head = NULL;
        push_param(&p_head, NULL, NULL, NULL, &var1);//, NULL);
        auctionmonitor_global_import(AUCTIONMONITOR_CH3_CONNECTION, p_head);
    } else if (strcmp("endOfDay", evname) == 0) {
        param *p_head = NULL;
        auctionmonitor_global_import(AUCTIONMONITOR_CH4_CONNECTION, p_head);
    }
}

//argNum is the bound of event attribute numbers
//copy must be a copy of the event that can be modified
char** divideEventString(char * copy, int argNum){

    //c99 allows variable array length
    char** str = malloc(sizeof(char*)*argNum);

    str[0] = strtok(copy, ",");
    for (int i = 1; i < argNum; i++) {
        str[i] = strtok(NULL, ",");
    }

#ifdef DEBUG
    for(int i = 0; i < argNum; i++){
       printf("arg%d:%s\n",i,str[i]);
    }
#endif //DEBUG

    return str;
}

int main(int argc, char **argv) {
    auctionmonitor_set_init();

    if (argc != 2){
        printf("Usage: %s <trace_file>\n", argv[0]);
        return 1;
    }

    //open the data file
    FILE *fp = fopen(argv[1], "r");
    //file read failure
    if (fp == NULL){
        printf("empty file pointer\n");
        return 1;
    }

    char * line = NULL;
    char * copy = NULL;
    size_t len = 0;
    ssize_t read;

    int linecount = 0;
    int total_linecount = 0;
    //read file line by line
    while ((read = getline(&line, &len, fp)) != -1) {
#ifdef DEBUG
        printf("Retrieved line of length %zu :\n", read);
#endif //DEBUG
        int paraNum = 4;
        if(line[0] == 'b'){
            paraNum = 3;
        }
        else if(line[0] == 's'){//member event has
            paraNum = 2;
        }
        else if(line[0] == 'e'){//member event has
            paraNum = 1;
        }
        //construct an event and push it into the sync queue
        copy = malloc(strlen(line)+1);
        strcpy(copy, line);
        char** evParaList = divideEventString(copy,paraNum);
        if(evParaList != NULL){
            call_global_wrapper(evParaList);
        }
        //printf("%s", line);
        free(copy);
        free(evParaList);

        if (++linecount == 100000) {
            linecount = 0;
            total_linecount++;
            printf("%d00000\n", total_linecount);
        }
    }

    //printf("out of while\n");
    fclose(fp);
    if (line)
        free(line);
    return 0;
}
