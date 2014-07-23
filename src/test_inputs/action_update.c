enum { MIN1 } stateset;

int bar;

stateset currentState = MIN1;

void foo(int x) { if (x==1) bar = x; currentState = MIN1; }
