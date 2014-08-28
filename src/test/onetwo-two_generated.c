enum { ONETWO } stateset;

stateset currentState = ONETWO;

void foo() {
currentState = ONETWO;
}

void bar() {
currentState = ONETWO;
}

