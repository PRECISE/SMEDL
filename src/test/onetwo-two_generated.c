enum { TWOONE, ONETWO } stateset;

stateset currentState = TWOONE;

void foo() {
  switch (currentState) {
    case ONETWO:
      currentState = TWOONE;
      break;
}

void bar() {
  switch (currentState) {
    case TWOONE:
      currentState = ONETWO;
      break;
}

