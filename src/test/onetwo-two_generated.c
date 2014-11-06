enum { TWOONE, ONETWO } stateset;

stateset currentState = TWOONE;

void foo(c) {
  switch (currentState) {
    case ONETWO:
      currentState = TWOONE;
      break;
}

void bar(c) {
  switch (currentState) {
    case TWOONE:
      currentState = ONETWO;
      break;
}

