enum { TWOONE, ONETWO, MIN } stateset;

stateset currentState = TWOONE;

void foo() {
  switch (currentState) {
    case ONETWO:
      currentState = MIN;
      break;
    case MIN:
      currentState = TWOONE;
      break;
}

