enum { ONETWO, TWOONE } stateset;

stateset currentState = ONETWO;

void foo() {
  switch (currentState) {
    case ONETWO:
      currentState = TWOONE;
    case TWOONE:
      currentState = ONETWO;
  }
}
