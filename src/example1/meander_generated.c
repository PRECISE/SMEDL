enum { SWITCH, SAFEMON } stateset;

int upbound;
int lobound;

stateset currentState = SWITCH;

void changeDir() {
  switch (currentState) {
    case SWITCH:
      currentState = SAFEMON;
      break;
    case SAFEMON:
      currentState = SAFEMON;
      break;
}

void updatePos() {
  switch (currentState) {
    case SAFEMON:
      currentState = SWITCH;
      break;
}

