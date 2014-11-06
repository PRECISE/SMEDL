enum { SWITCH, SAFEMON } stateset;

struct {
  int upbound;
  int lobound;
};

stateset currentState = SWITCH;

void changeDir(c) {
  switch (currentState) {
    case SWITCH:
      currentState = SAFEMON;
      break;
    case SAFEMON:
      currentState = SAFEMON;
      break;
}

void updatePos(c) {
  switch (currentState) {
    case SAFEMON:
      currentState = SWITCH;
      break;
}

