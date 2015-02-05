enum { SWITCH, SAFEMON } stateset;

struct {
  int upbound;
  int lobound;
};
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
}

void updatePos() {
  switch (currentState) {
    case SAFEMON:
      if(pos == upbound || pos == lobound) {
        currentState = SWITCH;
      }
      break;
  }
}

