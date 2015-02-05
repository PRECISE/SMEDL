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
      if(+pos(4,5) > -y.a.b.c(2) + -2 + 1 && pos == lobound) {
        currentState = SWITCH;
      }
      break;
}

