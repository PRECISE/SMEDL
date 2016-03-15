enum { SWITCH, SAFEMON } stateset;

struct {
  int upbound;
  int lobound;
};
stateset currentState = SWITCH;

void changeDir(_SafeMon* c) {
  switch (currentState) {
    case SWITCH:
      currentState = SAFEMON;
      break;
    case SAFEMON:
      currentState = SAFEMON;
      break;
    default:
      //Raise error of some sort
      break;
  }
}

void updatePos(_SafeMon* c, int pos) {
  switch (currentState) {
    case SAFEMON:
      if(pos == upbound || pos == lobound) {
        currentState = SWITCH;
      }
      break;
    default:
      //Raise error of some sort
      break;
  }
}

