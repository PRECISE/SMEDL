enum { ONETWO, TWOONE } stateset;

stateset currentState = ONETWO;

void foo() { 
  switch (currentState) {
  case ONETWO:
      currentState = TWOONE; 
  case TWOONE:
      // raise an error, need to figure out the error API; 
  }
}

void bar() { 
  switch (currentState) {
  case TWOONE:
      currentState = ONETWO; 
  case ONETWO:
      // raise an error, need to figure out the error API; 
  }
}
