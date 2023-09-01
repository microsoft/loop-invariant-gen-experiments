extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}

int foo(){
  int result;
	int res=unknown();
	
  if (res==0)
    {
//    case 0:
      result= 0;
//      break;
	}
	else if (res==5)
	{
//    case 5:
      result = 5;
//      break;
	}
	else if (res==15)
	{
//    case 15:
      result = 15;
//      break;
	}
	else
	{
//    default:
      result = 20;
    }

  return result;
}

void main(){

  int result;

  result = foo();

  __VERIFIER_assert(!( result==15 ));

  return;
}
