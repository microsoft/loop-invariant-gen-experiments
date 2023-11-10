/*
Commit Number: b546212a16a6ac3e9f40f332644345ceec96a0e7
URL: https://github.com/mysql/mysql-server/commit/b546212a16a6ac3e9f40f332644345ceec96a0e7
Project Name: mysql-server
License: GPL-2.0
termination: FALSE
*/
#define pthread_mutex_t int

int pthread_mutex_trylock( pthread_mutex_t* mutex)
{
    //return __VERIFIER_nondet_int();
    return 0;
}

#define pthread_mutex_trylock my_pthread_mutex_trylock

int my_pthread_mutex_trylock(pthread_mutex_t *mutex)
{
  int error=pthread_mutex_trylock(mutex);
  if (error == 1)			/* Safety if the lib is fixed */
    return 0;				/* Mutex was locked */
   return error;
};


int main()
{
    pthread_mutex_t mutex1 = 2;
    pthread_mutex_t* mutex = &mutex1;
    int rc = my_pthread_mutex_trylock(mutex);
    return 0;
}
