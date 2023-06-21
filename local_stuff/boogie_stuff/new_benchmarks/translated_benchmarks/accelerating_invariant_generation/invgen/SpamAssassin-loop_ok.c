int main()
{
        int len;
        int i;
        int j;
        int bufsize;
        int limit = bufsize - 4;
        i = 0;
        while (i < len)
        {
                j = 0;
                while (i < len && j < limit)
                {
                        if ((i + 1 < len) || unknown())
                        {
                                //__VERIFIER_assert(i+1<len);//1
                                //__VERIFIER_assert(0<=i);//2//Interesting assert
                                //__VERIFIER_assert(i<len);//3
                                //__VERIFIER_assert(0<=i); //4
                                //__VERIFIER_assert(j<bufsize);//5 //Interesting Assert
                                //__VERIFIER_assert(0<=j);
                                //        buffer[j] = msg[i];
                                j++;
                                i++;
                                //__VERIFIER_assert(i<len);//6
                                //__VERIFIER_assert(0<=i);//7
                                // __VERIFIER_assert(j<bufsize);//8 //Very intersting
                                //__VERIFIER_assert(0<=j);	//9

                                //        buffer[j] = msg[i];
                                j++;
                                i++;
                                //__VERIFIER_assert(j<bufsize);//10
                                //__VERIFIER_assert(0<=j);	//11
                                /* OK */
                                //        buffer[j] = '.';
                                j++;
                        }
                        else
                        {
                                //__VERIFIER_assert(i<len);//12
                                assert(0 <= i); // Really really interesting
                                //__VERIFIER_assert(j<bufsize);//13
                                //__VERIFIER_assert(0<=j);	//14

                                //	buffer[j] = msg[i];
                                j++;
                                i++;
                        }
                }
        }
}
