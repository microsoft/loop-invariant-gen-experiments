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
                        if (i + 1 < len)
                        {
                                assert(i + 1 < len); // 1
                                assert(0 <= i);      // 2//Interesting assert
                                if (unknown())
                                        goto ELSE;
                                assert(i < len);     // 3
                                assert(0 <= i);      // 4
                                assert(j < bufsize); // 5 //Interesting Assert
                                assert(0 <= j);
                                //        buffer[j] = msg[i];
                                j++;
                                i++;
                                assert(i < len);     // 6
                                assert(0 <= i);      // 7
                                assert(j < bufsize); // 8 //Very intersting
                                assert(0 <= j);      // 9

                                //        buffer[j] = msg[i];
                                j++;
                                i++;
                                assert(j < bufsize); // 10
                                assert(0 <= j);      // 11
                                /* OK */
                                //        buffer[j] = '.';
                                j++;
                        }
                        else
                        {
                        ELSE:
                                assert(i < len);     // 12
                                assert(0 <= i);      // Really really interesting
                                assert(j < bufsize); // 13
                                assert(0 <= j);      // 14

                                //	buffer[j] = msg[i];
                                j++;
                                i++;
                        }
                }
        }
}
