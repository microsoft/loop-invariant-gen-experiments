/*
Commit Number: 7800003a8fd28c386fcefa652376bbe7e5aa0ddb
URL: https://github.com/ArtifexSoftware/mupdf/commit/7800003a8fd28c386fcefa652376bbe7e5aa0ddb
Project Name: mupdf
License: AGPL-3.0
termination: TRUE
*/
#include "string.h"
void loadpagetree(char* obj, char* kobj) {
    char* type = obj;
    int kids = strlen(obj);
    if (strcmp(type, "Page") == 0) {
    }else if(strcmp(type, "Pages") == 0){
        for(int i =0; i < kids; i++){
            if (kobj == obj)
            {
                /* prevent infinite recursion possible in maliciously crafted PDFs */
                return;
            }
            loadpagetree(obj, kobj);
        }
}
    return;
}
int main(){
    char obj[5];
    char kobj[5];
    for(int i=0; i<4; i++){
        obj[i] = __VERIFIER_nondet_char();
        kobj[i] = __VERIFIER_nondet_char();
    }
    obj[4] = '\0';
    kobj[4] = '\0';
    return 0;
}
