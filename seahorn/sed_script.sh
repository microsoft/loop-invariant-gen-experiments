for file in seahorn_benchmark/*.c; do
    # echo -e '#include "seahorn/seahorn.h"\nextern int unknown();\n' | cat - "$file" > temp && mv temp "$file"
    printf '%s\n%s\n' '#include "seahorn/seahorn.h"' 'extern int unknown();' | cat - "$file" > temp && mv temp "$file"
    sed -i 's/assert/sassert/g' "$file"
    # sed -i 's/^\(\s*int\s\+\)\(\w\+\);/\1\2 = unknown();/g' "$file"
done

