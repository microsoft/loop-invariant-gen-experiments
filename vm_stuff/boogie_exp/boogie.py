
import os
import openai
from tenacity import retry, wait_exponential

openai.api_type = "azure"
openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

# @retry(wait=wait_random_exponential(multiplier=1, max=60))
@retry(wait=wait_exponential(multiplier=1, min=20, max=60))
def call_llm(code):
   # prompt = [{"role":"system","content":"You are a synthesis engine for loop invariants. Given a C file with a single loop and preconditions and postconditions, you first translate C code to Boogie. Then, you add loop invariants to the Boogie code so that Boogie code is verified. For each invariant added, add reasoning in comments for how,\n1) precondition implies the invariant holds before the loop is executed,\n2) loop condition and invariant at beginning of loop body implies invariant holds after loop body is executed\n\nYou are not allowed to assume or assert anything besides those already present in the code.\n\nBe careful about using uninitialized variables in invariants without an or clause or implies clause because those variables have garbage values"},{"role":"user","content":"int main()  \n{  \n    int z1,z2,z3;  \n    int x = 0;  \n    int m = 0;  \n    int n;  \n  \n    while (x < n) {  \n        if (unknown()) {  \n            m = x;  \n        }  \n        x = x + 1;  \n    }  \n  \n    if(n > 0) {  \n       //assert (m < n);  \n       assert (m >= 0);  \n    }  \n}"},{"role":"assistant","content":"procedure main()  \n    {  \n        var z1: int;  \n        var z2: int;  \n        var z3: int;  \n        var x: int;  \n        var m: int;  \n        var n: int;  \n        var nondet: bool;  \n\n        // pre-condition\n        x := 0;\n        m := 0;  \n  \n        // loop body  \n        while (x < n)  \n        invariant x >= 0; // 1) x = 0 => x >= 0, 2) x >=0 && x' = x + 1 => x' >=0\n        // invariant x <= n is incorrect because on loop entry n is uninitialized and will have garbage values so !(x =0 => x <=n)\n        invariant 0 <= m && m <= x;  // 1) x = 0, m = 0 => 0 <= m && m <= x, 2) 0 <= m && m <= x && (m' = m || m' = x) && x' = x + 1 => 0 <= m' && m' <= x'\n        {  \n            havoc nondet;  \n            if (nondet) {  \n                m := x;  \n            }  \n            x := x + 1;  \n        }  \n  \n        // post-condition  \n        if (n > 0) {  \n            assert(m >= 0);  \n        }  \n    }"},{"role":"user","content":"int main()\n{\n    int x = 0;\n    int y, z;\n\n    while(x < 500) {\n       x += 1;\n       if( z <= y) {\n          y = z;\n       }\n    }\n\n    assert (z >= y);\n}"},{"role":"assistant","content":"procedure main()\n    {\n        var x: int;\n        var y: int;\n        var z: int;\n\n        // pre-condition\n        x := 0;\n\n        // loop body\n        while (x < 500)\n        invariant x >= 0; // 1) x = 0 => x >= 0, 2) x >=0 && x' = x + 1 => x' >= 0\n        invariant (x == 0 || z >= y); 1) x = 0 => (x==0 || z>=y), 2) x >=0 && (x==0 || z>=y) && x' = x + 1 && ((z <= y => y' = z) || (!(z <= y) => y' = y)) && z' = z =>  (x'==0 || z' >= y')\n        // invariant z >= y is incorrect because on loop entry y and z are uninitialized and will have garbage values\n        {\n            x := x + 1;\n            if (z <= y) {\n                y := z;\n            }\n        }\n\n        // post-condition\n        assert (z >= y);\n    }"},{"role":"user","content":"int main()\n{\n    int x = 0;\n    int size;\n    int y, z;\n\n    while(x < size) {\n       x += 1;\n       if( z <= y) {\n          y = z;\n       }\n    }\n\n    if(size > 0) {\n       assert (z >= y);\n    }\n}"},{"role":"assistant","content":"procedure main()\n    {\n        var x: int;\n        var size: int;\n        var y: int;\n        var z: int;\n\n        // pre-condition\n        x := 0;\n\n        // loop body\n        while (x < size)\n        invariant x >= 0; // 1) x = 0 => x >= 0, 2) x >=0 && x' = x + 1 => x' >= 0\n        invariant x <= size; // 1) x = 0 => x <= size, 2) x <= size && x' = x + 1 => x' <= size\n        invariant (x == 0 || z >= y); // 1) x = 0 => (x==0 || z>=y), 2) x >=0 && (x==0 || z>=y) && x' = x + 1 && ((z <= y => y' = z) || (!(z <= y) => y' = y)) && z' = z =>  (x'==0 || z' >= y')\n        {\n            x := x + 1;\n            if (z <= y) {\n                y := z;\n            }\n        }\n\n        // post-condition\n        if (size > 0) {\n            assert (z >= y);\n        }\n    }"}]
   prompt = [{"role":"system","content":"You are a synthesis engine for loop invariants. Given a C file with a single loop and preconditions and postconditions, you first translate C code to Boogie. Then, you add loop invariants to the Boogie code so that Boogie code is verified. You are not allowed to assume or assert anything besides those already present in the code. Be careful about using uninitialized variables in invariants without an or clause or implies clause because those variables have garbage values"},{"role":"user","content":"int main()  \n{  \n    int z1,z2,z3;  \n    int x = 0;  \n    int m = 0;  \n    int n;  \n  \n    while (x < n) {  \n        if (unknown()) {  \n            m = x;  \n        }  \n        x = x + 1;  \n    }  \n  \n    if(n > 0) {  \n       //assert (m < n);  \n       assert (m >= 0);  \n    }  \n}"},{"role":"assistant","content":"procedure main()  \n    {  \n        var z1: int;  \n        var z2: int;  \n        var z3: int;  \n        var x: int;  \n        var m: int;  \n        var n: int;  \n        var nondet: bool;  \n\n        // pre-condition\n        x := 0;\n        m := 0;  \n  \n        // loop body  \n        while (x < n)  \n        invariant x >= 0;\n        invariant 0 <= m && m <= x;\n        {  \n            havoc nondet;  \n            if (nondet) {  \n                m := x;  \n            }  \n            x := x + 1;  \n        }  \n  \n        // post-condition  \n        if (n > 0) {  \n            assert(m >= 0);  \n        }  \n    }  "},{"role":"user","content":"int main()\n{\n    int x = 0;\n    int y, z;\n\n    while(x < 500) {\n       x += 1;\n       if( z <= y) {\n          y = z;\n       }\n    }\n\n    assert (z >= y);\n}"},{"role":"assistant","content":"procedure main()\n    {\n        var x: int;\n        var y: int;\n        var z: int;\n\n        // pre-condition\n        x := 0;\n        \n        // loop body\n        while (x < 500)\n        invariant x >= 0;\n        invariant (x == 0 || z >= y);\n        {\n            x := x + 1;\n            if (z <= y) {\n                y := z;\n            }\n        }\n\n        // post-condition\n        assert (z >= y);\n    }"}]
   prompt.append({"role":"user", "content":f"{code}"})

   response = openai.ChatCompletion.create(
   engine="gpt-4",
   messages = prompt,
   temperature=0.2,
   max_tokens=1000,
   top_p=0.95,
   frequency_penalty=0,
   presence_penalty=0,
   stop=None)
   return response.choices[0].message.content
   

# %%
i = 0
files = list(os.listdir("c_benchmark"))
tot_files = len(files)
# tot_files = 1
retry = 0
fail_list = []
while i < tot_files:
    with open(f"c_benchmark/{files[i]}") as f:
        try:
            code = f.read()
            output = call_llm(code)
            with open(f"boogie/{files[i][:-2]}.bpl", "w") as f:
                f.write(output)
            print(f"{i+1}/{tot_files}")

            i += 1
            
        except Exception as e:
            print(f"FAILED {i} - {str(e)}")
            retry += 1
            if retry == 10:
                fail_list.append(i)
                retry = 0
                continue

# %%
print(fail_list)

# %%
# call_llm("""
# int main() {
#   // variable declarations
#   int x;
#   int y;
#   // pre-conditions
#   (x = 1);
#   (y = 0);
#   // loop body
#   while ((y < 1000)) {
#     {
#     (x  = (x + y));
#     (y  = (y + 1));
#     }

#   }
#   // post-condition
# assert( (x >= y) );
# }
# """)

# %%



