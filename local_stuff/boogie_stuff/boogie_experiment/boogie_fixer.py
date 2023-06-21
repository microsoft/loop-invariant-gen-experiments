
import requests
import json
from langchain.utilities import BashProcess
import os
import time
from tenacity import retry, wait_exponential


#Note: The openai-python library support for Azure OpenAI is in preview.
import os
import openai
openai.api_type = "azure"
openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

# @retry(wait=wait_random_exponential(multiplier=1, max=60))
@retry(wait=wait_exponential(multiplier=1, min=20, max=60))
def call_llm(code, error):
   # prompt = [{"role":"system","content":"You are an automatic software verification assistant. You will be given Boogie code and the error returned by the Boogie verifier on execution. Your task is to analyze the error, fix ONLY the invariants in the given Boogie code and output the correct Boogie code."},{"role":"user","content":"Boogie Code:\nprocedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var x4: int;\n        var x5: int;\n        var x6: int;\n        var x7: int;\n\n        // pre-condition\n        x4 := 0;\n\n        // loop body\n        while (x4 < x5)\n        invariant x4 >= 0; // 1) x4 = 0 => x4 >= 0, 2) x4 >=0 && x4' = x4 + 1 => x4' >= 0\n        invariant x4 <= x5; // 1) x4 = 0 => x4 <= x5, 2) x4 <= x5 && x4' = x4 + 1 => x4' <= x5\n        invariant (x4 == 0 || x7 >= x6); // 1) x4 = 0 => (x4==0 || x7>=x6), 2) x4 >=0 && (x4==0 || x7>=x6) && x4' = x4 + 1 && ((x7 <= x6 => x6' = x7) || (!(x7 <= x6) => x6' = x6)) && x7' = x7 =>  (x4'==0 || x7' >= x6')\n        {\n            x4 := x4 + 1;\n            if (x7 <= x6) {\n                x6 := x7;\n            }\n        }\n\n        // post-condition\n        if (x5 > 0) {\n            assert (x7 >= x6);\n        }\n    }\n\nBoogie Error:\nboogie/6.bpl(17,9): Error: this loop invariant could not be proved on entry\nExecution trace:\n    boogie/6.bpl(12,12): anon0\n\nBoogie program verifier finished with 0 verified, 1 error"},{"role":"assistant","content":"procedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var x4: int;\n        var x5: int;\n        var x6: int;\n        var x7: int;\n\n        // pre-condition\n        x4 := 0;\n\n        // loop body\n        while (x4 < x5)\n        invariant x4 >= 0; // 1) x4 = 0 => x4 >= 0, 2) x4 >=0 && x4' = x4 + 1 => x4' >= 0\n        invariant (x4 == 0 || x7 >= x6); // 1) x4 = 0 => (x4==0 || x7>=x6), 2) x4 >=0 && (x4==0 || x7>=x6) && x4' = x4 + 1 && ((x7 <= x6 => x6' = x7) || (!(x7 <= x6) => x6' = x6)) && x7' = x7 =>  (x4'==0 || x7' >= x6')\n        {\n            x4 := x4 + 1;\n            if (x7 <= x6) {\n                x6 := x7;\n            }\n        }\n\n        // post-condition\n        if (x5 > 0) {\n            assert (x7 >= x6);\n        }\n    }"},{"role":"user","content":"Boogie Code:\nprocedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var nondet: bool;\n\n        // pre-condition\n        x1 := 1;\n        x2 := 1;\n\n        // loop body\n        while (x1 < x3)\n        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 1 => x1' >= 1\n        invariant x2 >= 1; // 1) x2 = 1 => x2 >= 1, 2) x2 >= 1 && (x2' = x1 || x2' = x2) => x2' >= 1\n        invariant x2 <= x1; // 1) x1 = 1, x2 = 1 => x2 <= x1, 2) x2 <= x1 && (x2' = x1 || x2' = x2) && x1' = x1 + 1 => x2' <= x1'\n        {\n            havoc nondet;\n            if (nondet) {\n                x2 := x1;\n            }\n            x1 := x1 + 1;\n        }\n\n        // post-condition\n        if (x3 > 1) {\n            assert (x2 < x3);\n            //assert (x2 >= 1); // This is already proven by the loop invariant x2 >= 1\n        }\n    }\n\nBoogie Error:\nboogie/17.bpl(27,13): Error: this assertion could not be proved\nExecution trace:\n    boogie/17.bpl(9,12): anon0\n    boogie/17.bpl(13,9): anon6_LoopHead\n    boogie/17.bpl(13,9): anon6_LoopDone\n    boogie/17.bpl(27,13): anon8_Then\n\nBoogie program verifier finished with 0 verified, 1 error"},{"role":"assistant","content":"procedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var nondet: bool;\n\n        // pre-condition\n        x1 := 1;\n        x2 := 1;\n\n        // loop body\n        while (x1 < x3)\n        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 1 => x1' >= 1\n        invariant x2 >= 1; // 1) x2 = 1 => x2 >= 1, 2) x2 >= 1 && (x2' = x1 || x2' = x2) => x2' >= 1\n        invariant x2 <= x1; // 1) x1 = 1, x2 = 1 => x2 <= x1, 2) x2 <= x1 && (x2' = x1 || x2' = x2) && x1' = x1 + 1 => x2' <= x1'\n        invariant x1 == 1 || x2 < x3;\n        {\n            havoc nondet;\n            if (nondet) {\n                x2 := x1;\n            }\n            x1 := x1 + 1;\n        }\n\n        // post-condition\n        if (x3 > 1) {\n            assert (x2 < x3);\n            //assert (x2 >= 1); // This is already proven by the loop invariant x2 >= 1\n        }\n    }"}]
   prompt = [{"role":"system","content":"You are an automatic software verification assistant. You will be given Boogie code and the error returned by the Boogie verifier on execution. Your task is to analyze the error, fix ONLY the invariants in the given Boogie code and output the correct Boogie code."},{"role":"user","content":"Boogie Code:\nprocedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var x4: int;\n        var x5: int;\n        var x6: int;\n        var x7: int;\n\n        // pre-condition\n        x4 := 0;\n\n        // loop body\n        while (x4 < x5)\n        invariant x4 >= 0;\n        invariant x4 <= x5;\n        invariant (x4 == 0 || x7 >= x6);\n        {\n            x4 := x4 + 1;\n            if (x7 <= x6) {\n                x6 := x7;\n            }\n        }\n\n        // post-condition\n        if (x5 > 0) {\n            assert (x7 >= x6);\n        }\n    }\n\nBoogie Error:\nboogie/6.bpl(17,9): Error: this loop invariant could not be proved on entry\nExecution trace:\n    boogie/6.bpl(12,12): anon0\n\nBoogie program verifier finished with 0 verified, 1 error"},{"role":"assistant","content":"procedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var x4: int;\n        var x5: int;\n        var x6: int;\n        var x7: int;\n\n        // pre-condition\n        x4 := 0;\n\n        // loop body\n        while (x4 < x5)\n        invariant x4 >= 0;\n        invariant (x4 == 0 || x7 >= x6);\n        {\n            x4 := x4 + 1;\n            if (x7 <= x6) {\n                x6 := x7;\n            }\n        }\n\n        // post-condition\n        if (x5 > 0) {\n            assert (x7 >= x6);\n        }\n    }"},{"role":"user","content":"Boogie Code:\nprocedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var nondet: bool;\n\n        // pre-condition\n        x1 := 1;\n        x2 := 1;\n\n        // loop body\n        while (x1 < x3)\n        invariant x1 >= 1;\n        invariant x2 >= 1;\n        invariant x2 <= x1;\n        {\n            havoc nondet;\n            if (nondet) {\n                x2 := x1;\n            }\n            x1 := x1 + 1;\n        }\n\n        // post-condition\n        if (x3 > 1) {\n            assert (x2 < x3);\n            //assert (x2 >= 1); // This is already proven by the loop invariant x2 >= 1\n        }\n    }\n\nBoogie Error:\nboogie/17.bpl(27,13): Error: this assertion could not be proved\nExecution trace:\n    boogie/17.bpl(9,12): anon0\n    boogie/17.bpl(13,9): anon6_LoopHead\n    boogie/17.bpl(13,9): anon6_LoopDone\n    boogie/17.bpl(27,13): anon8_Then\n\nBoogie program verifier finished with 0 verified, 1 error"},{"role":"assistant","content":"procedure main()\n    {\n        var x1: int;\n        var x2: int;\n        var x3: int;\n        var nondet: bool;\n\n        // pre-condition\n        x1 := 1;\n        x2 := 1;\n\n        // loop body\n        while (x1 < x3)\n        invariant x1 >= 1;\n        invariant x2 >= 1;\n        invariant x2 <= x1;\n        invariant x1 == 1 || x2 < x3;\n        {\n            havoc nondet;\n            if (nondet) {\n                x2 := x1;\n            }\n            x1 := x1 + 1;\n        }\n\n        // post-condition\n        if (x3 > 1) {\n            assert (x2 < x3);\n            //assert (x2 >= 1); // This is already proven by the loop invariant x2 >= 1\n        }\n    }"}]
   prompt.append({"role":"user", "content":f"Boogie Code:\n{code}\n\nBoogie Error:\n{error}"})

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
   


source = "boogie"
dest = "boogie_fixed1"
i = 0
for file in sorted(list(os.listdir(source))):
    if file.endswith(".bpl"):
        with open(f"{source}/{file}") as f1:
            with open(f"{source}/{file[:-4]}.out") as f2:
                code = f1.read()
                error = f2.read()
                output = ""
                if "1 verified" not in error:
                    error = error.split("STDOUT:")[1].split("STDERR:")[0].strip()
                    output = call_llm(code, error)
                else:
                    output = code
                with open(f"{dest}/{file}", "w") as f:
                    f.write(output)
                i += 1
                print(f"{i} - {file}")


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





