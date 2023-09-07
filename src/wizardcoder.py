from transformers import AutoTokenizer, AutoModelForCausalLM

tokenizer = AutoTokenizer.from_pretrained("./WizardCoder-15B-V1.0")
model = AutoModelForCausalLM.from_pretrained("./WizardCoder-15B-V1.0", device_map="auto")

print("Model loaded")

messages = [
"""
You are a helpful AI software assistant that reasons about how code behaves. Given a program, you can find loop invariants, which can then be used to verify some property in the program. 
Frama-C is a software verification tool for C programs. The input to Frama-C is a C program file with ACSL (ANSI/ISO C Specification Language) annotations.
For the given program, find the necessary loop invariants of the while loop to help Frama-C verify the post-condition.

Instructions:
- Make a note of the pre-conditions or variable assignments in the program.
- Analyze the loop body and make a note of the loop condition. 
- Output loop invariants that are true 
(i) before the loop execution, 
(ii) in every iteration of the loop and 
(iii) after the loop termination, 
such that the loop invariants imply the post condition.
- If a loop invariant is a conjunction, split it into its parts.
- Output all the loop invariants in one code block. For example:
```
/*@ 
    loop invariant i1;
    loop invariant i2;
*/
```
Rules:
- **Do not use variables or functions that are not declared in the program.** 
- **Do not make any assumptions about functions whose definitions are not given.**
- **All undefined variables contain garbage values. Do not use variables that have garbage values.**
- **Do not use keywords that are not supported in ACSL annotations for loops.**
- **Variables that are not explicitly initialized, could have garbage values. Do not make any assumptions about such values.**
- **Do not use the \\at(x, Pre) notation for any variable x.**
- **Do not use non-deterministic function calls.**

Consider the following C program:
```
#define assume(e) if(!(e)) return;

void main() {
  int i;
  int j;
  int x = i;
  int y = j;
  while(x!=0) {
    x--;
    y--;
  }
  if(i==j)
    if(y != 0) {;//@ assert(0);
}
}
```

You are allowed to use implication to take care of the conditional nature of the code. Use implication (==>) instead of using if-then.

For all variables, add conjunctions that bound the maximum and minimum values that they can take, if such bounds exist.

If a variable is always equal to or smaller or larger than another variable, add a conjunction for their relation.

If the assertion is guarded by a condition, use the guard condition in an implication.

If certain variables are non-deterministic at the beginning or end of the loop, use an implication to make the invariant trivially true at that location. 

Output the loop invariants for the loop in the program above. Let's think step by step.""",
"""
You are a helpful AI software assistant that reasons about how code behaves. Given a program, you can find loop invariants, which can then be used to verify some property in the program. 
Frama-C is a software verification tool for C programs. The input to Frama-C is a C program file with ACSL (ANSI/ISO C Specification Language) annotations.
For the given program, find the necessary loop invariants of the while loop to help Frama-C verify the post-condition.

Instructions:
- Make a note of the pre-conditions or variable assignments in the program.
- Analyze the loop body and make a note of the loop condition. 
- Output loop invariants that are true 
(i) before the loop execution, 
(ii) in every iteration of the loop and 
(iii) after the loop termination, 
such that the loop invariants imply the post condition.
- If a loop invariant is a conjunction, split it into its parts.
- Output all the loop invariants in one code block. For example:
```
/*@ 
    loop invariant i1;
    loop invariant i2;
*/
```
Rules:
- **Do not use variables or functions that are not declared in the program.** 
- **Do not make any assumptions about functions whose definitions are not given.**
- **All undefined variables contain garbage values. Do not use variables that have garbage values.**
- **Do not use keywords that are not supported in ACSL annotations for loops.**
- **Variables that are not explicitly initialized, could have garbage values. Do not make any assumptions about such values.**
- **Do not use the \at(x, Pre) notation for any variable x.**
- **Do not use non-deterministic function calls.**

Consider the following C program:
```
#define assume(e) if(!(e)) return 0;

int main()
{
  
  int p;
  int i;
  int leader_len;
  int bufsize;
  int bufsize_0;
  int ielen;

  if(leader_len >0); else goto END;
  if(bufsize >0); else goto END;
  if(ielen >0); else goto END;

  if (bufsize < leader_len)
    goto END;

  p = 0;
  
  bufsize_0 = bufsize;
  bufsize -= leader_len;
  p += leader_len;

  if (bufsize < 2*ielen)
    goto END;

  for (i = 0; i < ielen && bufsize > 2; i++) {
    {;//@ assert(0<=p);
}
    {;//@ assert(p+1<bufsize_0);
}
      
    p += 2;
  }

 END:;
}

```

You are allowed to use implication to take care of the conditional nature of the code. Use implication (==>) instead of using if-then.

For all variables, add conjunctions that bound the maximum and minimum values that they can take, if such bounds exist.

If a variable is always equal to or smaller or larger than another variable, add a conjunction for their relation.

If the assertion is guarded by a condition, use the guard condition in an implication.

If certain variables are non-deterministic at the beginning or end of the loop, use an implication to make the invariant trivially true at that location. 

Output the loop invariants for the loop in the program above. Let's think step by step."""
]

input_ids = tokenizer(messages, return_tensors="pt").input_ids
outputs = model.generate(
                    input_ids.to(model.device),
                    do_sample = True,
                    top_p = 0.95,
                    temperature = 0.7,
                    max_new_tokens = 1200,
                    pad_token_id = tokenizer.eos_token_id,
                    num_return_sequences = 15,
                    batch_size = 2
                )
generated_answers=tokenizer.batch_decode(outputs, skip_special_tokens=True)

for a in generated_answers:
    print(a.removeprefix())
    print("===========================================================================================================")
