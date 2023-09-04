from transformers import AutoTokenizer, AutoModelForCausalLM

tokenizer_wizardcoder = AutoTokenizer.from_pretrained("./WizardCoder-15B-V1.0")
model_wizardcoder = AutoModelForCausalLM.from_pretrained("./WizardCoder-15B-V1.0", device_map="auto")

print("Model loaded")

messages = [
    {
        "role": "system",
        "content": "You are a helpful AI software assistant that reasons about how code behaves. Given a program, you can find loop invariants, which can then be used to verify some property in the program. \nFrama-C is a software verification tool for C programs. The input to Frama-C is a C program file with ACSL (ANSI/ISO C Specification Language) annotations.\nFor the given program, find the necessary loop invariants of the while loop to help Frama-C verify the post-condition.\n\nInstructions:\n- Make a note of the pre-conditions or variable assignments in the program.\n- Analyze the loop body and make a note of the loop condition. \n- Output loop invariants that are true \n(i) before the loop execution, \n(ii) in every iteration of the loop and \n(iii) after the loop termination, \nsuch that the loop invariants imply the post condition.\n- If a loop invariant is a conjunction, split it into its parts.\n- Output all the loop invariants in one code block. For example:\n```\n/*@ \n    loop invariant i1;\n    loop invariant i2;\n*/\n```\nRules:\n- **Do not use variables or functions that are not declared in the program.** \n- **Do not make any assumptions about functions whose definitions are not given.**\n- **All undefined variables contain garbage values. Do not use variables that have garbage values.**\n- **Do not use keywords that are not supported in ACSL annotations for loops.**\n- **Variables that are not explicitly initialized, could have garbage values. Do not make any assumptions about such values.**\n- **Do not use the \\at(x, Pre) notation for any variable x.**\n- **Do not use non-deterministic function calls.**\n"
    },
    {
        "role": "user",
        "content": "\n\nConsider the following C program:\n```\n#define assume(e) if(!(e)) return;\n\nvoid main() {\n  int i;\n  int j;\n  int x = i;\n  int y = j;\n  while(x!=0) {\n\tx--;\n\ty--;\n  }\n  if(i==j)\n\tif(y != 0) {;//@ assert(0);\n}\n}\n```\n\nYou are allowed to use implication to take care of the conditional nature of the code. Use implication (==>) instead of using if-then.\n\nFor all variables, add conjunctions that bound the maximum and minimum values that they can take, if such bounds exist.\n\nIf a variable is always equal to or smaller or larger than another variable, add a conjunction for their relation.\n\nIf the assertion is guarded by a condition, use the guard condition in an implication.\n\nIf certain variables are non-deterministic at the beginning or end of the loop, use an implication to make the invariant trivially true at that location. \n\nOutput the loop invariants for the loop in the program above. Let's think step by step."
    },
]

input_ids = tokenizer_wizardcoder(messages, return_tensors="pt").input_ids
outputs = model_wizardcoder.generate(
                    input_ids.to(model_wizardcoder.device),
                    do_sample = True,
                    top_p = 0.95,
                    temperature = 0.7,
                    max_new_tokens = 1200,
                    pad_token_id = tokenizer_wizardcoder.eos_token_id,
                    num_return_sequences = 1,
                )
generated_answers=tokenizer_wizardcoder.batch_decode(outputs, skip_special_tokens=True)

print(generated_answers)
