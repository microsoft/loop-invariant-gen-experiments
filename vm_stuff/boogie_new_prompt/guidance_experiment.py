# %%
import guidance
# guidance.llm = guidance.llms.OpenAI("gpt-3.5-turbo")
guidance.llm = guidance.llms.OpenAI(model = "gpt-4")

# %%
conversation = guidance('''{{#system~}}
        You are a helpful extremely smart software assistant that reasons about how code behaves.
        {{~/system}}
        {{#user~}}
        Boogie is a software verification tool that given a program and a specification, attempts to prove that the program satisfies the specification.

        Consider the following Boogie code:
        ```boogie    
        {{code}}
        ```
        Keep in mind:    
        1. Uninitialized variables can have garbage values    

        Let's think step by step about the following:    
        1. What pre-conditions are given?
        2. What does the loop body do?
        3. What post-conditions are required?
        4. What is the transfer function of the loop body?
        {{~/user}}

        {{#assistant~}}
        {{gen n=1 temperature=0.7 max_tokens=1000}}
        {{~/assistant}}

        {{#user~}}
        Great! Now, what is a loop invariant? Don't output the loop invariants for the given code snippet yet.
        {{~/user}}

        {{#assistant~}}
        {{gen n=1 temperature=0.7 max_tokens=1000}}
        {{~/assistant}}

        {{#user~}}
        Great! Now, what conditions does a loop invariant need to satisfy to be correct in the given code snippet? Don't output the loop invariants for the given code snippet yet.
        {{~/user}}

        {{#assistant~}}
        {{gen n=1 temperature=0.7 max_tokens=1000}}
        {{~/assistant}}

        {{#user~}}
        Great! Now, let's think step by step. What are the loop invariants for the given code snippet?
        {{~/user}}

        {{#assistant~}}
        {{gen n=1 temperature=0.7 max_tokens=1000}}
        {{~/assistant}}

        {{#user~}}
        Amazing! Now please generate loop invariants that can be inserted into the given code snippet in the following format:

        Format:
        invariant ....;
        invariant ....;
        ...
        {{~/user}}

        {{#assistant~}}
        {{gen 'invariants' temperature=0.0 max_tokens=1000}}
        {{~/assistant}}''')

out = conversation(code="""procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 20;
while(j >= i)
// insert invariants
{
i := i + 2;
j := j - 1;
}
assert(j == 13);
}""")

        # %%
print(out['invariants'].split('```')[1].split('```')[0])

        # %%




