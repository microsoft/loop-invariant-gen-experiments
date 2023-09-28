import json
import re

failed_benchmarks = [
    "../new_benchmarks/original_benchmarks/accelerating_invariant_generation/cav/35.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loops/sum03-2.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/hola/04.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/fig1.v.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-lit/gsv2008.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loops/while_infinite_loop_1.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loops/while_infinite_loop_2.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-lit/gsv2008_true-unreach-call_true-termination.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-acceleration/overflow_1-1.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/crafted/overflow_safe1.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-zilu/benchmark24_conjunctive.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-invgen/MADWiFi-encode_ie_ok.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/invgen/MADWiFi-encode_ie_ok.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/invgen/MADWiFi-encode_ie_ok.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-invgen/MADWiFi-encode_ie_ok_true-unreach-call_true-termination.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/incn.v.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/hola/22.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-invariants/even.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-invariants/mod4.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-invariants/odd.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/VeriMAP/TRACER-testloop17_VeriMAP_true.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/VeriMAP/TRACER-testloop9_VeriMAP_true.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/sum01.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/svcomp/sum01_true.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/sum01.v.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/sum04n.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/sum04n.v.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loops/sum01-2.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loops/sum01_true-unreach-call_true-termination.i.annot.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/crafted/diamond_safe1.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-acceleration/diamond_1-1.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-new/half.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-new/half_true-unreach-call_true-termination.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-lit/ddlm2013.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-lit/ddlm2013_true-unreach-call.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/crafted/diamond_safe2.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-acceleration/diamond_2-2.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/sum01_safe.v.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-lit/gj2007b_true-unreach-call_true-termination.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-lit/cggmp2005.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/ICE/benchmarks/cggmp2005_true-unreach-call.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/llreve/fib_merged_safe.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/hola/42.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/cav/20.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/sharma_splitter/ex1.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/sharma_splitter/ex2.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/pie/hola/21.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/dagger/cars.c"
]

new_failed_benchmarks = [
    "../new_benchmarks/original_benchmarks/sv-benchmarks/loop-invariants/bin-suffix-5.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loops-crafted-1/vnew2.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loop-new/count_by_k.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-new/count_by_k_true-unreach-call_true-termination.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/dagger/fig2.c",
"../new_benchmarks/original_benchmarks/LinearArbitrary-SeaHorn/loops/loop-new/count_by_nondet_true-unreach-call_true-termination.c",
"../new_benchmarks/original_benchmarks/sv-benchmarks/loops-crafted-1/mono-crafted_6.c",
"../new_benchmarks/original_benchmarks/accelerating_invariant_generation/invgen/split.c"
]

log_1_f = open("loopy_2023_08_25_13_54_09/final_rechecked_re_filtered.json", "r", encoding='utf-8')
log_1 = json.load(log_1_f)
log_1 = log_1["logs"]
log_1_f.close()

log_2_f = open("loopy_2023_08_13_23_52_42/final_rechecked_rechecked_re_filtered.json", "r", encoding='utf-8')
log_2 = json.load(log_2_f)
log_2 = log_2["logs"]
log_2_f.close()

invariants = {f: [] for f in new_failed_benchmarks}

for i in log_1:
    if i["file"] in new_failed_benchmarks:
        if "invariants" not in i.keys():
            print("No invariants", i["file"])
            continue
        invariants[i["file"]].extend(i["invariants"])

for i in log_2:
    if i["file"] in new_failed_benchmarks:
        if "invariants" not in i.keys():
            print("No invariants", i["file"])
            continue
        invariants[i["file"]].extend(i["invariants"])

for f in new_failed_benchmarks:
    b_invs = invariants[f]
    inv_string = "".join(b_invs)
    invariant_expressions = re.findall(r"loop invariant (.+);", inv_string)
    invariant_expressions = [x.strip() for x in invariant_expressions]
    invariant_expressions = list(set(invariant_expressions))
    invariant_expressions = sorted(invariant_expressions)
    invariant_expressions = ",TT ".join(invariant_expressions)
    invariants[f] = {"completions" : b_invs, "expressions" : invariant_expressions}

with open("invariants_new.json", "w") as f:
    json.dump(invariants, f, indent=4, ensure_ascii=False)