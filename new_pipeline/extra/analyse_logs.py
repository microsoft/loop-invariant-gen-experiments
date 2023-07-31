import sys
import json

def getfiles(filename, mode, healing, phrase=None):
    trueset = []
    falseset = []
    errorset = []
    invariant = { }
    checker_message = { }
    with open(filename) as f:
        d = json.load(f)
        for bench in d["logs"]:
            cfilename = bench["file"]
            if healing:
                bench = bench["healing_conversations"][-1]
            if mode == "invariant":
                if "checker_message_after_prune" in bench:
                    checker_message[cfilename] = bench["checker_message_after_prune"]
                elif "checker_message_after_nudge_and_prune" in bench:
                    checker_message[cfilename] = bench["checker_message_after_nudge_and_prune"]
                elif "checker_message" in bench:
                    checker_message[cfilename] = bench["checker_message"]
                else:
                    assert(0)
                if "final_code_outputs" in bench:
                    invariant[cfilename] = bench["final_code_outputs"]
                else:
                    invariant[cfilename] = "Not found"
            elif mode == "statistics":
                if not phrase in bench:
                    errorset.append(cfilename)
                    continue
                success = bench[phrase]
                if success:
                    trueset.append(cfilename)
                else:
                    falseset.append(cfilename)
    if mode == "statistics":
        return trueset, falseset, errorset
    elif mode == "invariant":
        return invariant, checker_message
    else:
        assert False

def print_file(filename):
    fileloc = "../"
    with open(fileloc + filename, 'r') as f:
        print(f.read())

if len(sys.argv) < 3:
    print("Usage: analyse <phase1-file> <healing-file> [statistics|invariant]")
    sys.exit(-1)

if "loopy" in sys.argv[1] and "healing" in sys.argv[2]:
    pass
else:
    print("Wrong order of files: analyse <phase1-file> <healing-file>")
    sys.exit(-1)

mode = sys.argv[3]
if mode == "statistics":
    ta, fa, ea = getfiles(sys.argv[1], mode, False, "checker_output")
    tb, fb, eb = getfiles(sys.argv[1], mode, False, "checker_output_after_prune")
    tn, fb, en = getfiles(sys.argv[1], mode, False, "checker_output_after_nudge_and_prune")
    print("Files solved in first round:", len(ta) + len(tb) + len(tn))
    print(ta + tb + tn)
    print("\n")

    tc, fc, ec = getfiles(sys.argv[2], mode, True, "checker_output")
    td, fd, ed = getfiles(sys.argv[2], mode, True, "checker_output_after_prune")
    print("Files solved in second round (healing):", len(tc) + len(td))
    print(tc + td)
    print("\n")
    print("Files not solved:", len(fd))
    print(fd)
    print("\n")
    print("Files crashed:", len(ea) + len(ec))
    print(ea + ec)
    print("\n")
elif mode == "invariant":
    phase1_inv, co1 = getfiles(sys.argv[1], mode, False)
    phase2_inv, co2 = getfiles(sys.argv[2], mode, True)
    cfile = sys.argv[4]
    print_file(cfile)
    print("After first phase:")
    print(phase1_inv[cfile])
    print(co1[cfile])
    print("\n")
    print("After healing phase:")
    print(phase2_inv[cfile])
    print(co2[cfile])
else:
    print("Mode: statistics|invariant")
    sys.exit(-1)

