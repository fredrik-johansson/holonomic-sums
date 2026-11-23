#!/usr/bin/env python3
"""
Benchmark driver for holsum.

Runs every constant at 10^3, 10^4, 10^5 and 10^6 digits (by default) with theta splitting, and with the
reference methods up to their own limits; writes the digits to results/digits/, appends one JSON record
per run to results/runs.jsonl, cross-checks all digit files against each other, and writes a summary
table to results/summary.md and results/summary.csv.

Finished runs are skipped when the script is restarted (delete the record from runs.jsonl, or pass
--force, to redo one).

Examples:
    ./run.py                                   # everything, 8 threads
    ./run.py --digits 1000,10000 --threads 4   # quick check
    ./run.py --constants vortex --methods theta,zeta --max-zeta 1000000
"""
import argparse
import csv
import json
import os
import subprocess
import sys
import time

ALL_CONSTANTS = ["A340440", "A085361", "Kminus1", "vortex", "hardy_littlewood", "somos", "expsqrt",
                 "khinchin_Z", "khinchin_log", "khinchin_dilog", "theodorus", "sphere"]
ALL_METHODS = ["theta", "zeta", "em", "direct"]
# methods implemented for each constant (default: theta, zeta, em)
AVAILABLE = {"somos": ["theta", "direct"], "expsqrt": ["theta", "em"],
             "khinchin_Z": ["theta", "zeta"], "khinchin_log": ["theta", "zeta"], "khinchin_dilog": ["theta", "zeta"],
             "theodorus": ["theta", "em"]}


def parse_args():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--binary", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "holsum"))
    p.add_argument("--results", default="results", help="output directory (default: results)")
    p.add_argument("--constants", default=",".join(ALL_CONSTANTS))
    p.add_argument("--methods", default=",".join(ALL_METHODS))
    p.add_argument("--digits", default="1000,10000,100000,1000000")
    p.add_argument("--threads", type=int, default=8)
    p.add_argument("--guard", type=int, default=10, help="extra digits computed for rounding control")
    p.add_argument("--max-theta", type=int, default=10**6)
    p.add_argument("--max-zeta", type=int, default=10**5, help="largest size for the zeta-value expansion")
    p.add_argument("--max-em", type=int, default=10**5, help="largest size for Euler-Maclaurin")
    p.add_argument("--max-direct", type=int, default=10**5, help="largest size for direct summation")
    p.add_argument("--max-em-vortex", type=int, default=10**4,
                   help="largest size for Euler-Maclaurin for the vortex sum (its direct part, a 2F1 per term, is slow)")
    p.add_argument("--timeout", type=float, default=None, help="per-run timeout in seconds")
    p.add_argument("--force", action="store_true", help="rerun even if a record exists")
    return p.parse_args()


def load_records(path):
    recs = {}
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line:
                    r = json.loads(line)
                    recs[(r["constant"], r["method"], r["digits"])] = r
    return recs


def digits_file(results, const, method, digits):
    return os.path.join(results, "digits", "%s_%s_%d.txt" % (const, method, digits))


def read_digits(path):
    with open(path) as f:
        return f.read().strip()


def run_one(args, const, method, digits):
    out = digits_file(args.results, const, method, digits)
    cmd = [args.binary, const, str(digits), "--method", method, "--threads", str(args.threads),
           "--guard", str(args.guard), "--out", out]
    print("  $ " + " ".join(cmd), flush=True)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        return {"constant": const, "method": method, "digits": digits, "status": "timeout",
                "total_wall": time.time() - t0}
    if p.returncode != 0 or not p.stdout.strip():
        sys.stderr.write(p.stderr)
        return {"constant": const, "method": method, "digits": digits, "status": "error %d" % p.returncode,
                "total_wall": time.time() - t0}
    rec = json.loads(p.stdout.strip().splitlines()[-1])
    rec["status"] = "ok" if rec["rounding_ok"] else "inaccurate"
    if p.stderr.strip():
        sys.stderr.write(p.stderr)
    return rec


def cross_check(args, recs):
    """Compare every digit file with every other file of the same constant (prefix comparison)."""
    checks = {}
    by_const = {}
    for (c, m, d), r in recs.items():
        if r.get("status") == "ok" and os.path.exists(digits_file(args.results, c, m, d)):
            by_const.setdefault(c, []).append((d, m))
    for c, runs in by_const.items():
        runs.sort()
        texts = {(d, m): read_digits(digits_file(args.results, c, m, d)) for d, m in runs}
        for (d, m) in runs:
            agree, disagree = [], []
            for (d2, m2) in runs:
                if (d2, m2) == (d, m):
                    continue
                a, b = texts[(d, m)], texts[(d2, m2)]
                n = min(len(a), len(b))      # truncations to fewer digits are prefixes
                (agree if a[:n] == b[:n] else disagree).append("%s/%d" % (m2, d2))
            checks[(c, m, d)] = (agree, disagree)
    return checks


def fmt_time(t):
    if t is None:
        return ""
    if t < 100:
        return "%.2f" % t
    return "%.0f" % t


def write_summary(args, recs, checks):
    cols = ["constant", "method", "digits", "status", "threads", "u0", "dual_terms", "k_terms",
            "setup_cpu", "setup_wall", "dual_cpu", "dual_wall", "k_cpu", "k_wall", "total_cpu", "total_wall",
            "peak_rss_kb", "accuracy_bits", "agrees_with", "disagrees_with"]
    keys = sorted(recs, key=lambda k: (ALL_CONSTANTS.index(k[0]) if k[0] in ALL_CONSTANTS else 99, k[2],
                                       ALL_METHODS.index(k[1]) if k[1] in ALL_METHODS else 99))
    with open(os.path.join(args.results, "summary.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(cols)
        for k in keys:
            r = dict(recs[k])
            agree, disagree = checks.get(k, ([], []))
            r["agrees_with"] = " ".join(agree)
            r["disagrees_with"] = " ".join(disagree)
            w.writerow([r.get(c, "") for c in cols])
    with open(os.path.join(args.results, "summary.md"), "w") as f:
        f.write("| constant | method | digits | dual terms | k-terms | dual cpu / wall (s) | k cpu / wall (s) "
                "| total cpu / wall (s) | peak RSS (MB) | status | cross-check |\n")
        f.write("|---|---|--:|--:|--:|--:|--:|--:|--:|---|---|\n")
        for k in keys:
            r = recs[k]
            agree, disagree = checks.get(k, ([], []))
            if disagree:
                cc = "MISMATCH: " + ", ".join(disagree)
            elif agree:
                cc = "agrees with %d other run%s" % (len(agree), "" if len(agree) == 1 else "s")
            else:
                cc = ""
            theta = r["method"] == "theta"
            f.write("| %s | %s | %d | %s | %s | %s | %s | %s / %s | %s | %s | %s |\n" % (
                r["constant"], r["method"], r["digits"],
                r.get("dual_terms", "") if theta else "", r.get("k_terms", "") if theta else "",
                ("%s / %s" % (fmt_time(r.get("dual_cpu")), fmt_time(r.get("dual_wall")))) if theta else "",
                ("%s / %s" % (fmt_time(r.get("k_cpu")), fmt_time(r.get("k_wall")))) if theta else "",
                fmt_time(r.get("total_cpu")), fmt_time(r.get("total_wall")),
                "%.0f" % (r["peak_rss_kb"] / 1024.0) if "peak_rss_kb" in r else "",
                r.get("status", ""), cc))


def main():
    args = parse_args()
    if not os.path.exists(args.binary):
        sys.exit("%s not found; run make first" % args.binary)
    os.makedirs(os.path.join(args.results, "digits"), exist_ok=True)
    runs_path = os.path.join(args.results, "runs.jsonl")
    recs = load_records(runs_path)
    limits = {"theta": args.max_theta, "zeta": args.max_zeta, "em": args.max_em, "direct": args.max_direct}
    constants = [c for c in args.constants.split(",") if c]
    methods = [m for m in args.methods.split(",") if m]
    sizes = sorted(int(float(d)) for d in args.digits.split(","))
    for digits in sizes:
        for const in constants:
            for method in methods:
                if method not in AVAILABLE.get(const, ["theta", "zeta", "em"]):
                    continue
                limit = limits.get(method, 0)
                if (const, method) == ("vortex", "em"):
                    limit = min(limit, args.max_em_vortex)
                if digits > limit:
                    continue
                key = (const, method, digits)
                if key in recs and not args.force and recs[key].get("status") == "ok":
                    continue
                print("%s, %s, %d digits" % (const, method, digits), flush=True)
                rec = run_one(args, const, method, digits)
                recs[key] = rec
                with open(runs_path, "a") as f:
                    f.write(json.dumps(rec) + "\n")
                if rec.get("status") == "ok":
                    print("    %s: cpu %.2f s, wall %.2f s, peak %.0f MB" % (
                        rec["status"], rec["total_cpu"], rec["total_wall"], rec["peak_rss_kb"] / 1024.0), flush=True)
                else:
                    print("    %s" % rec.get("status"), flush=True)
                checks = cross_check(args, recs)
                agree, disagree = checks.get(key, ([], []))
                if disagree:
                    print("    MISMATCH with " + ", ".join(disagree), flush=True)
                elif agree:
                    print("    agrees with " + ", ".join(agree), flush=True)
                write_summary(args, recs, checks)
    checks = cross_check(args, recs)
    write_summary(args, recs, checks)
    bad = [k for k, (a, d) in checks.items() if d]
    print("done; %d runs, %d with mismatches; see %s" % (len(recs), len(bad), os.path.join(args.results, "summary.md")))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
