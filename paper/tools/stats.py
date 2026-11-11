import numpy as np, sys, math
a = np.loadtxt(sys.argv[1], dtype=np.int64)
np.save('/tmp/claude-0/kcf/a.npy', a)
K = 2.68545200106530644530971483548179569382038229399446
N = len(a) - 1
print("terms a_0..a_N, N =", N, "a_0 =", a[0])
b = a[1:].astype(np.float64)
lg = np.log(b)
S = np.cumsum(lg)
n = np.arange(1, N + 1, dtype=np.float64)
gm = np.exp(S / n)
print("GM_N =", repr(gm[-1]), "GM_N - K =", gm[-1] - K, "rel", (gm[-1] - K) / K)
print("max a_k =", a[1:].max(), "at k =", int(np.argmax(a[1:])) + 1)
for v in [1, 2, 3]:
    print("freq of", v, (b == v).mean(), "Gauss-Kuzmin", -math.log2(1 - 1 / (v + 1) ** 2))
# Levy: log q_n via ratios r_n = q_n/q_{n-1} = a_n + 1/r_{n-1}
r = 1e300; lq = 0.0; lqs = np.empty(N)
inv = 0.0
for i in range(N):
    rr = b[i] + inv
    lq += math.log(rr); lqs[i] = lq; inv = 1.0 / rr
print("log10 q_N ~", lq / math.log(10), " Levy (1/N) log q_N =", lq / N, " pi^2/(12 log 2) =", math.pi ** 2 / (12 * math.log(2)))
print("Lochs: N / D =", N / 1e7, " 6 log2 log10 / pi^2 =", 6 * math.log(2) * math.log(10) / math.pi ** 2)
# CLT scale: batch means of log a
L = 10000; B = N // L
bm = lg[:B * L].reshape(B, L).mean(axis=1)
sig2 = bm.var(ddof=1) * L
print("log K =", math.log(K), "mean log a =", lg.mean(), "batch-means sigma_inf^2 =", sig2, "plain var =", lg.var())
z = np.sqrt(n) * (np.log(gm) - math.log(K))
sel = n >= 1000
print("sqrt(n)(log GM_n - log K): max abs for n>=1000:", np.abs(z[sel]).max(), " at n =", int(n[sel][np.argmax(np.abs(z[sel]))]))
print("final z =", z[-1], " z / sigma =", z[-1] / math.sqrt(sig2))
np.save('/tmp/claude-0/kcf/gm.npy', gm)
np.save('/tmp/claude-0/kcf/lq.npy', lqs)
