import numpy as np, math
gm = np.load('/tmp/claude-0/kcf/gm.npy'); N = len(gm)
K = 2.68545200106530644530971483548179569382038229399446
idx = np.unique(np.round(np.geomspace(1, N, 1400)).astype(np.int64)) - 1
idx = np.unique(np.concatenate([idx, [N - 1]]))
with open('/home/claude/khafe/paper/khcf_gm.dat', 'w') as f:
    f.write('n gm z\n')
    for i in idx:
        n = i + 1
        f.write('%d %.6f %.4f\n' % (n, gm[i], math.sqrt(n) * (math.log(gm[i]) - math.log(K))))
print(len(idx))
