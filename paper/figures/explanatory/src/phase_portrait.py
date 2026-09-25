"""Phase portrait of f_1000 near exp(i pi/3), seed 522000. Writes ../phase-portrait.pdf."""
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE.parent
# Phase portrait of f_N near exp(i pi/3), N = 1000, seed 522000.
import numpy as np
from paperstyle import *
setup()
import matplotlib.pyplot as plt, cmocean
eps = np.load(ROOT / 'numerics/publication/matching.npz')['coefficients'].astype(float)
N, th0 = 1000, np.pi / 3
Ua = np.linspace(-36, 36, 2161); Va = np.linspace(-12, 12, 721)
Za = (1 + Va[:, None] / N) * np.exp(1j * (th0 + Ua[None, :] / N))
fa = np.full(Za.shape, eps[N], dtype=complex)
for k in range(N - 1, -1, -1):
    fa = fa * Za + eps[k]

# ---------- panel a image
rr = 1 + Va / N
sig = np.sqrt((rr ** (2 * (N + 1)) - 1) / (rr ** 2 - 1 + (np.abs(Va) < 1e-12)) * (np.abs(Va) >= 1e-12) + (N + 1) * (np.abs(Va) < 1e-12))[:, None]
arg = (np.angle(fa) + np.pi) / (2 * np.pi)
lm = np.log2(np.abs(fa) / sig)
cmap = cmocean.cm.phase
img = np.clip(cmap(arg)[..., :3] * (0.70 + 0.30 * (lm - np.floor(lm)))[..., None], 0, 1)

# ---------- figure
plt.rcParams.update({'axes.labelsize': 9.5, 'xtick.labelsize': 8.5, 'ytick.labelsize': 8.5})
W = 5.8; x0, wax = 0.085, 0.895
ha = wax * W * (2 * 12) / 72
top, bot = 0.40, 0.44
H = top + ha + bot
fig = plt.figure(figsize=(W, H))
axa = fig.add_axes([x0, bot / H, wax, ha / H])

axa.imshow(img, extent=[Ua[0], Ua[-1], Va[0], Va[-1]], origin='lower', aspect='equal', interpolation='lanczos', rasterized=True)
axa.axhline(0, color='white', lw=1.1)
axa.set_ylabel(r'$N(|z|-1)$', labelpad=2)
axa.set_yticks([-10, -5, 0, 5, 10]); axa.set_xticks([-30, -20, -10, 0, 10, 20, 30])
axa.tick_params(length=2.5)
axa.set_xlabel(r'$N(\arg z-\pi/3)$', labelpad=2)
for s in axa.spines.values(): s.set_visible(False)
axa.text(0, 1.045, r'Phase of $f_{%d}$ near $e^{i\pi/3}$, brightness steps where $|f_{%d}|/\sigma_{%d}$ doubles' % (N, N, N), transform=axa.transAxes, fontsize=9.5, va='bottom', ha='left')
kx = fig.add_axes([0.925, (bot + ha + 0.03) / H, 0.055, 0.33 / H], projection='polar')
th = np.linspace(-np.pi, np.pi, 361); T, RR = np.meshgrid(th, np.array([0.62, 1.0]))
kx.pcolormesh(T, RR, (T[:-1, :-1] + np.pi) / (2 * np.pi), cmap=cmap, shading='flat', rasterized=True)
kx.set_ylim(0, 1); kx.set_axis_off()

fig.savefig(OUT / 'phase-portrait.pdf', dpi=400)
print('H', round(H, 2))
