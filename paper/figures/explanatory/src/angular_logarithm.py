"""The angular logarithm, seed 522000. Reads data/angular-means.npz and the signs in numerics/publication/matching.npz. Writes ../angular-logarithm.pdf."""
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE.parent
# Angular-logarithm figure, seed 522000.
import numpy as np
from paperstyle import *
setup()
import matplotlib.pyplot as plt, cmocean
from matplotlib.gridspec import GridSpec
g = np.euler_gamma
eps = np.load(ROOT / 'numerics/publication/matching.npz')['coefficients'].astype(float)
def logsig(N, x):
    return 0.5 * np.log(np.sum((1 + x / N) ** (2 * np.arange(N + 1))))
def values(N, x, M):
    '''f_N(r e^{-2 pi i j / M}) for r = 1 + x/N, by one FFT.'''
    return np.fft.fft(eps[:N + 1] * (1 + x / N) ** np.arange(N + 1), M)
# panel a, a window near pi/3 at N = 1000
N = 1000; M = 2 ** 16; xs = np.linspace(-6, 6, 241)
th = 2 * np.pi * np.arange(M) / M; w = np.abs(N * (th - np.pi / 3)) <= 120
heat = np.array([np.log(np.abs(np.conj(values(N, x, M))[w])) - logsig(N, x) for x in xs])
u = N * (th[w] - np.pi / 3)
# panel b, all angles on the unit circle at N = 1e5
y = np.log(np.abs(values(100000, 0.0, 2 ** 21))) - logsig(100000, 0.0)
hist, be = np.histogram(y, bins=np.linspace(-7, 2.5, 191), density=True)
# panel c, angular means from the roots (data/angular-means.npz)
A = np.load(HERE / 'data/angular-means.npz')
D = {'be': be, 'hist': hist, 'xc': A['xc'], 'd3': A['d1000'], 'd4': A['d10000'], 'x5': A['xc'], 'd5': A['d100000']}
fig = plt.figure(figsize=(5.8, 4.3))
gs = GridSpec(2, 2, height_ratios=[1.0, 1.0], width_ratios=[1, 1], hspace=0.62, wspace=0.3,
              left=0.085, right=0.975, bottom=0.105, top=0.93)
a = fig.add_subplot(gs[0, :]); b = fig.add_subplot(gs[1, 0]); c = fig.add_subplot(gs[1, 1])
cm = cmocean.cm.thermal
im = a.imshow(heat, extent=[u[0], u[-1], xs[0], xs[-1]], origin='lower', aspect='auto', cmap=cm, vmin=-4.5, vmax=1.0,
              interpolation='bilinear', rasterized=True)
a.axhline(0, color='white', lw=0.8, alpha=0.9)
a.set_xlabel(r'$N(\theta-\pi/3)$', labelpad=2); a.set_ylabel(r'$x=N(r-1)$', labelpad=2)
a.set_yticks([-6, -3, 0, 3, 6]); a.set_xticks([-120, -80, -40, 0, 40, 80, 120])
for s in a.spines.values(): s.set_visible(False)
title(a, 'a', r'$\log|X_r(\theta)|$ with $X_r=f_N(re^{i\theta})/\sigma_N(r)$ and $N=1000$')
pos = a.get_position()
cax = fig.add_axes([pos.x1 - 0.17, pos.y1 + 0.016, 0.17, 0.013])
cb = fig.colorbar(im, cax=cax, orientation='horizontal', ticks=[-4, -2, 0])
cb.outline.set_visible(False); cax.tick_params(labelsize=7.5, length=2, pad=1)
cax.xaxis.set_ticks_position('top')
# b, distribution over the circle
be, hist = D['be'], D['hist']; yc = 0.5 * (be[1:] + be[:-1])
b.fill_between(yc, hist, step='mid', color=PURPLE_TINT, lw=0)
b.step(yc, hist, where='mid', color=PURPLE, lw=0.8, label=r'$N=10^5$, all $\theta$')
yy = np.linspace(-7, 2.5, 600); b.plot(yy, 2 * np.exp(2 * yy - np.exp(2 * yy)), color=INK, lw=LW_THEORY, label=r'law of $\log|G|$')
b.axvline(-g / 2, color=INK, lw=0.6, ls=(0, (2.5, 2)))
b.text(-g / 2 - 0.12, 0.97, r'$-\gamma/2$', transform=b.get_xaxis_transform(), fontsize=8.5, va='top', ha='right')
b.set_xlim(-6.5, 2.2); b.set_ylim(0, 0.86); b.set_xlabel(r'$\log|X_1(\theta)|$'); b.set_yticks([0, 0.2, 0.4, 0.6, 0.8])
b.legend(loc='upper left', handlelength=1.2, borderaxespad=0.1, labelspacing=0.3)
title(b, 'b', 'values along the unit circle')
# c, the angular mean across radii
RAMP = {3: '#e97356', 4: '#a42662', 5: '#3f1349'}
c.axhline(0, color=MUTED, lw=0.6)
c.plot(D['xc'], D['d3'], color=RAMP[3], lw=LW_DATA, label=r'$N=10^3$')
c.plot(D['xc'], D['d4'], color=RAMP[4], lw=LW_DATA, label=r'$N=10^4$')
c.plot(D['x5'], D['d5'], color=RAMP[5], lw=LW_DATA, label=r'$N=10^5$')
c.set_xlim(-6, 6); c.set_xticks([-6, -3, 0, 3, 6]); c.set_xlabel(r'$x=N(r-1)$')
c.set_ylim(-0.02, 0.02); c.set_yticks([-0.02, -0.01, 0, 0.01, 0.02]); c.set_yticklabels([r'$-0.02$', r'$-0.01$', r'$0$', r'$0.01$', r'$0.02$'])
c.legend(loc='upper left', handlelength=1.2, borderaxespad=0.1, labelspacing=0.3, ncol=3, columnspacing=0.9)
title(c, 'c', r'$J_N(r)-\log\sigma_N(r)+\gamma/2$')
fig.savefig(OUT / 'angular-logarithm.pdf', dpi=400); print('ok')
