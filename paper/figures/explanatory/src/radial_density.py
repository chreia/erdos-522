"""Root density at the critical scale, 77 polynomials with random signs at N = 1e5.
Reads data/polar-hist.npz. Writes ../radial-density.pdf."""
from pathlib import Path
HERE = Path(__file__).resolve().parent
OUT = HERE.parent
import numpy as np
from paperstyle import *
setup()
import matplotlib.pyplot as plt, matplotlib.colors as mcolors, cmocean
from scipy.ndimage import gaussian_filter

def Phi_prime(x):
    x = np.asarray(x, float); out = np.full_like(x, 1 / 6); nz = np.abs(x) > 1e-4
    out[nz] = 0.5 * (x[nz] ** -2 - np.sinh(x[nz]) ** -2)
    return out

FG2 = '#52514e'
D = np.load(HERE / 'data/polar-hist.npz')
H0, xe0, tot = D['H'], D['x_edges'], int(D['roots']); nseq = len(D['sequences'])
# coarser bins, 360 angles by 160 radii, then light smoothing
H = H0.reshape(360, 4, 160, 2).sum((1, 3))
te = np.linspace(-np.pi, np.pi, 361); xe = xe0[::2]
dth = 1 / 360; dx = np.diff(xe)[0]
dens = gaussian_filter(H / (tot * dth * dx), sigma=(1.0, 0.6), mode=('wrap', 'nearest'))
cmap = cmocean.cm.thermal
norm = mcolors.PowerNorm(0.5, vmin=0, vmax=0.17, clip=True)
def shade(d):
    """thermal colours, faded into the white page where the density is small"""
    rgb = cmap(norm(d))[..., :3]
    a = np.clip((d - 0.008) / (0.04 - 0.008), 0, 1)
    return np.clip(rgb * a[..., None] + (1 - a[..., None]), 0, 1)
R0 = 11.0; T, X = np.meshgrid(te, xe, indexing='ij')
fig = plt.figure(figsize=(5.8, 3.3))
ax = fig.add_axes([0.01, 0.07, 0.56, 0.86], projection='polar')
ax.pcolormesh(T, R0 + X, shade(dens), shading='flat', rasterized=True)
th = np.linspace(0, 2 * np.pi, 721); ax.plot(th, np.full_like(th, R0), color='white', lw=0.6, alpha=0.9)
ax.set_ylim(0, R0 + 8.6); ax.set_axis_off()
a = np.pi / 2
ax.plot([a, a], [R0 - 8, R0 + 8], color=FG2, lw=0.55, solid_capstyle='butt')
for xv in (-8, -4, 0, 4, 8):
    rho = R0 + xv; d = (0.30 if xv in (-8, 0, 8) else 0.18) / rho
    ax.plot([a - d, a + d], [rho, rho], color=FG2, lw=0.55)
ax.text(a, R0 + 8.35, r'$x=8$', ha='center', va='bottom', fontsize=7.8, color=INK)
ax.text(a, R0 - 9.0, r'$x=-8$', ha='center', va='top', fontsize=7.8, color=INK)
ax.annotate(r'$|z|=1$', xy=(np.deg2rad(135), R0), xytext=(np.deg2rad(137), R0 + 10.6), textcoords='data',
            fontsize=8.5, color=INK, ha='right', va='bottom', annotation_clip=False,
            arrowprops=dict(arrowstyle='-', color=FG2, lw=0.45, shrinkA=1, shrinkB=0))
ax2 = fig.add_axes([0.665, 0.19, 0.305, 0.56])
BLUE = '#2f6db5'
e4 = xe0[::8]; mid = (e4[:-1] + e4[1:]) / 2                     # 40 bins of width 0.4
avg = H0.sum(0).reshape(40, 8).sum(1) / (tot * np.diff(e4))
xx = np.linspace(-8, 8, 400)
ax2.semilogy(xx, Phi_prime(xx), color=INK, lw=1.2, zorder=2, label=r"$\Phi'(x)$")
ax2.semilogy(mid, avg, 'o', ms=3.4, color=BLUE, mec='white', mew=0.4, zorder=3, label='roots')
ax2.set_xlim(-8, 8); ax2.set_ylim(0.005, 0.3); ax2.set_xticks([-8, -4, 0, 4, 8])
ax2.set_xlabel(r'$x=N(|z|-1)$'); ax2.set_ylabel('density')
h, l = ax2.get_legend_handles_labels()
ax2.legend(h[::-1], l[::-1], loc='lower center', fontsize=8.5, handlelength=1.2, ncol=2, bbox_to_anchor=(0.5, 1.0), borderaxespad=0.3)
# colour key drawn with the same fade
cax = fig.add_axes([0.665, 0.895, 0.305, 0.022])
g = np.linspace(0, 0.17, 400)
cax.imshow(shade(g)[None, :, :], extent=[0, 0.17, 0, 1], aspect='auto', interpolation='bilinear')
cax.set_yticks([]); cax.set_xticks([0, 0.05, 0.1, 0.15], ['0', '0.05', '0.1', '0.15'])
cax.tick_params(labelsize=7.5, length=2, colors=INK); [s.set_visible(False) for s in cax.spines.values()]
cax.set_title('root density', fontsize=8.5, color=INK, pad=3)
fig.text(0.29, 0.012, r'$%.1f\times10^{6}$ roots of %d polynomials with random signs, $N=10^{5}$' % (tot / 1e6, nseq),
         ha='center', va='bottom', fontsize=8.5, color=INK)
fig.savefig(OUT / 'radial-density.pdf', dpi=400)
print('ok')
