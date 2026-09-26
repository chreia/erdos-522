#!/usr/bin/env python3
"""Reproduce the sequence-bootstrap tables, plotted data and metadata.

The run needs only data/sequence-statistics.npz.
"""
from __future__ import annotations
import csv, json, platform
from importlib.metadata import version
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
DATA = HERE / 'data'
NS = np.array([1000, 3000, 10000, 30000, 100000])
KS = np.array([2, 4, 8, 16, 32])
LS = np.array([2, 4, 8, 16])
LE = np.array([16, 32, 64, 128])
TS = np.array([.25, .5, 1., 2.])
XS = np.array([0, -2, 2, -4, 4, -8, 8, -16, 16, -32, 32])
GRID = np.linspace(-16, 16, 321)
SEEDS = np.arange(522000, 522100)
BOOTSTRAPS = 2000
BOOTSTRAP_SEED = 522987


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True, allow_nan=False) + '\n')


def write_csv(path, rows):
    with path.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def phi(x):
    x = np.asarray(x, dtype=float)
    out = np.empty_like(x)
    small = np.abs(x) < .01
    t = x[small]
    out[small] = .5 + t / 6 - t**3 / 90 + t**5 / 945
    t = x[~small]
    out[~small] = -1 / np.expm1(-2*t) - 1 / (2*t)
    return out


def bootstrap_weights(n, group):
    rng = np.random.default_rng(np.random.SeedSequence([BOOTSTRAP_SEED, group]))
    return rng.multinomial(n, np.full(n, 1/n), BOOTSTRAPS).astype(float)/n


def summarize(a, weights, variance=False):
    shape = a.shape[1:]
    flat = a.reshape(len(a), -1)
    boot = weights @ flat
    if variance:
        boot = np.maximum(0., weights @ (flat**2)-boot**2)*len(a)/(len(a)-1)
        point = np.var(a, axis=0, ddof=1)
    else:
        point = a.mean(axis=0)
    boot = boot.reshape((BOOTSTRAPS,)+shape)
    lo, hi = np.quantile(boot, [.025, .975], axis=0)
    return point, lo, hi, boot


def fit_slope(x, y, bootstrap, note=''):
    dx = np.log(x)-np.log(x).mean()
    good = np.all(np.isfinite(bootstrap) & (bootstrap > 0), axis=-1)
    slopes = np.log(bootstrap[good]) @ dx / (dx @ dx)
    point = float(np.log(y) @ dx / (dx @ dx))
    ci = np.quantile(slopes, [.025, .975]).tolist()
    return {'slope': point, 'lower': ci[0], 'upper': ci[1],
        'bootstrap_draws': BOOTSTRAPS, 'retained_draws': int(good.sum()),
        'zero_or_nonfinite_omissions': int((~good).sum()),
        'interval_conditional_on_positive_statistics': bool((~good).any()), 'note': note}


def prepare():
    d = np.load(DATA / 'sequence-statistics.npz')
    common = np.isfinite(d['base_closed']).all(axis=1)
    endpoint = np.isfinite(d['endpoint_change'][:, 1:]).all(axis=1)
    full = np.isfinite(d['fullblock_max'])
    root_seeds = d['seeds'][common].tolist()
    assert len(root_seeds) == 77
    W = bootstrap_weights(sum(common), 1)
    WF = bootstrap_weights(100, 2)
    WE = bootstrap_weights(sum(endpoint), 3)
    WB = bootstrap_weights(sum(full), 4)
    rows = []
    p, lo, hi, boot = summarize(d['profile'][common], W)
    for ni, N in enumerate(NS):
        for xi, x in enumerate(GRID):
            rows.append(dict(N=int(N), x=x, mean=p[ni,xi], lower=lo[ni,xi], upper=hi[ni,xi], limit=float(phi(x)), samples=len(root_seeds)))
    write_csv(DATA / 'radial-profile.csv', rows)
    rows = []
    p, lo, hi, boot = summarize(d['outside'][common], W)
    for ni, N in enumerate(NS):
        for ki, K in enumerate(KS):
            rows.append(dict(N=int(N), K=int(K), mean=p[ni,ki], lower=lo[ni,ki], upper=hi[ni,ki], limit=float(1/K-2/np.expm1(2*K)), bound=float(2*np.log(2)/K), samples=len(root_seeds)))
    write_csv(DATA / 'annulus.csv', rows)
    rows, fits = [], {}
    for scope, key in [('annular', 'bad_annular'), ('global', 'bad_global')]:
        p, lo, hi, boot = summarize(d[key][common], W)
        for ni, N in enumerate(NS):
            fits[f'{scope}_L_N{N}'] = fit_slope(LS, p[ni], boot[:,ni], 'Primary L=2,4,8,16, no angular excision; all five degrees use the same 77 sequences.')
            for li, L in enumerate(LS):
                rows.append(dict(scope=scope, N=int(N), L=int(L), mean=p[ni,li], lower=lo[ni,li], upper=hi[ni,li], samples=len(root_seeds)))
        for li, L in enumerate(LS):
            fits[f'{scope}_N_L{L}'] = fit_slope(NS, p[:,li], boot[:,:,li])
    write_csv(DATA / 'small-derivative.csv', rows)
    p, lo, hi, boot = summarize(d['bad_extended_excised'][common,-1], W)
    fits['supplementary_L_16_128_N100000'] = fit_slope(LE,p,boot,'Supplementary only: K=2 annulus, excises distance <=N^-1/2 from 0 or pi. Intervals may omit zero-count bootstrap draws. Not the primary L=2,4,8,16 fit.')
    write_csv(DATA / 'small-derivative-supplement.csv', [dict(L=int(L),mean=p[j],lower=lo[j],upper=hi[j]) for j,L in enumerate(LE)])
    mean_rows=[]
    log_mean_rows=[]
    for gi, grid in enumerate(['coarse','dense']):
        p,lo,hi,_=summarize(d['fft_occupation'][:,:,0,:,gi],WF)
        for ni,N in enumerate(NS):
            for ti,t in enumerate(TS):
                mean_rows.append(dict(grid=grid,N=int(N),t=t,mean=p[ni,ti],lower=lo[ni,ti],upper=hi[ni,ti],gaussian=1-np.exp(-t*t),samples=100))
        p,lo,hi,_=summarize(d['fft_log'][:,:,:,gi],WF)
        for ni,N in enumerate(NS):
            for xi,x in enumerate(XS):
                log_mean_rows.append(dict(grid=grid,N=int(N),x=int(x),mean=p[ni,xi],lower=lo[ni,xi],upper=hi[ni,xi],samples=100))
    write_csv(DATA/'occupation-means.csv',mean_rows)
    write_csv(DATA/'logarithmic-means.csv',log_mean_rows)
    rows = []
    for gi, grid in enumerate(['coarse','dense']):
        p,lo,hi,boot = summarize(d['fft_occupation'][:,:,0,:,gi], WF, variance=True)
        for ti,t in enumerate(TS):
            fits[f'occupation_variance_{grid}_t{t:g}'] = fit_slope(NS,p[:,ti],boot[:,:,ti])
            for ni,N in enumerate(NS):
                rows.append(dict(kind='occupation_variance', grid=grid, parameter=t, N=int(N),mean=p[ni,ti],lower=lo[ni,ti],upper=hi[ni,ti],samples=100))
        for xi,x in enumerate(XS):
            p,lo,hi,boot = summarize(d['fft_log'][:,:,xi,gi]**2, WF)
            fits[f'log_mean_square_{grid}_x{x}'] = fit_slope(NS,p,boot)
            for ni,N in enumerate(NS):
                rows.append(dict(kind='log_mean_square',grid=grid,parameter=int(x),N=int(N),mean=p[ni],lower=lo[ni],upper=hi[ni],samples=100))
    for name,key in [('endpoint','endpoint_change'),('endpoint_centered','endpoint_centered')]:
        p,lo,hi,boot = summarize(d[key][endpoint,1:], WE)
        fits[name] = fit_slope(NS[1:],p,boot,'Four larger-degree endpoints only, common complete sequences. This is not a full-block maximum; uncentered changes include degree drift.')
        for ni,N in enumerate(NS[1:]):
            rows.append(dict(kind=name,grid='none',parameter=0,N=int(N),mean=p[ni],lower=lo[ni],upper=hi[ni],samples=int(sum(endpoint))))
    for name,key in [('fullblock_max','fullblock_max'),('fullblock_centered_max','fullblock_centered_max')]:
        p,lo,hi,_=summarize(d[key][full,None],WB)
        rows.append(dict(kind=name,grid='none',parameter=0,N=1000,mean=p[0],lower=lo[0],upper=hi[0],samples=int(sum(full))))
    write_csv(DATA / 'diagnostic-scaling.csv', rows)
    rows=[]
    p,lo,hi,_=summarize(d['blob_radius_N'][common],W)
    for ni,N in enumerate(NS):
        for li,L in enumerate(LS):
            mask=np.isfinite(d['blob_perturbed_fraction'][:,ni,li])
            rows.append(dict(N=int(N),L=int(L),mean_radius_N=p[ni,li],lower_radius_N=lo[ni,li],upper_radius_N=hi[ni,li],radius_samples=77,
                base_single_root_fraction=float(np.mean(d['blob_base_fraction'][common,ni,li])),
                perturbed_single_root_fraction=float(np.mean(d['blob_perturbed_fraction'][mask,ni,li])),
                extraL_single_root_fraction=float(np.mean(d['blob_extraL_fraction'][mask,ni,li])),perturbed_samples=int(sum(mask))))
    write_csv(DATA / 'blob.csv', rows)
    write_json(DATA / 'bootstrap-fits.json', fits)
    degree_coverage=[]
    for ni,N in enumerate(NS):
        valid=np.isfinite(d['base_closed'][:,ni])
        degree_coverage.append({'N':int(N),'root_samples':int(valid.sum()),'root_seeds':d['seeds'][valid].tolist(),
            'max_normalized_residual':float(np.nanmax(d['base_residual'][:,ni])),
            'unresolved_boundary_band_total':int(np.nansum(d['base_unresolved'][:,ni])),
            'common_cohort_closed_fraction_sensitivity':{
                'lower':float(np.mean(d['base_lower'][common,ni]/N)),
                'upper':float(np.mean(d['base_upper'][common,ni]/N)),
                'nominal':float(np.mean(d['base_closed'][common,ni]/N))},
            'endpoint_samples':int(np.isfinite(d['endpoint_change'][:,ni]).sum())})
    metadata={'schema_version':1,'coefficient_generator':'NumPy Generator(PCG64(seed)).choice(np.array([-1,1], dtype=np.int8), 125001); every degree uses the same sequence prefix','bootstrap':{'seed':BOOTSTRAP_SEED,'draws':BOOTSTRAPS,'unit':'whole coefficient sequence, jointly across all degrees and thresholds in each cohort','interval':'pointwise percentile 95%, not simultaneous; zero omissions reported individually in bootstrap-fits.json','streams':{'1':'77 common root sequences','2':'100 FFT sequences','3':'common larger-degree endpoint sequences','4':'78 complete degree-1000 blocks'}},
        'cohorts':{'common_root_seeds':root_seeds,'fft_seeds':SEEDS.tolist(),'common_endpoint_seeds':d['seeds'][endpoint].tolist(),'fullblock_seeds':d['seeds'][full].tolist()},
        'degree_coverage':degree_coverage,
        'normalizations':{'radial_coordinate':'N*(|z|-1), exact +/-1 roots forced to radius 1 for counts only','derivative':'log|f_N\'(alpha)| - (3/2)log N','annular_derivative':'| |alpha|-1 | <=2/N, includes real-axis sectors','occupation':'angular mean of 1{|f/σ|<=t}, angular Haar mass 1','log_center':'J_N(r)-log σ_N(r)+EulerGamma/2; finite FFT quadrature'},
        'fft':{'samples':100,'grid_multipliers':[16,32],'stored_radii_x':XS.tolist(),
            'max_log_grid_change_by_degree':np.max(np.abs(d['fft_log'][:,:,:,1]-d['fft_log'][:,:,:,0]),axis=(0,2)).tolist(),
            'max_occupation_grid_change_by_degree':np.max(np.abs(d['fft_occupation'][:,:,:,:,1]-d['fft_occupation'][:,:,:,:,0]),axis=(0,2,3)).tolist()},
        'blob':{'K0':2,'m':'floor(N^(7/8))','a':'15 exp(4) sqrt(m log N)','radius':'2a/|f_N\'(alpha)|','extraL_radius':'2aL/|f_N\'(alpha)|','good_roots':'K=2 annulus, |f_N\'|/N^(3/2)>=1/L','all_measured_single_root_fractions_zero':True,'scope':'78 complete small blocks, eight snapshot fractions averaged within each sequence; larger degrees endpoint only, counts 58, 57, 53, 27. Radius means use the common 77 base sequences.','relation_to_proof':'The recorded K0=2 is below the containment choice Kprime>=K+2=4 for K=2. Raising K0 to 4 enlarges a and all radii by exp(4). Finite data do not exhibit the asymptotic small-blob regime.'},
        'matching':{'source':'matching.npz','metadata':'matching.json','interpretation':'Independent minimum-total-Euclidean-distance injections from degree 1000 to 1210 and 1421. Empirical assignments, not certified analytic root continuation.'},
        'boundary':'Known exact +/-1 multiplicities included in closed-disk counts. Other roots within 1e-9 of modulus 1 remain numerically ambiguous. Sensitivity intervals are not certified enclosures and are separate from bootstrap intervals.',
        'residual_definition':'|f_N(z)| / sum_{k=0}^N |z|^k','versions':{'Python':platform.python_version(),'NumPy':np.__version__,'Matplotlib':version('matplotlib')},
        'limitations':['The computations are finite numerical evidence, not proof inputs.','Five-degree fits use 77 complete root sequences.','Only degree 1000 has complete block maxima. Larger-degree values are endpoint changes.','Primary small-derivative L=2,4,8,16 slopes are not an asymptotic L^-4 regime.','FFT doubling measures sensitivity, not certified integration error.']}
    metadata['figures']={
        'radial-profile':{'data':['data/radial-profile.csv','data/sequence-statistics.npz'],'cohort':'common_root_seeds','bands':'pointwise 95% bootstrap in panels a and b only','single_sequence_panel':{'seed':522000,'degrees':d['N'].tolist(),'scaled_radii':321,'window':[-16,16],'quantity':'empirical radial profile minus Phi'}},
        'annulus':{'data':['data/annulus.csv'],'cohort':'common_root_seeds'},
        'small-derivative':{'data':['data/small-derivative.csv'],'cohort':'common_root_seeds'},
        'root-matching':{'data':['matching.npz','matching.json'],'seed':522000,'degrees':[1000,1210,1421],'displayed_links':'Independent base-to-final minimum-distance assignment only. Middle-degree roots shown without trajectory lines.','count_panel':'nu_(1000+m)(1)-nu_1000(1)-m/2 at all 422 degrees, 0<=m<=421'}}
    metadata['section_10_diagnostics']={'data':['data/diagnostic-scaling.csv','data/occupation-means.csv','data/logarithmic-means.csv','data/blob.csv'],'cohorts':['fft_seeds','common_endpoint_seeds','fullblock_seeds','common_root_seeds'],'blob_aggregation':'Mean across sequences of the median radius among that sequence’s good annular roots.'}
    write_json(HERE/'metadata.json',metadata)
    print(json.dumps({'root_counts':[v['root_samples'] for v in degree_coverage],'common_roots':sum(common).item(),'fft':100,'common_endpoints':sum(endpoint).item(),'fullblocks':sum(full).item(),'primary_derivative_fit':fits['annular_L_N100000'],'endpoint_fit':fits['endpoint'],'occupation_t1_fit':fits['occupation_variance_dense_t1'],'log_fit':fits['log_mean_square_dense_x0']},indent=2))


if __name__=='__main__':
    prepare()
