#!/usr/bin/env python3
"""Render the four numerical figures of the paper from the committed plotted data."""
from __future__ import annotations
import csv, hashlib, json, re
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection

HERE=Path(__file__).resolve().parent
DATA=HERE/'data'
OUT=HERE/'figures'
OUT.mkdir(exist_ok=True)
COLORS=['#225C8B','#35917F','#B47B2B','#85649C','#777777']
BLUE,TEAL,AMBER,PURPLE,GREY=COLORS
# Okabe-Ito blue and its tints and shades, as in the tilted-mean figure (oiblue, oiblue!45).
OI_BLUE='#0072B2';OI_BLUE_TINT='#8CC0DC'
OI_BLUES=['#003F62',OI_BLUE,'#4D9CC9',OI_BLUE_TINT]
plt.rcParams.update({'font.family':'STIXGeneral','mathtext.fontset':'stix','font.size':10,
    'axes.labelsize':10,'axes.titlesize':10,'xtick.labelsize':9,'ytick.labelsize':9,
    'legend.fontsize':9,'legend.title_fontsize':9,'axes.spines.top':False,'axes.spines.right':False,
    'axes.linewidth':.6,'axes.edgecolor':'#555555','xtick.major.width':.6,'ytick.major.width':.6,
    'xtick.minor.width':.4,'ytick.minor.width':.4,'lines.linewidth':1.4,
    'pdf.fonttype':42,'ps.fonttype':42,'svg.fonttype':'path','svg.hashsalt':'erdos522-publication-v1',
    'savefig.facecolor':'white','figure.facecolor':'white', 'savefig.bbox':None})

FIGURE_WIDTH_INCHES=5.8
RENDERED={}


def table(name):
    with (DATA/(name+'.csv')).open() as f:
        out=[]
        for row in csv.DictReader(f):
            for key,v in row.items():
                try: row[key]=float(v)
                except ValueError: pass
            out.append(row)
        return out


def select(rows,**kwargs):
    return [r for r in rows if all(r[k]==v for k,v in kwargs.items())]


def vals(rows,key): return np.array([r[key] for r in rows])


def panel(ax,letter,title):
    ax.set_title(r'$\mathbf{' + letter + '}$  ' + title,loc='left',pad=9)


def grid(ax):
    ax.set_axisbelow(True)
    ax.grid(axis='y',which='major',color='#dddddd',linewidth=.45)


def ribbon(ax,rows,x,color,label=None,scale=1.,marker=None):
    xx=vals(rows,x); p=vals(rows,'mean')*scale
    ax.fill_between(xx,vals(rows,'lower')*scale,vals(rows,'upper')*scale,color=color,alpha=.13,linewidth=0)
    ax.plot(xx,p,color=color,label=label,marker=marker,markersize=4,markeredgewidth=.5)


def save(fig,name):
    # The uncropped canvas is the final physical size at full manuscript width.
    assert fig.get_figwidth() == FIGURE_WIDTH_INCHES
    fig.canvas.draw()
    text_sizes=sorted({float(text.get_fontsize()) for text in fig.findobj(matplotlib.text.Text)
        if text.get_visible() and text.get_text()})
    assert all(9 <= size <= 10 for size in text_sizes), (name, text_sizes)
    RENDERED[name]={'width_inches':float(fig.get_figwidth()),
        'height_inches':float(fig.get_figheight()),'text_sizes_pt':text_sizes}
    fig.savefig(OUT/(name+'.pdf'),metadata={'Creator':'Erdos 522 publication renderer','CreationDate':None,'ModDate':None})
    svg_path=OUT/(name+'.svg')
    fig.savefig(svg_path,metadata={'Creator':'Erdos 522 publication renderer','Date':None})
    # Clip identifiers otherwise hash unrounded layout floats. Stable names
    # preserve the exact emitted geometry while removing invisible roundoff.
    svg=svg_path.read_text()
    for index,clip_id in enumerate(re.findall(r'<clipPath id="([^"]+)">',svg)):
        stable_id=f'clip{index}'
        svg=svg.replace(f'id="{clip_id}"',f'id="{stable_id}"')
        svg=svg.replace(f'url(#{clip_id})',f'url(#{stable_id})')
    svg_path.write_text(svg)
    plt.close(fig)
    print(name,flush=True)


FITS=json.loads((DATA/'bootstrap-fits.json').read_text())
META=json.loads((HERE/'metadata.json').read_text())
NS=[1000,3000,10000,30000,100000]
NLABEL=[r'$10^3$',r'$3\times10^3$',r'$10^4$',r'$3\times10^4$',r'$10^5$']


def radial_profile():
    rows=table('radial-profile')
    statistics=np.load(DATA/'sequence-statistics.npz')
    seed_index=int(np.flatnonzero(statistics['seeds']==522000)[0])
    assert np.array_equal(statistics['N'],NS)
    assert np.all(np.isfinite(statistics['profile'][seed_index]))
    fig,axes=plt.subplots(3,1,figsize=(FIGURE_WIDTH_INCHES,6.6),sharex=True,layout='constrained',
        gridspec_kw={'height_ratios':[1.3,1,1]})
    for j,N in enumerate(NS):
        rr=select(rows,N=N)
        ribbon(axes[0],rr,'x',COLORS[j],label=NLABEL[j])
        x=vals(rr,'x');target=vals(rr,'limit')
        axes[1].fill_between(x,vals(rr,'lower')-target,vals(rr,'upper')-target,color=COLORS[j],alpha=.12,linewidth=0)
        axes[1].plot(x,vals(rr,'mean')-target,color=COLORS[j],lw=1.)
        # These are the retained closed-count profiles of one fixed sequence,
        # sampled on the same grid. They are not bootstrap or mean curves.
        assert np.array_equal(statistics['profile_x'],x)
        axes[2].plot(x,statistics['profile'][seed_index,j]-target,color=COLORS[j],lw=1.)
    rr=select(rows,N=NS[-1]);axes[0].plot(vals(rr,'x'),vals(rr,'limit'),color='#202020',ls='--',lw=1.3,label=r'$\Phi(x)$')
    axes[0].set_ylabel(r'Mean $\nu_N(1+x/N)/N$');axes[0].set_ylim(0,1)
    axes[0].legend(ncol=3,frameon=False,loc='lower right',columnspacing=.75,handlelength=1.45)
    axes[1].axhline(0,color='#202020',ls='--',lw=.7)
    axes[1].set_ylabel(r'Mean minus $\Phi(x)$')
    axes[1].ticklabel_format(axis='y',style='sci',scilimits=(-2,2),useMathText=True)
    axes[1].set_xlim(-16,16)
    axes[2].axhline(0,color='#202020',ls='--',lw=.7)
    axes[2].set_xlabel(r'Scaled radius $x$')
    axes[2].set_ylabel(r'$\widehat\Phi_N(x)-\Phi(x)$')
    axes[2].ticklabel_format(axis='y',style='sci',scilimits=(-2,2),useMathText=True)
    panel(axes[0],'a','Mean empirical radial profile')
    panel(axes[1],'b','Mean finite-degree deviations')
    panel(axes[2],'c','One fixed nested sequence (seed 522000)')
    for ax in axes:grid(ax)
    save(fig,'radial-profile')


def annulus():
    rows=table('annulus')
    fig,axes=plt.subplots(1,2,figsize=(FIGURE_WIDTH_INCHES,3.2),layout='constrained')
    ax=axes[0];rr=select(rows,N=100000)
    ribbon(ax,rr,'K',BLUE,label=r'$N=10^5$',marker='o')
    ax.plot(vals(rr,'K'),vals(rr,'limit'),'--',color='#222222',label='Limiting profile')
    ax.plot(vals(rr,'K'),vals(rr,'bound'),':',color=AMBER,label=r'$2\log 2/K$')
    ax.set_xscale('log',base=2);ax.set_yscale('log');ax.set_xticks([2,4,8,16,32],['2','4','8','16','32'])
    ax.set_xlabel(r'Annulus width parameter $K$');ax.set_ylabel('Fraction outside annulus')
    ax.legend(frameon=False,loc='lower left');panel(ax,'a','Annular mass');grid(ax)
    ax=axes[1]
    for j,K in enumerate([2,4,8,16,32]):
        rr=select(rows,K=K);x=vals(rr,'N');lim=vals(rr,'limit')
        ax.fill_between(x,K*(vals(rr,'lower')-lim),K*(vals(rr,'upper')-lim),color=COLORS[j],alpha=.12,linewidth=0)
        ax.plot(x,K*(vals(rr,'mean')-lim),color=COLORS[j],marker='o',markersize=3,label=str(K))
    ax.axhline(0,color='#222222',ls='--',lw=.7)
    ax.set_xscale('log');ax.set_xlabel(r'Degree $N$');ax.set_ylabel(r'$K\,($mean minus limit$)$')
    ax.ticklabel_format(axis='y',style='sci',scilimits=(-2,2),useMathText=True)
    ax.legend(title=r'$K$',ncol=3,frameon=False,loc='lower right',columnspacing=.65,handlelength=1.)
    panel(ax,'b','Approach to the profile');grid(ax)
    save(fig,'annulus')


def small_derivative():
    rows=table('small-derivative')
    fig,axes=plt.subplots(1,2,figsize=(FIGURE_WIDTH_INCHES,3.3),layout='constrained')
    ax=axes[0]
    for scope,color,label in [('annular',OI_BLUE,r'$2/N$ annulus'),('global',OI_BLUE_TINT,'All roots')]:
        rr=select(rows,scope=scope,N=100000)
        ribbon(ax,rr,'L',color,label=label,scale=1/100000,marker='o')
    ls=np.array([2,4,8,16]);ax.plot(ls,ls.astype(float)**-4,'--',color='#333333',
        label=r'$L^{-4}$ reference')
    ax.set_xscale('log',base=2);ax.set_yscale('log');ax.set_xticks(ls,[str(L) for L in ls]);ax.set_ylim(8e-6,1.)
    ax.set_xlabel(r'Derivative threshold parameter $L$');ax.set_ylabel('Fraction with small derivative')
    ax.legend(frameon=False,loc='lower left',labelspacing=.3,fontsize=9)
    f=FITS['annular_L_N100000']
    ax.text(.98,.47,f"Annular slope {f['slope']:.2f}\n95% CI [{f['lower']:.2f}, {f['upper']:.2f}]",ha='right',va='top',transform=ax.transAxes,fontsize=9,
        bbox={'facecolor':'white','edgecolor':'none','alpha':.95,'pad':2})
    panel(ax,'a',r'Finite thresholds at $N=10^5$');grid(ax)
    ax=axes[1]
    for j,L in enumerate(ls):
        rr=select(rows,scope='annular',L=int(L));ribbon(ax,rr,'N',OI_BLUES[j],label=str(L),marker='o')
    ax.set_xscale('log');ax.set_yscale('log');ax.set_xlabel(r'Degree $N$');ax.set_ylabel(r'Small-derivative roots in $2/N$ annulus')
    ax.legend(title=r'$L$',ncol=2,frameon=False,loc='upper left',columnspacing=.9,handlelength=1.4)
    panel(ax,'b','Counts at fixed thresholds');grid(ax)
    save(fig,'small-derivative')


def root_matching():
    z=np.load(HERE/'matching.npz')
    fig,axes=plt.subplots(1,2,figsize=(FIGURE_WIDTH_INCHES,3.5),layout='constrained',gridspec_kw={'width_ratios':[1.03,1.]})
    ax=axes[0];theta=np.pi/3;rot=np.exp(-1j*theta);N=1000
    def coord(a):
        w=a*rot
        return np.column_stack([N*w.imag,N*(w.real-1)])
    p=coord(z['z1000']);end=coord(z['z1421']);mid=coord(z['z1210'])
    mask=(np.abs(p[:,0])<=24)&(np.abs(p[:,1])<=9)
    links=np.stack([p[mask],end[z['injection1421'][mask]]],axis=1)
    ax.add_collection(LineCollection(links,colors='#aaaaaa',linewidths=.7,zorder=1))
    tangent=np.linspace(-24,24,300)
    ax.plot(tangent,N*(np.sqrt(1-(tangent/N)**2)-1),color='#333333',lw=.65)
    ax.annotate(r'Unit circle $|z|=1$',xy=(-18,N*(np.sqrt(1-(-18/N)**2)-1)),
        xytext=(-22,5.8),arrowprops={'arrowstyle':'-','color':'#333333','lw':.7},
        fontsize=9.5,bbox={'facecolor':'white','edgecolor':'none','alpha':.9,'pad':1.5})
    for pp,color,mark,label in [(p,BLUE,'o','1000'),(mid,TEAL,'^','1210'),(end,AMBER,'s','1421')]:
        window=(np.abs(pp[:,0])<30)&(np.abs(pp[:,1])<15)
        ax.scatter(pp[window,0],pp[window,1],s=22,marker=mark,facecolor='white' if mark=='s' else color,edgecolor=color,linewidth=.7,label=label,zorder=2)
    ax.set_xlim(-24,24);ax.set_ylim(-9,9)
    ax.set_xlabel(r'$N\operatorname{Im}(z e^{-i\pi/3})$');ax.set_ylabel(r'$N(\operatorname{Re}(z e^{-i\pi/3})-1)$')
    ax.legend(title='Degree',ncol=3,frameon=False,loc='upper center',bbox_to_anchor=(.5,-.22),columnspacing=.6,handletextpad=.25)
    panel(ax,'a','Empirical root assignments');grid(ax)
    ax=axes[1];offset=z['block_degrees']-1000;low=z['block_closed_count_lower'];high=z['block_closed_count_upper']
    # The two nonsingleton archived tolerance intervals are shown as a separate band.
    base_low=low[0];base_high=high[0]
    nominal=np.clip(z['block_raw_modulus_count'],low,high)
    ax.fill_between(offset,low-base_high-offset/2,high-base_low-offset/2,
        color=BLUE,alpha=.2,linewidth=0,label='Boundary sensitivity')
    ax.plot(offset,nominal-nominal[0]-offset/2,color=BLUE,lw=.95)
    ax.axhline(0,ls='--',color='#333333',lw=1.)
    for degree,col in [(1210,TEAL),(1421,AMBER)]:
        off=degree-1000;i=int(np.flatnonzero(offset==off)[0]);ax.scatter(off,nominal[i]-nominal[0]-off/2,s=24,color=col,zorder=3)
    ax.set_xlabel(r'Appended degree $m$');ax.set_ylabel(r'$\nu_{1000+m}(1)-\nu_{1000}(1)-m/2$')
    ax.legend(frameon=False,loc='upper left',fontsize=9,handlelength=1.5)
    panel(ax,'b','Count fluctuations across the block');grid(ax)
    save(fig,'root-matching')


if __name__=='__main__':
    radial_profile();annulus();small_derivative();root_matching()
    record={
        'matplotlib_version':matplotlib.__version__,
        'font_family':'STIXGeneral', 'mathtext_fontset':'stix',
        'text_size_range_pt':[9,10],
        "math_scripts":"Mathematical subscripts and superscripts use the font's normal reduced size.",
        'canvas':'Uncropped, exactly 5.8 inches wide; include at full text width.',
        'figures':RENDERED,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'data_sha256':{str(path.relative_to(HERE)):hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted([*DATA.glob('*.csv'),DATA/'bootstrap-fits.json',
                DATA/'sequence-statistics.npz',HERE/'matching.npz',HERE/'metadata.json'])},
        'outputs_sha256':{path.name:hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(OUT.glob('*')) if path.suffix in {'.pdf','.svg'}}}
    (HERE/'rendering.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
