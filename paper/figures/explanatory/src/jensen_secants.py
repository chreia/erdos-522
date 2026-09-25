"""Jensen secants at N = 1e5, seed 522000. Reads data/jensen.npz. Writes ../jensen-secants.pdf."""
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE.parent
import numpy as np
from paperstyle import *
setup()
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
D=np.load(HERE/'data/jensen.npz'); x,J,nu,F,N=D['x'],D['J'],D['nu'],D['F'],int(D['N'])
g=np.euler_gamma; y=J-0.5*np.log(N); th=F-g/2; cnt=nu/N
def Phi(t):
    t=np.asarray(t,float); out=np.full_like(t,0.5); nz=np.abs(t)>1e-9
    out[nz]=np.exp(2*t[nz])/(np.exp(2*t[nz])-1)-1/(2*t[nz]); return out
at=lambda v,arr: float(np.interp(v,x,arr))
K=4.0; h=N**(-1/64)
fig=plt.figure(figsize=(5.8,2.55))
gs=GridSpec(1,3,width_ratios=[1.15,1.15,0.78],wspace=0.42,left=0.075,right=0.99,bottom=0.17,top=0.86)
a,b,c=(fig.add_subplot(gs[i]) for i in range(3))
# a: the convex function and its chords
a.plot(x,th,color=INK,lw=LW_THEORY,zorder=2,label=r'$F(x)-\gamma/2$')
k=np.arange(0,len(x),50); a.plot(x[k],y[k],'o',ms=2.6,color=OI_BLUE_TINT,mec='none',zorder=3,label=r'$J_N(r)-\frac{1}{2}\log N$')
for (x1,x2) in [(-K,-K/2),(K/2,K)]:
    s=(at(x2,y)-at(x1,y))/(x2-x1); xx=np.array([x1-1.4,x2+1.4])
    a.plot(xx,at(x1,y)+s*(xx-x1),color=OI_BLUE,lw=LW_CONSTR,zorder=4,solid_capstyle='round')
    a.plot([x1,x2],[at(x1,y),at(x2,y)],'o',ms=MS+0.4,color=OI_BLUE,mec='white',mew=0.6,zorder=5)
for xv,lab,dy in [(-K,r'$r_1$',-15),(-K/2,r'$r_2$',-15),(K/2,r'$r_3$',6),(K,r'$r_4$',6)]:
    a.annotate(lab,xy=(xv,at(xv,y)),xytext=(-7 if xv>0 else 0,dy),textcoords='offset points',ha='center',fontsize=8.5,color=INK)
a.set_xlim(-10,10); a.set_ylim(-2.9,8.8); a.set_xticks([-8,-4,0,4,8]); a.set_xlabel(r'$x=N(r-1)$')
a.legend(loc='upper left',handlelength=1.1,borderaxespad=0.1,labelspacing=0.3)
title(a,'a',r'$J_N$ is convex in $\log r$')
# b: slopes are counts
b.plot(x,Phi(x),color=INK,lw=LW_THEORY,zorder=2,label=r'$\Phi(x)$')
kb=np.arange(0,len(x),40); b.plot(x[kb],cnt[kb],'o',ms=2.6,color=OI_BLUE_TINT,mec='none',zorder=3,label=r'$\nu_N(r)/N$')
for (x1,x2) in [(-K,-K/2),(K/2,K)]:
    s=(at(x2,y)-at(x1,y))/(x2-x1)
    b.plot([x1,x2],[s,s],color=OI_BLUE,lw=1.5,solid_capstyle='butt',zorder=4)
    xe=x1 if x1<0 else x2; ce=at(xe,cnt)
    b.plot([xe,xe],[ce,s],color=OI_BLUE,lw=LW_FINE,ls=(0,(1.2,1.2)),zorder=4)
    b.plot([xe],[ce],'o',ms=MS+0.4,color=OI_BLUE,mec='white',mew=0.6,zorder=5)
sL=(at(-K/2,y)-at(-K,y))/(K/2); sR=(at(K,y)-at(K/2,y))/(K/2)
b.text(-K-0.35,sL+0.012,'left chord',fontsize=7.8,color=INK,ha='right',va='bottom')
b.text(K/2-0.35,sR+0.012,'right chord',fontsize=7.8,color=INK,ha='right',va='bottom')
b.text(-K+0.35,at(-K,cnt)-0.035,r'$\nu_N(r_1)/N$',fontsize=7.8,color=INK,ha='left',va='top')
b.text(K+0.3,at(K,cnt)-0.05,r'$\nu_N(r_4)/N$',fontsize=7.8,color=INK,ha='left',va='top')
b.set_xlim(-10,10); b.set_ylim(0,1); b.set_xticks([-8,-4,0,4,8]); b.set_yticks([0,0.5,1],['0','1/2','1'])
b.set_xlabel(r'$x=N(r-1)$')
b.legend(loc='center right',bbox_to_anchor=(1.0,0.42),handlelength=1.1,borderaxespad=0.1,labelspacing=0.3)
title(b,'b','slopes are root counts')
# c: thin band
m=(x>-2.3)&(x<2.3)
c.plot(x[m],Phi(x[m]),color=INK,lw=LW_THEORY,zorder=2)
kc=np.where(m)[0][::12]; c.plot(x[kc],cnt[kc],'o',ms=2.6,color=OI_BLUE_TINT,mec='none',zorder=3)
for (x1,x2) in [(-h,0.0),(0.0,h)]:
    s=(at(x2,y)-at(x1,y))/(x2-x1); c.plot([x1,x2],[s,s],color=OI_BLUE,lw=1.5,solid_capstyle='butt',zorder=4)
c.plot([0],[at(0,cnt)],'o',ms=MS+0.4,color=OI_BLUE,mec='white',mew=0.6,zorder=5)
c.set_xlim(-2.3,2.3); c.set_ylim(0.28,0.72)
c.set_xticks([-h,0,h],[r'$-h$',r'$0$',r'$h$']); c.set_yticks([0.5],['1/2'])
c.set_xlabel(r'$x$, with $h=N^{-1/64}$')
title(c,'c','thin band')
fig.savefig(OUT/'jensen-secants.pdf')
print('ok', h)
