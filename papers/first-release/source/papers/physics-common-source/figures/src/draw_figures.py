#!/usr/bin/env python3
"""Reproducible source-model diagrams; no fitted or experimental data.

Run with --output DIR --dpi 240. SVG text stays editable. PNG is the
manuscript preview; the same figure generates the r10 PDF plate.
--lang zh (default) writes the Chinese set; --lang en writes the English set
with -en file names and a -en receipt. Visual language: house_style.py.
"""
from __future__ import annotations
import argparse, hashlib, json, math
from datetime import datetime, timezone
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib import font_manager
from matplotlib.lines import Line2D
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Rectangle, Circle
from matplotlib import patheffects
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/'shared'/'figure-style'))
from house_style import INK,SLATE,MUTE,HAIR,DEEP,VERMILION,GOLD,WASH,DARK,install
from matplotlib.colors import LinearSegmentedColormap
SIGMA=.5; K=math.sqrt(2); A=3*K/5; N=math.sqrt(54/125)
OMEGA=3*N*(K-A)/2; KAPPA=9*N/5; M=3*N; C=5*N; Q4=3/(2*N)
REPORT={'source_revision':'e60a86058abcb74b7f2225f2383c182be8343785',
        'scope':'Formula/plot checks only; no new Lean build or experiment',
        'constants':dict(sigma=SIGMA,k=K,a=A,N=N,omega=OMEGA,kappa=KAPPA,m=M,c=C)}
def text(ax,x,y,s,size=11,color=INK,ha='center',weight='normal',**kw):
    return ax.text(x,y,s,transform=ax.transAxes,ha=ha,va='center',fontsize=size,color=color,fontweight=weight,**kw)
def box(ax,x,y,w,h,fill='white',edge=HAIR,lw=.9):
    p=FancyBboxPatch((x,y),w,h,boxstyle='round,pad=0.006,rounding_size=0.006',
                    facecolor=fill,edgecolor=edge,linewidth=lw,transform=ax.transAxes)
    ax.add_patch(p); return p
def arrow(ax,start,end,color=SLATE,lw=1.1):
    ax.add_patch(FancyArrowPatch(start,end,arrowstyle='-|>',mutation_scale=11,
                                linewidth=lw,color=color,transform=ax.transAxes))
def inline(ax,x,y,parts,size):
    """Centre a run of differently coloured math/text segments on (x,y)."""
    fig=ax.figure;fig.canvas.draw();r=fig.canvas.get_renderer()
    items=[ax.text(0,y,s,transform=ax.transAxes,fontsize=size,color=c,va='center',ha='left') for s,c in parts]
    widths=[t.get_window_extent(r).width for t in items]
    axw=ax.get_window_extent(r).width;total=sum(widths)/axw;cur=x-total/2
    for t,w in zip(items,widths):t.set_x(cur);cur+=w/axw
def save(fig,name,out,dpi,scale=None):
    # Canvases are laid out at a large size; printing them at ~6 in wide shrank
    # 10 pt labels below 5 pt. Shrinking the canvas keeps the layout and raises
    # the printed type size by 1/PRINT_SCALE.
    if not getattr(fig,'print_scaled',False):fig.set_size_inches(*(fig.get_size_inches()*(scale or PRINT_SCALE)))
    fig.canvas.draw()
    fig.savefig(out/(name+'.svg'),metadata={'Date':'2026-09-30','Creator':'physics-common-source figure script'})
    svg=out/(name+'.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
    fig.savefig(out/(name+'.png'),dpi=dpi)
    fig.savefig(out/(name+'-r10.pdf'),metadata={'Title':name,'CreationDate':datetime(2026,9,30,tzinfo=timezone.utc),'ModDate':datetime(2026,9,30,tzinfo=timezone.utc)})
    plt.close(fig)
def gap(r):
    return C*(r-A)**2+Q4*(r-A)**2*(r+A)**2
PRINT_SCALE=.72
def frac_ticks(ax,axis,values,labels):
    getattr(ax,f'set_{axis}ticks')(values);getattr(ax,f'set_{axis}ticklabels')(labels)

FIG1={
 'zh':dict(carrier='母物质载体',dims='7 + 21 + 35 = 63；四个 Dirac 分量',
   dual=r'$\chi$：独立线性对偶',carrier_note='任意母作用；指定物质场与对偶',
   response='占据响应',ops='E 嵌入　P 投影　S 上下交换',
   response_note=r'$R(A)$ 不必酉、不必自伴',fock='费米子 Fock 空间',
   kept='含交换 $S$', dropped='省去 $S$', dark='暗时刻：差 1', agree='初时刻一致',
   inset='同一占据态上的电流读数（§6.6）'),
 'en':dict(carrier='Full matter carrier',dims='7 + 21 + 35 = 63; four Dirac components',
   dual=r'$\chi$: independent linear dual',carrier_note='arbitrary $A$; designated field and dual',
   response='Occupation response',ops='E embed   P project   S swap',
   response_note=r'$R(A)$ need be neither unitary nor self-adjoint',fock='Fermionic Fock space',
   kept='with swap $S$', dropped='without $S$', dark='dark moment:\noff by 1', agree='agree at the start',
   inset='Current reading on the same occupation state (§6.6)')}

def fig1(out,dpi,lang):
    s=FIG1[lang]; en=lang=='en'
    fig,ax=plt.subplots(figsize=(14*PRINT_SCALE,8.4*PRINT_SCALE));fig.print_scaled=True
    fig.subplots_adjust(left=0,right=1,bottom=0,top=1);ax.axis('off')
    cols=[.17,.5,.83]
    for x,h in zip(cols,[s['carrier'],s['response'],s['fock']]):
        text(ax,x,.955,h,13 if en else 14,color=SLATE)
    for x in (.335,.665):ax.plot([x,x],[.47,.975],color=HAIR,lw=.8,transform=ax.transAxes)
    text(ax,cols[0],.885,r'$\mathcal{M}\simeq\mathbb{C}^{252}$',24)
    text(ax,cols[0],.805,r'$\Lambda^6\mathbb{C}^7\oplus\Lambda^2\mathbb{C}^7\oplus\Lambda^4\mathbb{C}^7$',15)
    text(ax,cols[0],.762,s['dims'],10,color=SLATE)
    text(ax,cols[0],.685,r'$\psi=2Ev$',20);text(ax,cols[0],.628,s['dual'],11.5)
    text(ax,cols[0],.575,r'$A\in\mathrm{End}_{\mathbb{C}}(\mathcal{M})$',16)
    text(ax,cols[0],.51,s['carrier_note'],9.5 if en else 10.5,color=SLATE)
    text(ax,cols[1],.885,r'$\mathcal{E}=\mathbb{C}^{8}$',24)
    text(ax,cols[1],.805,r'$v=\frac{1}{2}P\psi,\qquad \langle v,v\rangle=1$',17)
    inline(ax,cols[1],.705,[(r'$R(A)=$',INK),(r'$S$',VERMILION),(r'$PAE$',INK)],28)
    text(ax,cols[1],.625,r'$PE=1,\quad S^*=S,\quad S^2=1$',14)
    text(ax,cols[1],.575,s['ops'],10 if en else 10.5,color=SLATE)
    text(ax,cols[1],.51,s['response_note'],9.5 if en else 10.5,color=SLATE)
    arrow(ax,(.312,.745),(.358,.745));text(ax,.335,.78,r'$P/2$',12,color=SLATE)
    arrow(ax,(.642,.745),(.688,.745));text(ax,.665,.78,r'$I$',13,color=SLATE)
    text(ax,cols[2],.885,r'$\mathcal{F}_-(\mathcal{E}),\ \dim=256$',19)
    text(ax,cols[2],.822,r'$I(v)\in\Lambda^1\mathcal{E}$',15,color=DEEP)
    dims=[math.comb(8,n) for n in range(9)]
    for n,d in enumerate(dims):
        x=.722+(n%3)*.074; y=.70-(n//3)*.085; active=n==1
        box(ax,x,y,.066,.07,fill=DEEP if active else 'white',edge=DEEP if active else HAIR)
        c='white' if active else INK
        text(ax,x+.033,y+.047,rf'$\Lambda^{n}\mathcal{{E}}$',11,color=c);text(ax,x+.033,y+.019,str(d),11.5,color=c)
    ax.plot([.06,.94],[.445,.445],color=HAIR,lw=.8,transform=ax.transAxes)
    text(ax,.5,.385,r'$\chi(A\psi)=4k\langle v,R(A)v\rangle=4k\langle I(v),\mathrm{d}\Gamma(R(A))I(v)\rangle,\qquad k=\sqrt{2}$',21)
    ax.plot([.06,.94],[.325,.325],color=HAIR,lw=.8,transform=ax.transAxes)
    ins=fig.add_axes([.30,.075,.44,.19]);th=np.linspace(0,np.pi,500)
    ins.axhline(0,color=HAIR,lw=.7)
    ins.plot(th,np.full_like(th,.5),color=DEEP,lw=2.2)
    ins.plot(th,np.cos(2*th)/2,color=VERMILION,lw=2.2,ls=(0,(5,2.2)))
    ins.annotate('',xy=(np.pi/2,.5),xytext=(np.pi/2,-.5),arrowprops=dict(arrowstyle='<->',color=INK,lw=1,shrinkA=2,shrinkB=2))
    ins.text(np.pi/2+.07,.2,s['dark'],fontsize=10.5,color=INK,va='center')
    ins.scatter([0],[.5],s=30,color=INK,zorder=5)
    ins.text(.06,.60,s['agree'],fontsize=9.5,color=SLATE,va='bottom')
    ins.text(np.pi*.98,.57,s['kept'],fontsize=10.5,color=DEEP,ha='right',va='bottom')
    ins.text(np.pi*.80,-.42,s['dropped'],fontsize=10.5,color=VERMILION,ha='left')
    frac_ticks(ins,'x',[0,np.pi/4,np.pi/2,3*np.pi/4,np.pi],[r'$0$',r'$\pi/4$',r'$\pi/2$',r'$3\pi/4$',r'$\pi$'])
    frac_ticks(ins,'y',[-.5,0,.5],[r'$-\frac{1}{2}$',r'$0$',r'$\frac{1}{2}$'])
    ins.set_xlabel(r'$\theta$',fontsize=12,labelpad=1);ins.set_ylim(-.66,.72);ins.set_xlim(0,np.pi)
    ins.set_title(s['inset'],fontsize=10.5 if en else 11,color=SLATE,pad=6)
    save(fig,'fig1-trinity-lens-system'+('-en' if en else ''),out,dpi)

FIG2={
 'zh':dict(action='同一九场作用',cartan='Cartan / 本构写入先闭合',
   phase='相位平衡与完整余标架变分',fiber='联合零纤维',
   residuals='九类残差逐点为零',
   cancel=r'$\omega/N=3(k-a)/2$；余标架时间列 $3+9/5-24/5=0$，空间列 $-N-3N/5+8N/5=0$',
   hessian='原点 Hessian 特征方向',
   xlabel=r'$u$　余标架时间列伸缩',ylabel=r'$b$　规范辅助场缩放',
   minimum='固定 $u$ 的极小，不是二维稳定点',writein='完整写入保留新余标架',
   family=r'原两参数族始终有 $B_{3,0}=-N$',successor='后继离开该族；此分量不在左图坐标内'),
 'en':dict(action='The same nine-field action',cartan='Cartan / constitutive writes close first',
   phase='Phase balance and full coframe variation',fiber='Joint zero fiber',
   residuals='all nine residual classes\nvanish pointwise',
   cancel=r'$\omega/N=3(k-a)/2$; coframe time column $3+9/5-24/5=0$, space column $-N-3N/5+8N/5=0$',
   hessian='origin Hessian eigendirections',
   xlabel=r'$u$: coframe time-column stretch',ylabel=r'$b$: gauge auxiliary-field scale',
   minimum='Minimum at fixed $u$,\nnot a 2D stationary point',writein='The complete write-in\nkeeps the new coframe',
   family=r'the original family always has $B_{3,0}=-N$',
   successor='The successor leaves the family;\nnot a coordinate of the left panel')}

def fig2(out,dpi,lang):
    s=FIG2[lang]; en=lang=='en'
    fig=plt.figure(figsize=(12,9.0)); top=fig.add_axes([.025,.745,.95,.235]);top.axis('off')
    box(top,.015,.20,.20,.52);text(top,.115,.55,s['action'],10 if en else 13.5);text(top,.115,.37,r'$L[e,\varpi,B,\lambda,A,B_A,\varphi,\psi,\chi]$',11)
    arrow(top,(.225,.47),(.286,.62))
    box(top,.295,.52,.405,.26);text(top,.497,.69,s['cartan'],10 if en else 11,color=SLATE);text(top,.497,.595,r'$\lambda,\ B,\ B_A,\ \mathrm{Lorentz\ 3\!\!-form}$',12.5)
    box(top,.295,.10,.405,.26);text(top,.497,.27,s['phase'],10 if en else 11,color=SLATE);text(top,.497,.175,r'$A,\ \varphi,\ \psi,\ \chi,\ e\ (16\ \mathrm{directions})$',12.5)
    arrow(top,(.497,.505),(.497,.375));arrow(top,(.71,.23),(.77,.44));box(top,.78,.20,.195,.52,fill=WASH,edge=WASH)
    text(top,.8775,.55,s['fiber'],12.5 if en else 13.5);text(top,.8775,.36 if en else .37,s['residuals'],9 if en else 10,color=SLATE)
    fig.text(.5,.718,s['cancel'],ha='center',fontsize=11 if en else 11.5,color=SLATE)
    ax=fig.add_axes([.085,.075,.575,.575]);u=np.linspace(-.80,1.02,401);b=np.linspace(-1.03,1.72,401)
    U,B=np.meshgrid(u,b); L=B*B+2*U*B+U*B*B
    with matplotlib.rc_context({'contour.negative_linestyle':':'}):
        contours=ax.contour(U,B,L,levels=[-2,-1,-.5,-.2,0,.2,.5,1,2,3,5],colors=MUTE,linewidths=.75)
    ax.clabel(contours,inline=True,fontsize=8,fmt='%g')
    val=-u/(1+u);valid=(val>=b.min())&(val<=b.max())
    ax.plot(u[valid],val[valid],color=DEEP,lw=2.4,label=r'$b^*(u)=-u/(1+u)$')
    phi=(1+math.sqrt(5))/2;h=np.linspace(-.42,.42,80)
    for k,slope in enumerate((phi,-1/phi)):
        ax.plot(h,slope*h,color=INK,lw=1,ls=(0,(6,2.4)),alpha=.7,label=s['hessian'] if k==0 else None)
    ax.scatter([0],[0],color=INK,s=26,zorder=5);ax.scatter([.5],[-1/3],color=VERMILION,s=60,edgecolor='white',linewidth=1.2,zorder=6)
    ax.annotate(r'$(1/2,-1/3)$',(.5,-1/3),xytext=(.62,.14),fontsize=12,color=VERMILION,arrowprops={'arrowstyle':'-','color':VERMILION,'lw':.9})
    ax.set(xlim=(u.min(),u.max()),ylim=(b.min(),b.max()),xlabel=s['xlabel'],ylabel=s['ylabel'])
    ax.set_title(r'$\ell=(L-L_0)/\kappa=b^2+2ub+ub^2,\qquad \kappa=9N/5,\ u>-1$',fontsize=14,pad=12)
    ax.legend(loc='upper right',fontsize=10)
    note=fig.add_axes([.707,.075,.27,.575]);note.axis('off')
    text(note,.5,.925,s['minimum'],9.5 if en else 11.5,color=SLATE)
    text(note,.5,.85,r'$\partial_b^2L=2\kappa(1+u)>0$',15)
    text(note,.5,.77,r'$\det H=-4\kappa^2<0$',15)
    box(note,.015,.14,.97,.52,fill=WASH,edge=WASH)
    text(note,.5,.595,s['writein'],9.5 if en else 12,color=SLATE)
    text(note,.5,.51,r'$B\leftarrow\mathrm{II}^+(e_u)$',18,color=DEEP)
    text(note,.5,.41,r'$B_{3,0}:\quad -N\ \longrightarrow\ -3N/2$',15)
    text(note,.5,.305,r'$\Delta B_{3,0}=-N/2$',22,color=VERMILION)
    text(note,.5,.20,s['family'],8.5 if en else 10.5,color=SLATE)
    text(note,.5,.065,s['successor'],9 if en else 10.5,color=SLATE)
    save(fig,'fig2-nine-field-balance'+('-en' if en else ''),out,dpi,scale=.85)

def bisect_root(f,left,right):
    fl,fr=f(left),f(right)
    if fl*fr>0:raise ValueError('Root not bracketed')
    for _ in range(100):
        middle=(left+right)/2;fm=f(middle)
        if fl*fm<=0:right=middle
        else:left=middle;fl=fm
    return (left+right)/2

def turning_points(energy):
    reach=1.
    while gap(A-reach)<energy:reach*=2
    left=bisect_root(lambda r:gap(r)-energy,A-reach,A)
    reach=1.
    while gap(A+reach)<energy:reach*=2
    right=bisect_root(lambda r:gap(r)-energy,A,A+reach)
    return left,right

FIG3={
 'zh':dict(xlabel=r'规范幅度 $r$',ylabel=r'共轭动量 $p$',
   sections='精确能量方程的闭合截线',
   bound=r'$c(r-a)^2$：全局下界',remainder='非负四次余项',
   potential='相对势能',decomposition='非负分解；余项仍贡献局部二阶曲率',
   method=r'$E_{\mathrm{rel}}=p_0^2/(2m)$；转向点二分求根，无 ODE 数值积分'),
 'en':dict(xlabel=r'gauge amplitude $r$',ylabel=r'conjugate momentum $p$',
   sections='Closed section curves of the exact energy equation',
   bound=r'$c(r-a)^2$: global lower bound',remainder='nonnegative quartic remainder',
   potential='relative potential energy',
   decomposition='Nonnegative decomposition; the remainder\nstill contributes local second-order curvature',
   method=r'$E_{\mathrm{rel}}=p_0^2/(2m)$; turning points by bisection, no ODE integration')}
RAMP=['#a9bdd2','#6a8fb4','#33628f','#15385a']

def fig3(out,dpi,lang):
    s=FIG3[lang]; en=lang=='en'
    fig=plt.figure(figsize=(12.8,6.3));ax=fig.add_axes([.08,.21,.39,.60]);en_ax=fig.add_axes([.57,.21,.40,.60])
    roots=[];guides={}
    for impulse,color in zip([.6,1.2,1.8,2.4],RAMP):
        energy=impulse**2/(2*M);lo,hi=turning_points(energy)
        r=(lo+hi)/2-(hi-lo)/2*np.cos(np.linspace(0,math.pi,801))
        p=np.sqrt(np.maximum(0,2*M*(energy-gap(r))));p[[0,-1]]=0
        ax.plot(np.r_[r,r[::-1]],np.r_[p,-p[::-1]],color=color,lw=1.8,label=rf'$p_0={impulse:g}$')
        roots.append(dict(impulse=impulse,left=lo,right=hi,energy=energy,root_residual=max(abs(gap(lo)-energy),abs(gap(hi)-energy))))
        if impulse in (1.2,2.4):guides[impulse]=color
    for item in roots:
        if item['impulse'] in guides:
            for edge in (item['left'],item['right']):
                ax.axvline(edge,color=guides[item['impulse']],ls=':',lw=1,alpha=.9,zorder=1)
    ax.scatter([A],[0],s=30,color=INK,zorder=6);ax.axvline(A,color=HAIR,ls=':',lw=.8)
    ax.set(xlabel=s['xlabel'],ylabel=s['ylabel'])
    ax.set_title(s['sections'],pad=30,fontsize=11 if en else 12,color=SLATE)
    ax.legend(fontsize=10,loc='lower center',bbox_to_anchor=(.5,1.015),ncol=4,borderaxespad=0,columnspacing=1.1,handlelength=1.8,handletextpad=.5)
    r=np.linspace(A-.65,A+.65,601);lower=C*(r-A)**2;remainder=Q4*(r-A)**2*(r+A)**2
    en_ax.plot(r,lower+remainder,color=INK,lw=2.2,label=r'$V(r)-V(a)$')
    en_ax.plot(r,lower,color=GOLD,lw=1.8,ls='--',label=s['bound'])
    en_ax.plot(r,remainder,color=VERMILION,lw=2,ls=':',label=s['remainder'])
    for item in roots:
        if item['impulse'] in guides:
            color=guides[item['impulse']]
            en_ax.plot([item['left'],item['right']],[item['energy']]*2,color=color,lw=1.3,zorder=5)
            en_ax.scatter([item['left'],item['right']],[item['energy']]*2,s=22,color=color,zorder=6)
            en_ax.text((item['left']+item['right'])/2,item['energy']+.09,rf"$p_0={item['impulse']:g}$",ha='center',fontsize=10,color=color)
    en_ax.scatter([A],[0],s=26,color=INK,zorder=6);en_ax.set(xlabel=s['xlabel'],ylabel=s['potential'])
    en_ax.set_title(s['decomposition'],pad=24 if en else 30,fontsize=10 if en else 12,color=SLATE)
    en_ax.legend(fontsize=9.5 if en else 10,loc='upper left');en_ax.set_ylim(bottom=-.12)
    fig.text(.275,.025,s['method'],ha='center',fontsize=10,color=SLATE)
    fig.text(.77,.025,r'$V(a+\delta)-V(a)=3c\delta^2+O(\delta^3)$',ha='center',fontsize=12)
    REPORT['turning_points']=roots
    save(fig,'fig4-global-orbit-energy'+('-en' if en else ''),out,dpi)

FIG4={
 'zh':dict(control='指定排他对照',dark='暗时刻',dark_sub='两支振幅相消，纯态仍在',
   xlabel=r'$u=t/t^{*}$',ylabel=r'$\cos^2(u\pi/2)$'),
 'en':dict(control='exclusive control',dark='dark moment',dark_sub='the two amplitudes cancel;\nthe pure state remains',
   xlabel=r'$u=t/t^{*}$',ylabel=r'$\cos^2(u\pi/2)$')}

def fig4(out,dpi,lang):
    s=FIG4[lang]; en=lang=='en'
    fig=plt.figure(figsize=(11.8,7.6));ax=fig.add_axes([.12,.42,.76,.55])
    cmap=LinearSegmentedColormap.from_list('reading',[DARK,'#fbf9f3'])
    u=np.linspace(-.05,2.05,1400);val=np.cos(np.pi*u/2)**2
    ax.imshow(val[None,:],extent=(-.05,2.05,-.12,1.12),aspect='auto',cmap=cmap,vmin=0,vmax=1,interpolation='bilinear',zorder=0)
    ax.axhline(.5,color=MUTE,lw=1.1,ls=(0,(5,3)),zorder=2)
    ax.plot(u,val,color=VERMILION,lw=2.8,zorder=4,path_effects=[patheffects.withStroke(linewidth=5.4,foreground='white',alpha=.85)])
    ticks=np.array([0,.5,1,1.5,2]);values=np.array([1,.5,0,.5,1])
    ax.scatter(ticks,values,s=50,color=VERMILION,edgecolor='white',linewidth=1.4,zorder=5)
    for x,y,label in zip(ticks,values,[r'$1$',r'$\frac{1}{2}$',r'$0$',r'$\frac{1}{2}$',r'$1$']):
        ax.annotate(label,(x,y),xytext=(0,13 if y<.8 else -26),textcoords='offset points',ha='center',fontsize=15,
                    color='white' if abs(x-1)<.3 else INK,zorder=6)
    ax.text(.0,.44,s['control']+r' $\frac{1}{2}$',color=SLATE,fontsize=11,ha='left',va='top')
    ax.text(1.0,.40,s['dark'],color='white',ha='center',fontsize=16)
    ax.text(1.0,.30,s['dark_sub'],color='#e6e1d5',ha='center',va='top',fontsize=10.5,linespacing=1.3)
    ax.set(xlim=(-.05,2.05),ylim=(-.12,1.12))
    frac_ticks(ax,'x',ticks,[r'$0$',r'$\frac{1}{2}$',r'$1$',r'$\frac{3}{2}$',r'$2$'])
    frac_ticks(ax,'y',[0,.5,1],[r'$0$',r'$\frac{1}{2}$',r'$1$'])
    ax.set_xlabel(s['xlabel'],fontsize=13);ax.set_ylabel(s['ylabel'],fontsize=13)
    for spine in ax.spines.values():spine.set_visible(False)
    x_left,x_width=ax.get_position().x0,ax.get_position().width
    for time,phase_label in zip(ticks,['0',r'\pi/4',r'\pi/2',r'3\pi/4',r'\pi']):
        center=x_left+x_width*(time+.05)/2.1
        pa=fig.add_axes([center-.065,.09,.13,.205]);pa.set_aspect('equal');pa.axis('off');pa.set(xlim=(-1.2,1.2),ylim=(-1.3,1.45))
        pa.add_patch(Circle((0,0),1,fill=False,edgecolor=HAIR,lw=.9));theta=np.pi*time/2
        # Nested strokes keep coincident phases visible without shifting their
        # exact unit-vector endpoints or hiding the real average underneath.
        overlap=abs(np.sin(theta))<1e-12
        pa.plot([0,np.cos(theta)],[0,0],color=VERMILION,lw=5 if overlap else 3.2,solid_capstyle='round',zorder=2)
        for sign,color,ls,lw in [(1,DEEP,'-',3.2 if overlap else 1.5),(-1,GOLD,(0,(3,2)),1.5)]:
            phase=FancyArrowPatch((0,0),(np.cos(theta),sign*np.sin(theta)),arrowstyle='-|>',mutation_scale=12 if sign==1 else 9,
                                 color=color,linewidth=lw,linestyle=ls,shrinkA=0,shrinkB=0,zorder=3 if sign==1 else 4)
            if sign==-1:phase.set_path_effects([patheffects.withStroke(linewidth=2.2,foreground='white')])
            pa.add_patch(phase)
        pa.scatter([0],[0],s=12,color=VERMILION,zorder=5)
        pa.text(0,1.28,rf'$\theta={phase_label}$',ha='center',fontsize=12)
    fig.legend(handles=[Line2D([],[],color=DEEP,lw=1.5,label=r'$e^{i\theta}$'),
                        Line2D([],[],color=GOLD,lw=1.5,ls=(0,(3,2)),label=r'$e^{-i\theta}$'),
                        Line2D([],[],color=VERMILION,lw=3.2,label=r'$(e^{i\theta}+e^{-i\theta})/2=\cos\theta$')],
               loc='lower center',bbox_to_anchor=(.5,.016),ncol=3,fontsize=12,
               handlelength=1.6,handletextpad=.6,columnspacing=1.7)
    save(fig,'fig3-five-point-quantum-clock'+('-en' if en else ''),out,dpi)

def validate():
    rng=np.random.default_rng(20260920);u=rng.uniform(-.8,1.2,500);b=rng.uniform(-2,2,500)
    direct=3*N*u+KAPPA*((1+u)*(1+b)**2-2*(1+b)+1)-6*N*u*K*(K-A)
    normal=KAPPA*(b*b+2*u*b+u*b*b);b_star=-u/(1+u)
    eliminated=-KAPPA*u*u/(1+u)+KAPPA*(1+u)*(b-b_star)**2
    H=np.block([[np.zeros((3,3)),np.eye(3)/N],[-N*np.eye(3),np.zeros((3,3))]])
    r=np.linspace(-3,3,1001);V=lambda x:Q4*x**4-6*N*K*x
    errs={'constant_balance':abs(A**3-2*SIGMA*N*N*K),
          'frequency_square':abs(OMEGA**2-972/3125),
          'hodge_square':float(np.max(abs(H@H+np.eye(6)))),
          'constitutive_inverse':float(np.max(abs((SIGMA*H)@(-H/SIGMA)-np.eye(6)))),
          'clock_density':float(np.max(abs(direct-normal))),
          'clock_elimination':float(np.max(abs(normal-eliminated))),
          'energy_decomposition':float(np.max(abs(V(r)-V(A)-gap(r)))),
          'remainder_quadratic_coefficient':abs(4*Q4*A*A-2*C),
          'gravity_feedback':abs((-1.5*N+N)-(-N/2)),
          'turning_points':max(item['root_residual'] for item in REPORT['turning_points'])}
    values=np.abs((np.exp(1j*np.pi*np.arange(5)/4)+np.exp(-1j*np.pi*np.arange(5)/4))/2)**2
    errs['five_point_values']=float(np.max(abs(values-np.array([1,.5,0,.5,1]))))
    if max(errs.values())>1e-10:raise AssertionError(errs)
    dims=[math.comb(8,n) for n in range(9)];assert sum(dims)==256
    REPORT.update(status='passed',absolute_tolerance=1e-10,residuals=errs,sector_dimensions=dims,
                  phase_control={'accepted':.5,'raw_initial':.5,'raw_quarter':float(.5*np.cos(np.pi/2)),'raw_dark':-.5},
                  versions={'numpy':np.__version__,'matplotlib':matplotlib.__version__})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'vector')
    parser.add_argument('--dpi',type=int,default=240)
    parser.add_argument('--lang',choices=['zh','en'],default='zh')
    args=parser.parse_args()
    if not 72<=args.dpi<=600:parser.error('--dpi must be in [72,600]')
    args.output.mkdir(parents=True,exist_ok=True)
    install('physics-common-source-20260930',args.lang)
    suffix='-en' if args.lang=='en' else ''
    for draw in [fig1,fig2,fig3,fig4]:draw(args.output,args.dpi,args.lang)
    validate()
    REPORT['artifacts']={}
    for base in ['fig1-trinity-lens-system','fig2-nine-field-balance','fig3-five-point-quantum-clock','fig4-global-orbit-energy']:
        for ext in ['.svg','.png','-r10.pdf']:
            p=args.output/(base+suffix+ext)
            REPORT['artifacts'][p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
    (args.output/('figure-checks'+suffix+'.json')).write_text(json.dumps(REPORT,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':REPORT['status'],'max_residual':max(REPORT['residuals'].values()),
                      'output':str(args.output),'artifacts':len(REPORT['artifacts'])},ensure_ascii=False))
if __name__=='__main__':main()
