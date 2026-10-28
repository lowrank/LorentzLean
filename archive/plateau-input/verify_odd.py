#!/usr/bin/env python3
"""Verify and generate the exact finite certificate for Lorentz conjecture 3 prime.

Requires Python 3.9+ and only the standard library. No floating-point result is
used as a proof condition. The certificate arithmetic takes place in Q[z]/(M),
with the relevant real embedding isolated by exact rational bisection. The
analytic Holder-contact argument and all-degree lifting are supplied in the
accompanying mathematical note.

Usage: python verify_odd.py [output.json]
"""
from pathlib import Path
import sys
from fractions import Fraction as F
import json
import time

# z=2*cos(pi/36), the largest root of this monic polynomial.
MOD=[1,0,-36,0,105,0,-112,0,54,0,-12,0,1]
N=12

def trim(a):
    while a and a[-1]==0:a.pop()
    return a

def padd(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a):c[i]+=v
    for i,v in enumerate(b):c[i]+=v
    return trim(c)

def pmul(a,b):
    if not a or not b:return []
    c=[F(0)]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        if v:
            for j,w in enumerate(b):
                if w:c[i+j]+=v*w
    return trim(c)

def pdiv(a,b):
    a=a.copy();q=[F(0)]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b) and a:
        j=len(a)-len(b);v=a[-1]/b[-1];q[j]=v
        for k,w in enumerate(b):a[j+k]-=v*w
        trim(a)
    return trim(q),a

class E:
    def __init__(self,a=0):
        if isinstance(a,E):self.a=a.a;return
        if isinstance(a,(int,F)):a=[F(a)]
        a=[F(v) for v in a];trim(a)
        for i in range(len(a)-1,N-1,-1):
            v=a[i]
            if v:
                for k in range(N):a[i-N+k]-=v*MOD[k]
        self.a=tuple(trim(a[:N]))
    def __add__(self,o):return E(padd(list(self.a),list(E(o).a)))
    __radd__=__add__
    def __neg__(self):return E([-v for v in self.a])
    def __sub__(self,o):return self+-E(o)
    def __rsub__(self,o):return E(o)+-self
    def __mul__(self,o):return E(pmul(list(self.a),list(E(o).a)))
    __rmul__=__mul__
    def inv(self):
        if not self.a:raise ZeroDivisionError
        r0=[F(v) for v in MOD];r1=list(self.a);s0=[];s1=[F(1)]
        while r1:
            q,r2=pdiv(r0,r1)
            s2=padd(s0,[-v for v in pmul(q,s1)])
            r0,r1=r1,r2;s0,s1=s1,s2
        if len(r0)!=1:raise ValueError('not invertible')
        return E([v/r0[0] for v in s0])
    def __truediv__(self,o):return self*E(o).inv()
    def __rtruediv__(self,o):return E(o)*self.inv()
    def __pow__(self,k):
        if k<0:return self.inv()**(-k)
        q=E(1);a=self
        while k:
            if k&1:q=q*a
            a=a*a;k//=2
        return q
    def __bool__(self):return bool(self.a)
    def __eq__(self,o):return self.a==E(o).a
    def floats(self,z=1.992389396183491):
        v=0.
        for c in self.a[::-1]:v=v*z+float(c)
        return v
    def serialize(self):return [str(v) for v in self.a]

def solve(A,b):
    n=len(b);A=[[E(x) for x in row]+[E(y)] for row,y in zip(A,b)]
    for i in range(n):
        j=next(j for j in range(i,n) if A[j][i]);A[i],A[j]=A[j],A[i]
        pinv=A[i][i].inv()
        for j in range(i+1,n):
            if not A[j][i]:continue
            fac=A[j][i]*pinv
            for k in range(i+1,n+1):A[j][k]-=fac*A[i][k]
            A[j][i]=E(0)
    x=[E(0)]*n
    for i in range(n-1,-1,-1):
        x[i]=(A[i][n]-sum((A[i][j]*x[j] for j in range(i+1,n)),E(0)))/A[i][i]
    return x

# Exact finite certificate for Lorentz conjecture 3 prime, r=3/5.

start=time.time()
z=E([0,1]);S=[E(2),z]
for k in range(2,37):S.append(z*S[-1]-S[-2])
def cosn(k):
 k%=72
 if k>36:k=72-k
 return S[k]/2
def tf(k,j):return ((-1)**k)*cosn(k*(2*j+1))
r=F(3,5);sqrt3=2*cosn(6)
assert sqrt3*sqrt3==3
X=[tf(1,j) for j in range(18)];CI=[1,4,7,10,13,16]
SF=[(1,-1,-1,1)[j%4] for j in range(18)]
SC=[-(1,-1,-1,1)[j%4] for j in range(6)]
# S_k is the orbit sum of T_k on the fine invariant grid.
H=[[tf(k,j)-r*tf(3*k,j)+r*r/(1+(-1)**k*r)*tf(9*k,j) for j in range(18)] for k in range(8)]
# Check the exact finite functional equation for all eight columns.
map3=[]
for j in range(18):
 y=tf(3,j);ii=next(i for i in range(18) if X[i]==y);map3.append(ii)
for k in range(8):
 for j in range(18):assert H[k][j]+r*H[k][map3[j]]==tf(k,j)
E0=[-(sqrt3+1)/(1+r)-sqrt3*H[2][j]+H[4][j] for j in range(18)]
E1=[1/(1+r)+H[6][j] for j in range(18)]
I4=[0,2,4,13,15,17];I6=[0,2,4,6,11,13,16,17];I2=[0,1,4,5]
print('Solving even forcing and cubic even part',flush=True)
eta,v30,v32=solve([[E1[j],-1,-tf(2,j)] for j in [13,15,17]],[-E0[j] for j in [13,15,17]])
EV=[E0[j]+eta*E1[j] for j in range(18)]
print('Solving quintic even part',flush=True)
v50,v52,v54=solve([[1,tf(2,j),tf(4,j)] for j in [11,13,17]],[EV[j] for j in [11,13,17]])
V5E=[v50+v52*tf(2,j)+v54*tf(4,j) for j in range(18)]
print('Solving odd forcing and quintic odd part',flush=True)
J=[2,11,13,16,17]
beta,v51,v53,v55,t6=solve([[SF[j]*H[7][j],-SF[j]*tf(1,j),-SF[j]*tf(3,j),-SF[j]*tf(5,j),-1] for j in J],[-SF[j]*(EV[j]-3*H[5][j]-V5E[j]) for j in J])
OV=[-3*H[5][j]+beta*H[7][j] for j in range(18)]
HF=[EV[j]+OV[j] for j in range(18)]
print('Solving cubic odd and linear parts',flush=True)
v31,v33,t4=solve([[tf(1,j),tf(3,j),SF[j]] for j in [13,15,17]],[OV[j] for j in [13,15,17]])
v10=EV[CI[0]]
v11,t2=solve([[X[CI[i]],SC[i]] for i in [4,5]],[OV[CI[i]] for i in [4,5]])
h=[eta-sqrt3-1,E(0),-sqrt3,E(0),E(1),E(-3),eta,beta]
v1=[v10,v11];v3=[v30,v31,v32,v33];v5=[v50,v51,v52,v53,v54,v55]
assert sum((h[k]*((-1)**(k//2)) for k in [0,2,4,6]),E(0))==0
assert all(HF[j]==sum((h[k]*H[k][j] for k in range(8)),E(0)) for j in range(18))
polys=[v1,v3,v5];ts=[t2,t4,t6];actives=[I2,I4,I6];grids=[CI,list(range(18)),list(range(18))];signs=[SC,SF,SF]
slacks=[]
for cc,t,ids,sg,active in zip(polys,ts,grids,signs,actives):
 ss=[t-s*(HF[j]-sum((ck*tf(k,j) for k,ck in enumerate(cc)),E(0))) for j,s in zip(ids,sg)]
 assert all(ss[i]==0 for i in active)
 assert all(sg[i]==-sg[j] for i,j in zip(active,active[1:]))
 slacks.append(ss)
# Rational root isolation and interval evaluation.
def peval(p,x):
 y=F(0)
 for c in p[::-1]:y=y*x+c
 return y
lo=F(198,100);hi=F(2)
assert peval(MOD,lo)<0<peval(MOD,hi)
for _ in range(250):
 mid=(lo+hi)/2
 if peval(MOD,mid)<0:lo=mid
 else:hi=mid

def interval(a):
 low=F(0);high=F(0);lp=F(1);hp=F(1)
 for c in a.a:
  if c>=0:low+=c*lp;high+=c*hp
  else:low+=c*hp;high+=c*lp
  lp*=lo;hp*=hi
 return low,high
for name,cc in [('h',h),('v1',v1),('v3',v3),('v5',v5),('lambda',ts)]:
 print(name,[float(sum(interval(v))/2) for v in cc],flush=True)
for n,ss,active in zip([2,4,6],slacks,actives):
 zeros=[j for j,v in enumerate(ss) if not v]
 assert zeros==active,(zeros,active)
 bounds=[interval(v) for v in ss if v]
 assert all(a>F(3,50) for a,b in bounds)
 print('n',n,'exact zeros',zeros,'all positive slack >3/50; min',min(float(a) for a,b in bounds),flush=True)
for t in ts:
 a,b=interval(t);assert 0<a<b<32
# Uniform norms and Lipschitz constants in the angle variable theta,
# with x=cos(theta): |T_k(cos theta)|<=1 and |d/dtheta T_k(cos theta)|<=k.
coefficient_bounds={}
for name,cc in [('h',h),('v1',v1),('v3',v3),('v5',v5)]:
 abs_upper=[max(abs(a),abs(b)) for a,b in map(interval,cc)]
 norm_bound=sum(abs_upper,F(0))
 angular_bound=sum((k*a for k,a in enumerate(abs_upper)),F(0))
 assert norm_bound<32 and angular_bound<128
 coefficient_bounds[name]={'uniform_bound':'32','angular_lipschitz_bound':'128',
   'computed_norm_upper':str(norm_bound),'computed_angular_upper':str(angular_bound)}
 print(name,'norm < 32; angular Lipschitz constant < 128',flush=True)
assert interval(eta)[1]<0
# Compact exact trigonometric expression for eta.
assert eta==(8*S[2]-13*S[6]-13*S[10])/15
# Closed expression used in the manuscript, with c_j=cos(j*pi/36).
beta_cos_coefficients=[7264892,-16364700,2333622,-20710080,7960924,
                       -8377290,6354480,-6380100,8032814,-667710,24678]
assert 7132971*beta == -21647763 + sum(
    (coefficient*cosn(j) for j,coefficient in enumerate(beta_cos_coefficients,1)),
    E(0))

out={'description':'Exact tangent certificate for normalized Lorentz conjecture 3 prime', 'r':str(r), 'field_variable':'z=2*cos(pi/36)', 'minimal_polynomial':MOD,'root_interval':[str(lo),str(hi)],'h':[v.serialize() for v in h], 'polynomials':[[v.serialize() for v in cc] for cc in polys], 'lambdas':[v.serialize() for v in ts], 'degrees':[2,4,6], 'active':actives,'grid_indices':grids,'signs':signs,'cubic_map':map3,'grid_H':[v.serialize() for v in HF],'slacks':[[v.serialize() for v in ss] for ss in slacks], 'normalization':{'h1':0,'h3':0,'h4':1,'h5':-3},'strict_slack_lower_bound':'3/50','coefficient_bounds':coefficient_bounds}
target=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('odd_certificate.json')
with target.open('w') as fp:json.dump(out,fp,indent=2)
print('Certificate written to', target, flush=True)
print('ALL EXACT FIELD IDENTITIES, ALTERNATIONS, AND RATIONAL INTERVAL SIGNS VERIFIED',flush=True)
print('Total seconds',time.time()-start,flush=True)
