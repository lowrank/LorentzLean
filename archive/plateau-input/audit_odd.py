"""Independent exact audit of the odd plateau certificate.

Uses only Python's standard library, a separate polynomial-arithmetic
implementation, and the serialized certificate. No numerical solver or
candidate-generation routine is imported.
"""
from fractions import Fraction as Q
import json
import sys

path = sys.argv[1] if len(sys.argv)>1 else str(__import__('pathlib').Path(__file__).with_name('odd_certificate.json'))
data = json.load(open(path))
mod = tuple(map(Q,data['minimal_polynomial']))
N=len(mod)-1

def canon(p):
    p=list(p)
    while len(p)>N:
        c=p.pop()
        off=len(p)-N
        for j in range(N): p[off+j]-=c*mod[j]
    p += [Q(0)]*(N-len(p))
    return tuple(p)

zero=canon([])
one=canon([Q(1)])
z=canon([Q(0),Q(1)])

def add(p,q):return tuple(x+y for x,y in zip(p,q))
def neg(p):return tuple(-x for x in p)
def sub(p,q):return add(p,neg(q))
def scale(p,c):return tuple(x*c for x in p)
def mul(p,q):
    v=[Q(0)]*(2*N-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):v[i+j]+=x*y
    return canon(v)
def read(p):return canon(list(map(Q,p)))
def const(x):return scale(one,Q(x))

S=[const(2),z]
for k in range(2,36):S.append(sub(mul(z,S[-1]),S[-2]))
X=[scale(S[2*j+1],Q(-1,2)) for j in range(18)]

lo,hi=map(Q,data['root_interval'])
def interval(p):
    l=u=Q(0)
    xl=xu=Q(1)
    for c in p:
        l+=c*(xl if c>=0 else xu)
        u+=c*(xu if c>=0 else xl)
        xl*=lo;xu*=hi
    return l,u
def absupper(p):
    l,u=interval(p)
    return max(abs(l),abs(u))
def peval(p,x):
    y=Q(0)
    for c in reversed(p):y=y*x+c
    return y

# Root isolation: MOD=S6^2-3 and S6'=6z(z^2-1)(z^2-3)>0
# on (1.98,2). Thus a sign bracket there contains exactly one root.
S6=[Q(-2),0,9,0,-6,0,1]
sq=[Q(0)]*13
for i,c in enumerate(S6):
    for j,d in enumerate(S6):sq[i+j]+=c*d
sq[0]-=3
assert tuple(sq)==mod
assert Q(198,100)<lo<hi<2 and lo*lo>3
assert peval(S6,lo)>0 and peval(mod,lo)<0<peval(mod,hi)

for j,x in enumerate(X):
    l,u=interval(x)
    assert -1<l<u<1
    if j:assert interval(sub(x,X[j-1]))[0]>0

def chebs(x,n):
    t=[one,x]
    for _ in range(2,n+1):t.append(sub(scale(mul(x,t[-1]),2),t[-2]))
    return t[:n+1]
T=[chebs(x,9) for x in X]

r=Q(3,5)
h=list(map(read,data['h']))
V=[list(map(read,row)) for row in data['polynomials']]
lam=list(map(read,data['lambdas']))
H=list(map(read,data['grid_H']))
mapping=data['cubic_map']

def chebeval(coeffs,j):
    out=zero
    for k,c in enumerate(coeffs):out=add(out,mul(c,T[j][k]))
    return out

for j in range(18):
    assert T[j][3]==X[mapping[j]]
    # This finite equation uniquely determines the values of the actual
    # uniformly convergent orbit series on this invariant finite grid.
    assert add(H[j],scale(H[mapping[j]],r))==chebeval(h,j)

h_at_zero=zero
for k in range(0,len(h),2):h_at_zero=add(h_at_zero,scale(h[k],(-1)**(k//2)))
assert h_at_zero==zero
assert h[4]==one and h[1]==zero and h[3]==zero and h[5]==const(-3)
assert interval(h[0])[1]<-4

M=sum(map(absupper,h),Q(0))
L=sum((k*absupper(c) for k,c in enumerate(h)),Q(0))
assert M<32 and L<128
print('h coefficient sum:',float(M),'; angular derivative sum:',float(L))
print('h:',[float(sum(interval(c))/2) for c in h])

eps=Q(1,10**10)
gamma=Q(1,8*1296**2)
allmin=[]
for k,(n,v,t,ids,signs,active) in enumerate(zip(
        data['degrees'],V,lam,data['grid_indices'],data['signs'],data['active'])):
    d=3 if n==2 else 9
    A=Q(1) if n==2 else r
    baselinesign=1 if n==2 else -1
    assert len(ids)==2*d
    assert len(v)<=n and len(active)==n+2  # degree(v)<=n-1
    assert all(i<j for i,j in zip(active,active[1:]))
    assert all(signs[i]==-signs[j] for i,j in zip(active,active[1:]))
    slacks=[]
    for local,j in enumerate(ids):
        assert mul(T[j][d],T[j][d])==const(Q(1,2))
        l,u=interval(scale(T[j][d],baselinesign*signs[local]))
        assert l>0
        s=sub(t,scale(sub(H[j],chebeval(v,j)),signs[local]))
        assert s==read(data['slacks'][k][local])
        if local in active:assert s==zero
        else:
            lower,upper=interval(s)
            assert lower>Q(3,50)
            slacks.append(lower)
    vnorm=sum(map(absupper,v),Q(0))
    vlip=sum((j*absupper(c) for j,c in enumerate(v)),Q(0))
    tnorm=absupper(t)
    assert vnorm<32 and vlip<128 and tnorm<32
    assert interval(t)[0]>0
    C=5*M+Q(15,64*d)*L+Q(3,16*d)*vlip
    K=Q(5,2)*M+vnorm
    assert eps*C<=A/Q(4608)
    assert eps*(K+tnorm)<=A*gamma
    print('n',n,'V',float(vnorm),'Lv',float(vlip),'lambda',float(tnorm),
          'min slack',float(min(slacks)))
    print('  polynomial:',[float(sum(interval(c))/2) for c in v])
    print('  local/global margins:',float(A/Q(4608)-eps*C),
          float(A*gamma-eps*(K+tnorm)))
    allmin.extend(slacks)

print('PASS: independent exact identities, ordering, signs, alternations,')
print('coefficient bounds, nonoddness, normalization, and epsilon=10^-10 bounds.')
