"""Independent standard-library audit of Lorentz conjecture 4 certificate.

The generator used FLINT. This verifier instead uses separate Fraction
polynomial arithmetic, reconstructs the invariant grid directly, and sums
the forcing along each finite orbit using its detected eventual period.
"""
from fractions import Fraction as Q
import json
import sys

path=sys.argv[1] if len(sys.argv)>1 else str(__import__('pathlib').Path(__file__).with_name('even_certificate.json'))
data=json.load(open(path))
mod=tuple(map(Q,data['minimal_polynomial']))
N=len(mod)-1
assert N==24 and data['conjecture']==4

def canon(p):
    p=list(p)
    while len(p)>N:
        c=p.pop();off=len(p)-N
        for j in range(N):p[off+j]-=c*mod[j]
    return tuple(p+[Q(0)]*(N-len(p)))
zero=canon([]);one=canon([Q(1)]);z=canon([Q(0),Q(1)])
def add(p,q):return tuple(x+y for x,y in zip(p,q))
def neg(p):return tuple(-x for x in p)
def sub(p,q):return add(p,neg(q))
def scale(p,c):return tuple(x*c for x in p)
def mul(p,q):
    v=[Q(0)]*(2*N-1)
    for i,x in enumerate(p):
        if x:
            for j,y in enumerate(q):
                if y:v[i+j]+=x*y
    return canon(v)
def read(p):return canon(list(map(Q,p)))
def const(x):return scale(one,Q(x))
def psquare(p):
    out=[Q(0)]*(2*len(p)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(p):out[i+j]+=x*y
    return out
def peval(p,x):
    y=Q(0)
    for c in reversed(p):y=y*x+c
    return y

lo,hi=map(Q,data['root_interval'])
S6=[Q(-2),0,9,0,-6,0,1]
S12=psquare(S6);S12[0]-=2
rootpoly=psquare(S12);rootpoly[0]-=3
assert tuple(rootpoly)==mod
assert Q(999,500)<lo<hi<2 and lo*lo>3
assert peval(S6,lo)>0 and peval(S12,lo)>0
assert peval(mod,lo)<0<peval(mod,hi)
# S6'=6z(z^2-1)(z^2-3)>0; S12=S6^2-2 and MOD=S12^2-3.
# Their positivity at lo proves MOD is strictly increasing on [lo,2].

def interval(p):
    l=u=Q(0);xl=xu=Q(1)
    for c in p:
        l+=c*(xl if c>=0 else xu)
        u+=c*(xu if c>=0 else xl)
        xl*=lo;xu*=hi
    return l,u
def absupper(p):
    l,u=interval(p);return max(abs(l),abs(u))

S=[const(2),z]
for k in range(2,72):S.append(sub(mul(z,S[-1]),S[-2]))
X=[scale(S[2*j+1],Q(-1,2)) for j in range(36)]
for j,x in enumerate(X):
    l,u=interval(x)
    assert -1<l<u<1
    if j:assert interval(sub(x,X[j-1]))[0]>0

def chebs(x,n):
    t=[one,x]
    for _ in range(2,n+1):t.append(sub(scale(mul(x,t[-1]),2),t[-2]))
    return t[:n+1]
T=[chebs(x,18) for x in X]
lookup={x:j for j,x in enumerate(X)}
mapping=[lookup[t[3]] for t in T]
assert len(set(X))==36

h=list(map(read,data['forcing_chebyshev']))
assert len(h)==9
def chebeval(coeffs,j):
    out=zero
    for k,c in enumerate(coeffs):out=add(out,mul(c,T[j][k]))
    return out
qvals=[chebeval(h,j) for j in range(36)]
rho=Q(-3,5)
H=[]
for initial in range(36):
    orbit=[];seen={};v=initial
    while v not in seen:
        seen[v]=len(orbit);orbit.append(v);v=mapping[v]
    m=seen[v];p=len(orbit)-m
    out=zero
    for k in range(m):out=add(out,scale(qvals[orbit[k]],rho**k))
    cycle=zero
    for k in range(p):cycle=add(cycle,scale(qvals[orbit[m+k]],rho**k))
    out=add(out,scale(cycle,rho**m/(1-rho**p)))
    H.append(out)
for j in range(36):assert H[j]==add(qvals[j],scale(H[mapping[j]],rho))

assert interval(h[7])[0]>Q(1,40)
odd_sum=zero
for k in range(1,9,2):odd_sum=add(odd_sum,h[k])
assert interval(odd_sum)[0]>Q(1,100)
# At +/-1, the forcing series is h(+/-1)/(1+3/5), so this proves
# f_epsilon(1)-f_epsilon(-1) > epsilon/80 > 0.

M=sum(map(absupper,h),Q(0))
L=sum((k*absupper(c) for k,c in enumerate(h)),Q(0))
assert M<2 and L<34
print('h coefficient sum:',float(M),'; angular derivative sum:',float(L))
print('h:',[float(sum(interval(c))/2) for c in h])
print('endpoint asymmetry coefficient >',float(Q(5,4)*interval(odd_sum)[0]))

eps=Q(1,10**10);gamma=Q(1,8*1296**2)
CI=list(range(1,36,3))
for n in [1,3,5,7]:
    key=str(n)
    v=list(map(read,data['correction_chebyshev'][key]))
    lam=read(data['error_corrections'][key])
    active=data['all_active'][key]
    chosen=data['chosen_alternations'][key]
    ids=CI if n<7 else list(range(36))
    d=6 if n<7 else 18
    A=Q(1) if n<7 else Q(3,5)
    bsign=1 if n<7 else -1
    assert len(ids)==2*d and len(v)<=n
    assert len(chosen)==n+2
    assert all(i<j for i,j in zip(chosen,chosen[1:]))
    signs=[];positive=[];foundactive=[]
    for local,j in enumerate(ids):
        assert mul(T[j][d],T[j][d])==const(Q(1,2))
        l,u=interval(scale(T[j][d],bsign))
        assert l>0 or u<0
        sg=1 if l>0 else -1
        signs.append(sg)
        slack=sub(lam,scale(sub(H[j],chebeval(v,j)),sg))
        assert slack==read(data['slacks'][key][local])
        if slack==zero:foundactive.append(local)
        else:
            low,high=interval(slack)
            assert low>Q(1,50)
            positive.append(low)
    assert foundactive==active
    assert all(j in active for j in chosen)
    assert all(signs[i]==-signs[j] for i,j in zip(chosen,chosen[1:]))
    V=sum(map(absupper,v),Q(0))
    Lv=sum((k*absupper(c) for k,c in enumerate(v)),Q(0))
    lamnorm=absupper(lam)
    assert V<2 and Lv<12 and lamnorm<1
    C=5*M+Q(15,64*d)*L+Q(3,16*d)*Lv
    K=Q(5,2)*M+V
    assert eps*C<=A/Q(4608)
    assert eps*(K+lamnorm)<=A*gamma
    print('n',n,'V',float(V),'Lv',float(Lv),'lambda',float(sum(interval(lam))/2),
          'min slack',float(min(positive)))
    print('  polynomial:',[float(sum(interval(c))/2) for c in v])
    print('  local/global margins:',float(A/Q(4608)-eps*C),
          float(A*gamma-eps*(K+lamnorm)))
print('PASS: independent exact invariant-orbit sums, root isolation, node order,')
print('contact signs, all slack identities, alternations, non-evenness, and')
print('explicit epsilon=10^-10 coefficient bounds and stability inequalities.')
