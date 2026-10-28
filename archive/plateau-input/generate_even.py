"""Generate the exact algebraic certificate for Lorentz Conjecture 4.

Optional generation dependency: python-flint (install with
    python -m pip install python-flint
).
The separate verifier checks the saved certificate using standard-library
rational arithmetic; generation is not a trusted proof assumption.

The 27 unknowns are h_1,h_2,h_3,h_4,h_5,h_7,h_8, followed by the
Chebyshev coefficients of v_0,v_2,v_4,v_6 and their four error corrections.
There are 25 contact equations and the normalizations [T_2]v_2=1 and
[T_4]v_4=-1. All elimination pivots are verified nonzero in Q(z).
"""
import json, time
from pathlib import Path
try:
    from flint import fmpq, fmpq_poly
except ImportError as exc:
    raise SystemExit("Generation requires python-flint: python -m pip install python-flint") from exc
from fractions import Fraction as F
start=time.time()
P=fmpq_poly
m12=P([1,0,-36,0,105,0,-112,0,54,0,-12,0,1])
y=P([-2,0,1]); MOD=P(0)
for a in reversed(m12.coeffs()):MOD=MOD*y+a
N=24
class E:
 def __init__(self,a=0):
  if isinstance(a,E):self.p=a.p;return
  if isinstance(a,F):a=fmpq(a.numerator,a.denominator)
  self.p=(a if isinstance(a,P) else P(a if isinstance(a,(tuple,list)) else [a]))%MOD
 def __add__(self,o):return E(self.p+E(o).p)
 __radd__=__add__
 def __neg__(self):return E(-self.p)
 def __sub__(self,o):return E(self.p-E(o).p)
 def __rsub__(self,o):return E(o)-self
 def __mul__(self,o):return E(self.p*E(o).p)
 __rmul__=__mul__
 def inv(self):
  g,s,t=self.p.xgcd(MOD)
  assert g.degree()==0 and g[0]!=0
  return E(s/g[0])
 def __truediv__(self,o):return self*E(o).inv()
 def __rtruediv__(self,o):return E(o)/self
 def __pow__(self,k):
  if k<0:return self.inv()**(-k)
  s=E(1);v=self
  while k:
   if k&1:s=s*v
   v=v*v;k//=2
  return s
 def __bool__(self):return bool(self.p)
 def __eq__(self,o):return self.p==E(o).p
 def serialize(self):return [str(a) for a in self.p.coeffs()]

def solve(A,b):
 n=len(b);A=[[E(x) for x in r]+[E(v)] for r,v in zip(A,b)]
 for i in range(n):
  j=next(j for j in range(i,n) if A[j][i]);A[i],A[j]=A[j],A[i]
  inv=A[i][i].inv()
  for j in range(i+1,n):
   if not A[j][i]:continue
   fac=A[j][i]*inv
   for k in range(i+1,n+1):A[j][k]-=fac*A[i][k]
   A[j][i]=E(0)
  print('pivot',i,'seconds',round(time.time()-start,2),flush=True)
 x=[E(0)]*n
 for i in range(n-1,-1,-1):x[i]=(A[i][n]-sum((A[i][j]*x[j] for j in range(i+1,n)),E(0)))/A[i][i]
 return x
z=E([0,1]);S=[E(2),z]
for k in range(2,73):S.append(z*S[-1]-S[-2])
def cos72(k):
 k%=144
 if k>72:k=144-k
 return S[k]/2
rho=E(F(-3,5));ks=[1,2,3,4,5,7,8]
settings=[(1,12,1),(3,12,1),(5,12,1),(7,36,-1)]
allactive=[[3,6,8],[1,3,4,6,8,10],[0,2,4,6,7,9,11],[3,6,8,13,19,22,27,30,32]]
chosen=[[3,6,8],[1,3,6,8,10],[0,2,4,6,7,9,11],[3,6,8,13,19,22,27,30,32]]
rows=[];b=[];grids={};off=7
for (deg,M,sign),active in zip(settings,allactive):
 J=1 if M==12 else 2
 theta=[(2*M-1-2*j)*(36//M) for j in range(M)]
 sig=[sign*(1 if ((2*M-1-2*j)%8) in [1,7] else -1) for j in range(M)]
 H=[[sum((rho**i*cos72(k*t*3**i) for i in range(J)),E(0))+sum((rho**i*cos72(k*t*3**i) for i in range(J,J+4)),E(0))/(1-rho**4) for k in ks] for t in theta]
 V=[[cos72(k*t) for k in range(deg)] for t in theta]
 erows=[]
 for j in range(M):
  r=[E(0)]*27
  for i,a in enumerate(H[j]):r[i]=sig[j]*a
  for i,a in enumerate(V[j]):r[off+i]=-sig[j]*a
  r[off+deg]=E(-1);erows.append(r)
 for j in active:rows.append(erows[j]);b.append(E(0))
 grids[deg]={'M':M,'signs':sig,'theta':theta,'H':H,'V':V,'erows':erows,'off':off,'J':J}
 off+=deg+1
for i,val in [(11,1),(17,-1)]:
 r=[E(0)]*27;r[i]=E(1);rows.append(r);b.append(E(val))
assert len(rows)==27
print('mod',MOD,'matrixbuilt',time.time()-start,flush=True)
v=solve(rows,b)
assert all(sum((a*c for a,c in zip(r,v)),E(0))==s for r,s in zip(rows,b))
# Isolate largest root by rational bisection; M24(z)=M12(z²−2), strictly increasing on chosen interval.
mc=[F(str(a)) for a in MOD.coeffs()]
def evalq(p,x):
 y=F(0)
 for c in reversed(p):y=y*x+c
 return y
lo=F(999,500);hi=F(2)
assert evalq(mc,lo)<0<evalq(mc,hi)
for _ in range(400):
 mid=(lo+hi)/2
 if evalq(mc,mid)<0:lo=mid
 else:hi=mid

def interval(a):
 low=F(0);high=F(0);lp=F(1);hp=F(1)
 for c0 in a.p.coeffs():
  c=F(str(c0))
  if c>=0:low+=c*lp;high+=c*hp
  else:low+=c*hp;high+=c*lp
  lp*=lo;hp*=hi
 return low,high

def floatval(a):
 l,h=interval(a);return float((l+h)/2)
slacks={};polys={};lambdas={}
for (deg,M,sign),required,chosen0 in zip(settings,allactive,chosen):
 g=grids[deg];sl=[-sum((a*c for a,c in zip(r,v)),E(0)) for r in g['erows']]
 zeros=[i for i,a in enumerate(sl) if not a]
 assert zeros==required,(deg,zeros,required)
 bounds=[interval(a) for a in sl if a]
 assert all(l>0 for l,h in bounds)
 assert all(sl[j]==0 for j in chosen0)
 assert len(chosen0)==deg+2
 assert all(g['signs'][i]==-g['signs'][j] for i,j in zip(chosen0,chosen0[1:]))
 off=g['off'];polys[deg]=v[off:off+deg];lambdas[deg]=v[off+deg];slacks[deg]=sl
 print('degree',deg,'zeros',zeros,'minslack',min(float(a) for a,b in bounds),'poly',[floatval(a) for a in polys[deg]],'lambda',floatval(lambdas[deg]),flush=True)
 assert sum((max(abs(a),abs(b)) for a,b in map(interval,polys[deg])),F(0))<2
 assert sum((k*k*max(abs(a),abs(b)) for k,(a,b) in enumerate(map(interval,polys[deg]))),F(0))<72
 assert max(map(abs,interval(lambdas[deg])))<1
h=[E(0)]*9
for k,a in zip(ks,v[:7]):h[k]=a
assert interval(h[7])[0]>F(1,40)
assert interval(sum((h[k] for k in [1,3,5,7]),E(0)))[0]>F(1,100)
assert sum((max(abs(a),abs(b)) for a,b in map(interval,h)),F(0))<2
assert sum((k*k*max(abs(a),abs(b)) for k,(a,b) in enumerate(map(interval,h))),F(0))<34
print('forcing',[floatval(a) for a in h],flush=True)
# Verify actual series values on both grids by recurrence, not merely a truncated sum.
for deg in [1,7]:
 g=grids[deg]
 for j,t in enumerate(g['theta']):
  # evaluator on any rational grid angle including periodic images
  def HH(t0):
   return sum((h[k]*(sum((rho**i*cos72(k*t0*3**i) for i in range(g['J'])),E(0))+sum((rho**i*cos72(k*t0*3**i) for i in range(g['J'],g['J']+4)),E(0))/(1-rho**4)) for k in range(9)),E(0))
  hv=HH(t);ht=HH(3*t)
  assert hv==sum((h[k]*cos72(k*t) for k in range(9)),E(0))+rho*ht
out={'conjecture':4,'rho':'-3/5','baseline':'G_(3/5)(T6(x))','forcing_degree':8,'field_variable':'z=2*cos(pi/72)','minimal_polynomial':[str(a) for a in MOD.coeffs()],'root_interval':[str(lo),str(hi)],'forcing_chebyshev':[a.serialize() for a in h],'correction_chebyshev':{str(k):[a.serialize() for a in p] for k,p in polys.items()},'error_corrections':{str(k):a.serialize() for k,a in lambdas.items()},'slacks':{str(k):[a.serialize() for a in s] for k,s in slacks.items()},'chosen_alternations':{str(k):a for (k,_,_),a in zip(settings,chosen)},'all_active':{str(k):a for (k,_,_),a in zip(settings,allactive)},'numerical_forcing':[floatval(a) for a in h]}
out['certified_bounds']={'forcing_chebyshev_l1':'2','forcing_derivative_l1':'34','correction_chebyshev_l1':'2','correction_derivative_l1':'72','error_correction_abs':'1','h7_lower':'1/40','odd_endpoint_sum_lower':'1/100'}
out['linear_system_rank']=27
out['normalizations']={'h0':'0','h6':'0','v2_T2':'1','v4_T4':'-1'}
output=Path(__file__).with_name('even_certificate.json')
with output.open('w') as f:json.dump(out,f,indent=2)
print('ALL EXACT FIELD IDENTITIES AND RATIONAL INTERVAL SIGNS VERIFIED',time.time()-start,flush=True)
