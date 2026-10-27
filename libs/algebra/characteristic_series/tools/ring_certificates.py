"""Generate explicit equational certificates; every step is checked by ref-type."""
from functools import lru_cache
from pathlib import Path
Z=('zero',); O=('one',)
def A(a,b):return ('add',a,b)
def M(a,b):return ('mul',a,b)
def G(a):return ('neg',a)
def V(s):return ('var',s)
def plus(*xs):
 r=Z
 for x in reversed(xs):r=A(x,r)
 return r
def powr(x,n):
 r=O
 for _ in range(n):r=M(x,r)
 return r
class Cert:
 def __init__(self): self.lines=[];self.nodes={Z:'zero',O:'one'};self.proofs={}
 def node(self,e):
  if e[0]=='var':return e[1]
  if e in self.nodes:return self.nodes[e]
  args=[self.node(a) for a in e[1:]];n='v'+str(len(self.nodes));self.nodes[e]=n
  self.lines.append('\\definition '+n+': R := '+e[0]+' '+' '.join(args)+';');return n
 def proof(self,l,r,body):
  if l==r:return (l,r,None)
  if (l,r) in self.proofs:return self.proofs[l,r]
  ln,rn=self.node(l),self.node(r);name='h'+str(len(self.proofs));self.lines.append(f'\\definition {name}: {ln} = {rn} := {body};');p=(l,r,name);self.proofs[l,r]=p;return p
 def ref(self,p):return p[2] or '\\refl('+self.node(p[0])+')'
 def refl(self,e):return (e,e,None)
 def ax(self,op,l,r,*args):return self.proof(l,r,op+' '+' '.join(self.node(x) for x in args))
 def sym(self,p):return self.proof(p[1],p[0],f'sym!{{R}} _ _ ({self.ref(p)})')
 def chain(self,*ps):
  out=ps[0]
  for q in ps[1:]:
   assert out[1]==q[0],(out[1],q[0])
   if out[0]==out[1]:out=q;continue
   if q[0]==q[1]:continue
   out=self.proof(out[0],q[1],f'trans!{{R}} _ _ _ ({self.ref(out)}) ({self.ref(q)})')
  return out
 def cong(self,op,p,q=None):
  l=(op,p[0]) if q is None else (op,p[0],q[0]);r=(op,p[1]) if q is None else (op,p[1],q[1]);
  if l==r:return self.refl(l)
  b=f'congr!{{R R}} {op} _ _ ({self.ref(p)})' if q is None else f'congr!{{R R R}} {op} _ _ _ _ ({self.ref(p)}) ({self.ref(q)})'
  return self.proof(l,r,b)
 def addzero(self,e):return self.ax('Sum.zeroRight',A(e,Z),e,e)
 def zeroplus(self,e):return self.ax('Sum.zeroLeft',A(Z,e),e,e)
 def assoc(self,a,b,c):return self.ax('Sum.assoc',A(A(a,b),c),A(a,A(b,c)),a,b,c)
 def comm(self,a,b):return self.ax('Sum.comm',A(a,b),A(b,a),a,b)
 def massoc(self,a,b,c):return self.ax('ring.ring.semiring.multiplicative.associative',M(M(a,b),c),M(a,M(b,c)),a,b,c)
 def mcomm(self,a,b):return self.ax('ring.mulCommutative',M(a,b),M(b,a),a,b)
 def term(self,t):
  sg,vs=t;r=O
  for v in reversed(vs):r=M(V(v),r)
  return r if sg==1 else G(r)
 def nf(self,ts):return plus(*(self.term(t) for t in ts))
 def key(self,t):return t[1]
 @lru_cache(None)
 def insert(self,t,ts):
  te=self.term(t);s=self.nf(ts);l=A(te,s)
  if not ts:return (t,),self.refl(l)
  h,*rest=ts;rest=tuple(rest);he=self.term(h);re=self.nf(rest)
  if self.key(t)<self.key(h):return (t,)+ts,self.refl(l)
  if self.key(t)==self.key(h) and t[0]!=h[0]:
   mid=A(A(te,he),re)
   inv=self.ax('Sum.inverseLeft' if t[0]==-1 else 'Sum.inverseRight',A(te,he),Z,self.term((1,t[1])))
   return rest,self.chain(self.sym(self.assoc(te,he,re)),self.cong('add',inv,self.refl(re)),self.zeroplus(re))
  out,p=self.insert(t,rest)
  # t+(h+rest) = h+(t+rest)
  swap=self.chain(self.sym(self.assoc(te,he,re)),self.cong('add',self.comm(te,he),self.refl(re)),self.assoc(he,te,re))
  return (h,)+out,self.chain(swap,self.cong('add',self.refl(he),p))
 @lru_cache(None)
 def merge(self,ts,us):
  if not ts:return us,self.zeroplus(self.nf(us))
  t,*tail=ts;tail=tuple(tail)
  vs,p=self.merge(tail,us);out,q=self.insert(t,vs)
  return out,self.chain(self.assoc(self.term(t),self.nf(tail),self.nf(us)),self.cong('add',self.refl(self.term(t)),p),q)
 @lru_cache(None)
 def insvar(self,x,vs):
  xe=V(x)
  if not vs:return (x,),self.refl(M(xe,O))
  y,*tail=vs;tail=tuple(tail);ye=V(y);me=self.term((1,tail))
  if x<=y:return (x,)+vs,self.refl(M(xe,self.term((1,vs))))
  out,p=self.insvar(x,tail)
  swap=self.chain(self.sym(self.massoc(xe,ye,me)),self.cong('mul',self.mcomm(xe,ye),self.refl(me)),self.massoc(ye,xe,me))
  return (y,)+out,self.chain(swap,self.cong('mul',self.refl(ye),p))
 @lru_cache(None)
 def monmul(self,vs,ws):
  a=self.term((1,vs));b=self.term((1,ws))
  if not vs:return ws,self.ax('ring.ring.semiring.multiplicative.leftIdentity',M(O,b),b,b)
  x,*tail=vs;tail=tuple(tail);out,p=self.monmul(tail,ws);res,q=self.insvar(x,out)
  return res,self.chain(self.massoc(V(x),self.term((1,tail)),b),self.cong('mul',self.refl(V(x)),p),q)
 @lru_cache(None)
 def termmul(self,t,u):
  a=self.term(t);b=self.term(u);posA=self.term((1,t[1]));posB=self.term((1,u[1]));vs,pm=self.monmul(t[1],u[1]);out=(t[0]*u[0],vs)
  p=self.refl(M(a,b))
  if t[0]<0:
   p=self.ax('negMulLeft',M(a,b),G(M(posA,b)),posA,b)
   if u[0]<0:
    q=self.ax('negMulRight',M(posA,b),G(M(posA,posB)),posA,posB)
    p=self.chain(p,self.cong('neg',q),self.ax('Sum.negNeg',G(G(M(posA,posB))),M(posA,posB),M(posA,posB)))
  elif u[0]<0:p=self.ax('negMulRight',M(a,b),G(M(posA,posB)),posA,posB)
  return out,self.chain(p,pm if out[0]>0 else self.cong('neg',pm))
 @lru_cache(None)
 def termtimes(self,t,us):
  te=self.term(t);s=self.nf(us)
  if not us:return (),self.ax('ring.ring.semiring.zeroAbsorbsRight',M(te,Z),Z,te)
  u,*rest=us;rest=tuple(rest);a,p=self.termmul(t,u);bs,q=self.termtimes(t,rest);out,r=self.insert(a,bs)
  return out,self.chain(self.ax('ring.ring.semiring.leftDistributive',M(te,s),A(M(te,self.term(u)),M(te,self.nf(rest))),te,self.term(u),self.nf(rest)),self.cong('add',p,q),r)
 @lru_cache(None)
 def times(self,ts,us):
  a=self.nf(ts);b=self.nf(us)
  if not ts:return (),self.ax('ring.ring.semiring.zeroAbsorbsLeft',M(Z,b),Z,b)
  t,*tail=ts;tail=tuple(tail);ps,p=self.termtimes(t,us);qs,q=self.times(tail,us);out,r=self.merge(ps,qs)
  return out,self.chain(self.ax('ring.ring.semiring.rightDistributive',M(a,b),A(M(self.term(t),b),M(self.nf(tail),b)),self.term(t),self.nf(tail),b),self.cong('add',p,q),r)
 @lru_cache(None)
 def negative(self,ts):
  if not ts:return (),self.ax('Sum.negZero',G(Z),Z)
  t,*tail=ts;tail=tuple(tail);sg,vs=t;term=self.term(t);negterm=self.term((-sg,vs));qs,q=self.negative(tail)
  p=self.refl(G(term)) if sg>0 else self.ax('Sum.negNeg',G(term),negterm,self.term((1,vs)))
  return ((-sg,vs),)+qs,self.chain(self.ax('Sum.negAdd',G(self.nf(ts)),A(G(term),G(self.nf(tail))),term,self.nf(tail)),self.cong('add',p,q))
 @lru_cache(None)
 def norm(self,e):
  if e==Z:return (),self.refl(Z)
  if e==O:return ((1,()),),self.sym(self.addzero(O))
  if e[0]=='var':
   t=(1,(e[1],));m=self.term(t)
   return (t,),self.chain(self.sym(self.ax('ring.ring.semiring.multiplicative.rightIdentity',m,e,e)),self.sym(self.addzero(m)))
  if e[0]=='neg':
   ts,p=self.norm(e[1]);us,q=self.negative(ts);return us,self.chain(self.cong('neg',p),q)
  ts,p=self.norm(e[1]);us,q=self.norm(e[2]);out,r=self.merge(ts,us) if e[0]=='add' else self.times(ts,us)
  return out,self.chain(self.cong(e[0],p,q),r)
 def identity(self,a,b):
  ts,p=self.norm(a);us,q=self.norm(b);assert ts==us,(ts,us)
  return self.chain(p,self.sym(q))
 def write(self,path,a,b):
  p=self.identity(a,b)
  Path(path).write_text('\n'.join(self.lines)+f'\n\\definition equation: {self.node(a)} = {self.node(b)} := {self.ref(p)};\n')
