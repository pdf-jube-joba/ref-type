from ring_certificates import *
from rational_certificates import Scalars
from fractions import Fraction as F

def K(q):return ('const',F(q))
class Poly(Cert):
 def __init__(self,scalars):super().__init__();self.scalars=scalars
 def node(self,e):
  if e[0]=='const':return '(coefficient D.'+self.scalars.lit(e[1])+')'
  return super().node(e)
 def mon(self,vs):
  r=O
  for v in reversed(vs):r=M(V(v),r)
  return r
 def term(self,t):return M(K(t[0]),self.mon(t[1]))
 def scalar(self,op,a,b=None):
  c=a+b if op=='add' else a*b if op=='mul' else -a
  l=(op,K(a)) if b is None else (op,K(a),K(b));r=K(c)
  name=self.scalars.op(op,a,b);qa='D.'+self.scalars.lit(a);qb='D.'+self.scalars.lit(b) if b is not None else ''
  m='coefficientNeg' if op=='neg' else 'coefficientLaws.'+op
  p=f'sym!{{R}} _ _ ({m} {qa} {qb})'
  return self.proof(l,r,f'trans!{{R}} _ _ _ ({p}) (congr!{{Q.Carrier R}} coefficient _ _ D.{name})')
 def coeffzero(self):return self.proof(K(F(0)),Z,'coefficientLaws.zero')
 def coeffone(self):return self.proof(K(F(1)),O,'coefficientLaws.one')
 @lru_cache(None)
 def insvar(self,x,vs):
  xe=V(x)
  if not vs:return (x,),self.refl(M(xe,O))
  y,*tail=vs;tail=tuple(tail);ye=V(y);me=self.mon(tail)
  if x<=y:return (x,)+vs,self.refl(M(xe,self.mon(vs)))
  out,p=self.insvar(x,tail)
  swap=self.chain(self.sym(self.massoc(xe,ye,me)),self.cong('mul',self.mcomm(xe,ye),self.refl(me)),self.massoc(ye,xe,me))
  return (y,)+out,self.chain(swap,self.cong('mul',self.refl(ye),p))
 @lru_cache(None)
 def monmul(self,vs,ws):
  a=self.mon(vs);b=self.mon(ws)
  if not vs:return ws,self.ax('ring.ring.semiring.multiplicative.leftIdentity',M(O,b),b,b)
  x,*tail=vs;tail=tuple(tail);out,p=self.monmul(tail,ws);res,q=self.insvar(x,out)
  return res,self.chain(self.massoc(V(x),self.mon(tail),b),self.cong('mul',self.refl(V(x)),p),q)
 @lru_cache(None)
 def insert(self,t,ts):
  te=self.term(t);s=self.nf(ts)
  if t[0]==0:
   p=self.chain(self.cong('mul',self.coeffzero(),self.refl(self.mon(t[1]))),self.ax('ring.ring.semiring.zeroAbsorbsLeft',M(Z,self.mon(t[1])),Z,self.mon(t[1])))
   return ts,self.chain(self.cong('add',p,self.refl(s)),self.zeroplus(s))
  if not ts:return (t,),self.refl(A(te,s))
  h,*rest=ts;rest=tuple(rest);he=self.term(h);re=self.nf(rest)
  if t[1]<h[1]:return (t,)+ts,self.refl(A(te,s))
  if t[1]==h[1]:
   cf=t[0]+h[0];new=(cf,t[1]);mon=self.mon(t[1])
   comb=self.chain(self.sym(self.ax('ring.ring.semiring.rightDistributive',M(A(K(t[0]),K(h[0])),mon),A(te,he),K(t[0]),K(h[0]),mon)),self.cong('mul',self.scalar('add',t[0],h[0]),self.refl(mon)))
   ps=self.chain(self.sym(self.assoc(te,he,re)),self.cong('add',comb,self.refl(re)))
   if cf==0:
    zs,zp=self.insert(new,rest);return zs,self.chain(ps,zp)
   return (new,)+rest,ps
  out,p=self.insert(t,rest)
  swap=self.chain(self.sym(self.assoc(te,he,re)),self.cong('add',self.comm(te,he),self.refl(re)),self.assoc(he,te,re))
  return (h,)+out,self.chain(swap,self.cong('add',self.refl(he),p))
 @lru_cache(None)
 def termmul(self,t,u):
  a=K(t[0]);b=self.mon(t[1]);c=K(u[0]);d=self.mon(u[1]);vs,pm=self.monmul(t[1],u[1]);cf=t[0]*u[0]
  p=self.chain(self.massoc(a,b,M(c,d)),self.cong('mul',self.refl(a),self.ax('mulSwap',M(b,M(c,d)),M(c,M(b,d)),b,c,d)),self.sym(self.massoc(a,c,M(b,d))))
  return (cf,vs),self.chain(p,self.cong('mul',self.scalar('mul',t[0],u[0]),pm))
 @lru_cache(None)
 def negative(self,ts):
  if not ts:return (),self.ax('Sum.negZero',G(Z),Z)
  t,*tail=ts;tail=tuple(tail);term=self.term(t);qs,q=self.negative(tail);cf=-t[0]
  p=self.chain(self.sym(self.ax('negMulLeft',M(G(K(t[0])),self.mon(t[1])),G(term),K(t[0]),self.mon(t[1]))),self.cong('mul',self.scalar('neg',t[0]),self.refl(self.mon(t[1]))))
  return ((cf,t[1]),)+qs,self.chain(self.ax('Sum.negAdd',G(self.nf(ts)),A(G(term),G(self.nf(tail))),term,self.nf(tail)),self.cong('add',p,q))
 @lru_cache(None)
 def norm(self,e):
  if e==Z:return (),self.refl(Z)
  if e==O:return ((F(1),()),),self.chain(self.sym(self.coeffone()),self.sym(self.ax('ring.ring.semiring.multiplicative.rightIdentity',M(K(F(1)),O),K(F(1)),K(F(1)))),self.sym(self.addzero(self.term((F(1),())))))
  if e[0]=='const':
   if e[1]==0:return (),self.coeffzero()
   t=(e[1],());return (t,),self.chain(self.sym(self.ax('ring.ring.semiring.multiplicative.rightIdentity',self.term(t),e,e)),self.sym(self.addzero(self.term(t))))
  if e[0]=='var':
   t=(F(1),(e[1],));m=self.mon(t[1]);p=self.sym(self.ax('ring.ring.semiring.multiplicative.rightIdentity',m,e,e))
   return (t,),self.chain(p,self.sym(self.ax('ring.ring.semiring.multiplicative.leftIdentity',M(O,m),m,m)),self.cong('mul',self.sym(self.coeffone()),self.refl(m)),self.sym(self.addzero(self.term(t))))
  if e[0]=='neg':
   ts,p=self.norm(e[1]);us,q=self.negative(ts);return us,self.chain(self.cong('neg',p),q)
  ts,p=self.norm(e[1]);us,q=self.norm(e[2]);out,r=self.merge(ts,us) if e[0]=='add' else self.times(ts,us)
  return out,self.chain(self.cong(e[0],p,q),r)
