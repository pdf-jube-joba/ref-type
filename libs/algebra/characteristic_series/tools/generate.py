from pathlib import Path
from functools import lru_cache
from polynomial_certificates import *
BASE=Path('libs/algebra/characteristic_series/src')
scalars=Scalars()
class Scalar(Cert):
 def __init__(self):super().__init__();self.nodes={};self.lines=[]
 def node(self,e):
  if e[0]=='const':return 'D.'+scalars.lit(e[1])
  if e in self.nodes:return self.nodes[e]
  args=[self.node(x) for x in e[1:]];n='v'+str(len(self.nodes));self.nodes[e]=n
  self.lines.append(f'\\definition {n}: Q.Carrier := Q.{e[0]} '+ ' '.join(args)+';');return n
 def proof(self,l,r,body):
  if l==r:return l,r,None
  if (l,r) in self.proofs:return self.proofs[l,r]
  ln,rn=self.node(l),self.node(r);name='h'+str(len(self.proofs));self.lines.append(f'\\definition {name}: {ln} = {rn} := '+body.replace('{R','{Q.Carrier')+';');p=l,r,name;self.proofs[l,r]=p;return p
 def cong(self,op,p,q=None):
  l=(op,p[0]) if q is None else (op,p[0],q[0]);r=(op,p[1]) if q is None else (op,p[1],q[1]);
  if l==r:return self.refl(l)
  b=f'congr!{{Q.Carrier Q.Carrier}} Q.{op} _ _ ({self.ref(p)})' if q is None else f'congr!{{Q.Carrier Q.Carrier Q.Carrier}} Q.{op} _ _ _ _ ({self.ref(p)}) ({self.ref(q)})'
  return self.proof(l,r,b)
 @lru_cache(None)
 def norm(self,e):
  if e[0]=='const':return e[1],self.refl(e)
  if e[0]=='neg':
   a,p=self.norm(e[1]);c=-a
   q=self.proof(G(K(a)),K(c),'D.'+scalars.op('neg',a));return c,self.chain(self.cong('neg',p),q)
  a,p=self.norm(e[1]);b,q=self.norm(e[2]);c=a+b if e[0]=='add' else a*b
  r=self.proof((e[0],K(a),K(b)),K(c),'D.'+scalars.op(e[0],a,b))
  return c,self.chain(self.cong(e[0],p,q),r)
 @lru_cache(None)
 def listproof(self,xs):
  if not xs:return [],'\\refl(S.nil)'
  q,p=self.norm(xs[0]);tail,h=self.listproof(tuple(xs[1:]));left=self.node(xs[0]);right='D.'+scalars.lit(q)
  name='list'+str(len(self.lines));lt=self.listvalue(xs);rt=self.listvalue(tuple(K(x) for x in [q]+tail))
  self.lines.append(f'\\definition {name}: {lt} = {rt} := congr!{{Q.Carrier S.Coefficients S.Coefficients}} S.cons _ _ _ _ ({self.ref(p)}) ({h});')
  return [q]+tail,name
 def listvalue(self,xs):
  r='S.nil'
  for x in reversed(xs):r=f'(S.cons {self.node(x)} {r})'
  return r

def hd(p):return p[0] if p else K(0)
def tl(p):return p[1:] if p else []
def add(n,p,q):return [A(hd(p),hd(q))]+add(n-1,tl(p),tl(q)) if n else []
def scale(n,a,p):return [M(a,hd(p))]+scale(n-1,a,tl(p)) if n else []
def times(n,p,q):return [M(hd(p),hd(q))]+add(n-1,scale(n-1,hd(p),tl(q)),times(n-1,tl(p),q)) if n else []
def inv(n,u):return [K(1)]+scale(n-1,G(K(1)),times(n-1,u,inv(n-1,u))) if n else []
def fac(k):
 r=K(1)
 for n in range(1,k+1):r=M(r,K(F(1,n)))
 return r
def alt(k,a):
 for _ in range(k):a=G(a)
 return a
def powe(a,k):
 r=K(1)
 for _ in range(k):r=M(a,r)
 return r
n=5
ch=[fac(k) for k in range(n)]
todd=inv(n,[alt(k,fac(k+1)) for k in range(1,n+1)])
sinh=[fac(k+1) if k%2==0 else K(0) for k in range(1,n+1)]
l=times(n,[fac(k) if k%2==0 else K(0) for k in range(n)],inv(n,sinh))
ahat=inv(n,[M(powe(K(F(1,2)),k),fac(k+1) if k%2==0 else K(0)) for k in range(1,n+1)])
s=Scalar();public=[]
for name,table in [('ch',ch),('todd',todd),('l',l),('ahat',ahat)]:
 vals,h=s.listproof(tuple(table));expected={'ch':[1,1,F(1,2),F(1,6),F(1,24)],'todd':[1,F(1,2),F(1,12),0,F(-1,720)],'l':[1,0,F(1,3),0,F(-1,45)],'ahat':[1,0,F(-1,24),0,F(7,5760)]}[name];assert vals==expected,(name,vals)
 public.append(f'\\definition {name}Coefficients: S.Coefficients := '+s.listvalue(tuple(K(v) for v in vals))+';')
 public.append(f'\\definition {name}ThroughEight: {name} D.n5 = {name}Coefficients := {h};')
header=r'''/* Explicit rational arithmetic certificates for cohomological degrees through eight. */
\import Q.Computed[] \as D;
'''
(BASE/'Characteristic/Tables.ref').write_text(header+'\n'.join(s.lines+public)+'\n')
scalars.write(BASE/'Rational/Computed.ref')
print('scalar lemmas',len(scalars.ops),'table certificate lines',len(s.lines))
# Universal root-addition certificates, with rational coefficients carried by a ring map.
e=[O]+[V('e'+str(k)) for k in range(1,5)]
x=V('x')
sq=lambda a:M(a,a)
T=[O,M(K(F(1,2)),e[1]),M(K(F(1,12)),A(sq(e[1]),e[2])),M(K(F(1,24)),M(e[1],e[2])),
 M(K(F(1,720)),plus(G(powe(e[1],4)),M(K(4),M(sq(e[1]),e[2])),M(K(3),sq(e[2])),M(e[1],e[3]),G(e[4])))]
LL=[O,Z,M(K(F(1,3)),e[1]),Z,M(K(F(1,45)),A(M(K(7),e[2]),G(sq(e[1]))))]
AA=[O,Z,M(K(F(-1,24)),e[1]),Z,M(K(F(1,5760)),A(M(K(7),sq(e[1])),G(M(K(4),e[2]))))]
CH=[Z,e[1],M(K(F(1,2)),A(sq(e[1]),G(M(K(2),e[2])))),
 M(K(F(1,6)),plus(powe(e[1],3),G(M(K(3),M(e[1],e[2]))),M(K(3),e[3]))),
 M(K(F(1,24)),plus(powe(e[1],4),G(M(K(4),M(sq(e[1]),e[2]))),M(K(2),sq(e[2])),M(K(4),M(e[1],e[3])),G(M(K(4),e[4]))))]

def subst(a,env):
 if a[0]=='var':return env.get(a[1],a)
 if a[0] in ['const','zero','one']:return a
 return (a[0],)+tuple(subst(b,env) for b in a[1:])
def rtimes(n,p,q):
 def h(p):return p[0] if p else Z
 if n==0:return []
 def rscale(n,a,p):return [M(a,h(p))]+rscale(n-1,a,p[1:]) if n else []
 def rplus(n,p,q):return [A(h(p),h(q))]+rplus(n-1,p[1:],q[1:]) if n else []
 return [M(h(p),h(q))]+rplus(n-1,rscale(n-1,h(p),q[1:]),rtimes(n-1,p[1:],q))
def rvalue(p,arr):
 r='S.nil'
 for a in reversed(arr):r=f'(S.cons {p.node(a)} {r})'
 return r

def listIdentity(p,left,right,name):
 proofs=[p.identity(a,b) for a,b in zip(left,right)]
 out='\\refl(S.nil)'
 for q in reversed(proofs):out=f'congr!{{R S.Coefficients S.Coefficients}} S.cons _ _ _ _ ({p.ref(q)}) ({out})'
 p.lines.append(f'\\definition {name}: {rvalue(p,left)} = {rvalue(p,right)} := {out};')

mods=[]
for family,formula,table,pontryagin in [
 ('Todd',T,[1,F(1,2),F(1,12),0,F(-1,720)],False),
 ('L',LL,[1,0,F(1,3),0,F(-1,45)],True),
 ('Ahat',AA,[1,0,F(-1,24),0,F(7,5760)],True)]:
 p=Poly(scalars)
 power=O;factor=[]
 for c in table:factor.append(M(K(c),power));power=M(x,power)
 y=sq(x) if pontryagin else x
 changed={'e'+str(i):A(e[i],M(y,e[i-1])) for i in range(1,5)}
 new=[subst(a,changed) for a in formula]
 listIdentity(p,rtimes(5,factor,formula),new,'step')
 empty=[subst(a,{'e'+str(i):Z for i in range(1,5)}) for a in formula]
 listIdentity(p,empty,[O,Z,Z,Z,Z],'empty')
 # Public formula and its value after adding a root.
 p.lines.append('\\definition formula: S.Coefficients := '+rvalue(p,formula)+';')
 p.lines.append('\\definition next: S.Coefficients := '+rvalue(p,new)+';')
 path=BASE/'PolynomialCalculation'/f'{family}.ref';path.write_text('/* Generated by tools/generate.py; checked equational certificates. */\n'+'\n'.join(p.lines)+'\n')
 mods.append(f'\\module {family}(x, e1, e2, e3, e4: R);')
 print(family,'certificate lines',len(p.lines))
# Additive Chern character coefficients: the constant coefficient is the rank.
p=Poly(scalars)
new=[subst(a,{'e'+str(i):A(e[i],M(x,e[i-1])) for i in range(1,5)}) for a in CH]
for k in range(1,5):
 rp=O
 for _ in range(k):rp=M(x,rp)
 q=p.identity(A(M(K(F(1, __import__('math').factorial(k))),rp),CH[k]),new[k]);p.lines.append(f'\\definition step{k}: {p.node(q[0])} = {p.node(q[1])} := {p.ref(q)};')
for k in range(1,5):
 q=p.identity(subst(CH[k],{'e'+str(i):Z for i in range(1,5)}),Z);p.lines.append(f'\\definition empty{k}: {p.node(q[0])} = zero := {p.ref(q)};')
for k in range(1,5):p.lines.append(f'\\definition coefficient{k}: R := {p.node(CH[k])};')
(BASE/'PolynomialCalculation/Ch.ref').write_text('/* Generated by tools/generate.py; checked equational certificates. */\n'+'\n'.join(p.lines)+'\n');mods.append('\\module Ch(x, e1, e2, e3, e4: R);')
print('Ch certificate lines',len(p.lines))
f=BASE/'PolynomialCalculation.ref';src=f.read_text().split('\\module Example')[0].split('\\import \\root.Series')[0];f.write_text(src+'\\import \\root.Series[R := R, ring := ring] \\as S;\n'+'\n'.join(mods)+'\n')
(BASE/'PolynomialCalculation/Example.ref').unlink(missing_ok=True)
scalars.write(BASE/'Rational/Computed.ref')
print('all scalar operations',len(scalars.ops))
