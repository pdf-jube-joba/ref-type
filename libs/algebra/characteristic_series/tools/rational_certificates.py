from fractions import Fraction
from pathlib import Path
from math import lcm,gcd
class Scalars:
 def __init__(self):
  self.lines=[r'\import std.Data[].Nat[] \as N;',r'\import N.Basic[].Def[] \as NO;',r'\import std.Arithmetic[].Int[] \as I;',r'\import std.Logic[].Equality[] \as E;',r'\use E.trans;',r'\use E.congr;',r'\use E.sym;'];self.ns={0:'N.Nat^::zero'};self.qs={};self.ops={}
 def nat(self,n):
  if n in self.ns:return self.ns[n]
  v=self.nat(n//2);name='n'+str(n);rhs=f'NO.add {v} {v}' if n%2==0 else f'N.Nat^::succ (NO.add {v} {v})';self.lines.append(f'\\definition {name}: N.Nat^ := {rhs};');self.ns[n]=name;return name
 def integer(self,n):return f'I.Int^::ofNat {self.nat(n)}' if n>=0 else f'I.Int^::negSucc {self.nat(-n-1)}'
 def fraction(self,q):return f'(F.Fraction::# ({self.integer(q.numerator)}) {self.nat(q.denominator-1)})'
 def lit(self,q):
  q=Fraction(q)
  if q in self.qs:return self.qs[q]
  name='q'+('m' if q<0 else '')+str(abs(q.numerator))+'d'+str(q.denominator)
  f=self.fraction(q);self.lines.append(f'\\definition {name}: Carrier := Q.class {f};');self.qs[q]=name;return name
 def op(self,op,a,b=None):
  a=Fraction(a);b=Fraction(b) if b is not None else None;key=(op,a,b)
  if key in self.ops:return self.ops[key]
  c=a+b if op=='add' else a*b if op=='mul' else -a
  x=self.lit(a);y=self.lit(b) if b is not None else '';z=self.lit(c);fa=self.fraction(a);fb=self.fraction(b) if b is not None else '';fc=self.fraction(c)
  fo='Q.addFraction' if op=='add' else 'Q.mulFraction' if op=='mul' else 'Q.negFraction'
  cl='Q.addRatClass' if op=='add' else 'Q.mulRatClass' if op=='mul' else 'Q.negClass'
  fe=f'({fo} {fa} {fb})'
  # Reduce the integer cross-product; the checker verifies this certificate.
  proof=f'trans!{{Carrier}} _ _ _ ({cl} {fa} {fb}) (classEqual {fe} {fc} (\\refl(I.mulInteger ({fe}.numerator) (F.denominator {fc}))))'
  if op=='mul':
   g=gcd(abs(a.numerator*b.numerator),a.denominator*b.denominator)
   ki='('+self.integer(g)+')'
   hn=f'\\refl(I.mulInteger ({fc}.numerator) {ki})'
   hd=f'trans!{{I.Integer}} _ _ _ (FL.denominatorMul {fa} {fb}) (\\refl(I.mulInteger (F.denominator {fa}) (F.denominator {fb})))'
   proof=f'trans!{{Carrier}} _ _ _ ({cl} {fa} {fb}) (sym!{{Carrier}} _ _ (scaleClass {fc} {fe} {ki} ({hn}) ({hd})))'
  if op=='neg':
   proof=f'trans!{{Carrier}} _ _ _ (Q.negClass {fa}) (classEqual {fe} {fc} (FL.fractionEqOfNumeratorDenominator {fe} {fc} (\\refl({fc}.numerator)) (\\refl(F.denominator {fc}))))'
  if op=='add':
   den=lcm(a.denominator,b.denominator)
   na=a.numerator*(den//a.denominator);nb=b.numerator*(den//b.denominator);ns=na+nb
   def raw(num,d):return f'(F.Fraction::# ({self.integer(num)}) {self.nat(d-1)})'
   ra,rb,rs=raw(na,den),raw(nb,den),raw(ns,den)
   def scaling(fr,ft,k):
    ki='('+self.integer(k)+')'
    return f'scaleClass {fr} {ft} {ki} (\\refl(I.mulInteger ({fr}.numerator) {ki})) (\\refl(I.mulInteger (F.denominator {fr}) {ki}))'
   pa=scaling(fa,ra,den//a.denominator);pb=scaling(fb,rb,den//b.denominator)
   pc=scaling(fc,rs,den//c.denominator)
   sm=f'addSameDenominator ({self.integer(na)}) ({self.integer(nb)}) {self.nat(den-1)}'
   proof=f'trans!{{Carrier}} _ _ _ (congr!{{Carrier Carrier Carrier}} add _ _ _ _ ({pa}) ({pb})) (trans!{{Carrier}} _ _ _ ({sm}) (sym!{{Carrier}} _ _ ({pc})))'
  name='c'+str(len(self.ops));self.lines.append(f'\\definition {name}: {op} {x} {y} = {z} := {proof};');self.ops[key]=name;return name
 def write(self,p):Path(p).write_text('\n'.join(self.lines)+'\n')
if __name__=='__main__':
 s=Scalars();s.op('mul',Fraction(1,2),Fraction(1,2));s.op('add',Fraction(1,6),Fraction(-1,4));s.write('libs/algebra/characteristic_series/src/Rational/Computed.ref')
