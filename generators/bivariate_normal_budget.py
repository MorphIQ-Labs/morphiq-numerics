#!/usr/bin/env python3
"""Enclosure data and per-rule budget lemmas of the low-correlation branch
(formal/bivariate/BvnData.v, BvnBudget.v; docs/bivariate_normal_budget.md).
Decimal arithmetic only (no mpmath). With --check, fails if a committed file
differs from a fresh generation."""
import sys, pathlib
from decimal import Decimal as D, getcontext
import math
ROOT = pathlib.Path(__file__).resolve().parents[1]
getcontext().prec = 60
ORDERS = {6:("0.2","0.2019"),8:("0.38","0.3903"),
          12:("0.66","0.7214"),14:("0.75","0.8486"),20:("0.89","1.0979"),24:("0.925","1.1816")}
U = D(2)**-53
Z = D(2)**-1075
ETAK = D(17)/D(10)**17
PI = D("3.14159265358979323846264338327950288419716939937510582097494")
def dsin(x):
    t=x; s=x; n=1
    while abs(t) > D(10)**-55:
        t = -t*x*x/((2*n)*(2*n+1)); s += t; n+=1
    return s
def legendre(n,x):
    p0,p1=D(1),x
    for k in range(2,n+1): p0,p1=p1,((2*k-1)*x*p1-(k-1)*p0)/k
    return p1,p0
def rule(n):
    xs=[];ws=[]
    for i in range(1,n//2+1):
        x=D(math.cos(math.pi*(i-0.25)/(n+0.5)))
        for _ in range(60):
            p,q=legendre(n,x); dp=n*(x*p-q)/(x*x-1); step=p/dp; x-=step
            if abs(step)<D(10)**-50: break
        p,q=legendre(n,x); dp=n*(x*p-q)/(x*x-1)
        xs.append(x); ws.append(2/((1-x*x)*dp*dp))
    return xs,ws
def psi(eta): return (1+eta)*(1+2000*U*U)*(1+U)*(1+U)-1
def bp(eta): return (1+psi(eta))*(1+U)**3*Z.exp()-1
def theta_of(A,tauhi,k):
    dth=U*A*(tauhi+D("0.76")); sg=dsin(A*tauhi+dth)
    hs=(1+D(2)**-100)*D(2)**(k-54)
    eps1=(dth+hs)/(1-(sg+hs))
    return eps1+(1+eps1)*D("7.1")*U, sg
def Gsup(b,th,nu):
    if nu*b<=th: return th/nu*(nu*b/th-1).exp(), True
    return b, False
def up(x,digits=30):
    q=D(10)**-digits
    return (x/q).to_integral_value(rounding="ROUND_CEILING")*q
def dn(x,digits=30):
    q=D(10)**-digits
    return (x/q).to_integral_value(rounding="ROUND_FLOOR")*q
def data(N):
    L,A=ORDERS[N]; A=D(A)
    xs,ws=rule(N)
    out=[]
    for x,w in zip(xs,ws):
        for sgn in (1,-1):
            tau=(sgn*x+1)/2
            taulo=dn(tau - D(10)**-40); tauhi=up(tau + D(10)**-40)
            whi=up(w*(1+D(10)**-40))
            th0,sg=theta_of(A,tauhi,0)
            k=0
            while sg>D(2)**k and k>-60: k-=1  # find largest k? we want smallest 2^k >= sg
            # smallest k with sg <= 2^k
            k=0
            while D(2)**(k-1)>=sg: k-=1
            th,sg=theta_of(A,tauhi,k)
            nu=1-th
            G,br=Gsup(D(62)/D(10)**17,th,nu)
            out.append(dict(sgn=sgn,taulo=taulo,tauhi=tauhi,whi=whi,k=k,br=br,theta=th,G=G,sg=sg))
    return A,out

HEAD = '''(** Per-rule certificates of the low-correlation branch: the enclosure data
    satisfy the node lemmas' conditions, the per-node suprema, the truncation
    bound and the angle's rounding sum to the bound stated in [low_N]. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig BvnLow BvnSum BvnQuadG BvnTail BvnRule BvnIntegral BvnFinal BvnTop BvnLowRule BvnEllipse BvnRules BvnData.
Open Scope R_scope.

Ltac dat_goals :=
  unfold dat_ok, theta_of, sgs_of, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  repeat split; try lia; interval with (i_prec 64).
Ltac all_dats := repeat (apply List.Forall_cons; [dat_goals |]); apply List.Forall_nil.
Ltac br_goals :=
  unfold br_ok, theta_of, B0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  split; intros Hbr; first [discriminate Hbr | interval with (i_prec 64)].
Ltac all_brs := repeat (apply List.Forall_cons; [br_goals |]); apply List.Forall_nil.
Ltac sum_goal :=
  unfold gcl, theta_of, B0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl; interval with (i_prec 64).
'''


def lit(x, digits=30):
    q = x * D(10)**digits
    n = int(q)
    assert D(n) == q, (x,)
    return f"({n} / 10 ^ {digits})"
def rlit(x):
    return lit(x,30)
def emit(rules):
    out=[]
    out.append('''(** Enclosure data of the Gauss-Legendre rules of the low-correlation table, written by
    generators/bivariate_normal_budget.py; do not edit. Per node, in the order of
    [tables.rs] (the positive abscissa, then its mirror): bounds on
    [tau = (sign x + 1)/2], an upper bound on the weight, the binade [2^k] above the
    largest sine of the node's angle, and which branch of the per-node supremum
    applies. Each enclosure carries the 120-digit root of [P_n] with a margin of [10^-40]
    before rounding outward to [10^-30]. *)
From Coq Require Import Reals ZArith List.
Import ListNotations.
Require Import BvnRule.
Open Scope R_scope.
''')
    for N in rules:
        A,dat=data(N)
        out.append(f"Definition dats_{N} : list Dat := [")
        parts=[]
        for o in dat:
            parts.append(f"  mkD {rlit(o['taulo'])} {rlit(o['tauhi'])} {rlit(o['whi'])} ({o['k']})%Z {'true' if o['br'] else 'false'}")
        out.append(' ;\n'.join(parts))
        out.append("].\n")
    return '\n'.join(out)

RHO={4:"768/10",6:"202/10",8:"99/10",10:"638/100",12:"473/100",14:"382/100",16:"325/100",20:"259/100",24:"222/100"}
RHOD={4:D("76.8"),6:D("20.2"),8:D("9.9"),10:D("6.38"),12:D("4.73"),14:D("3.82"),16:D("3.25"),20:D("2.59"),24:D("2.22")}
LIM={4:"55/1000",6:"2/10",8:"38/100",10:"54/100",12:"66/100",14:"75/100",16:"81/100",20:"89/100",24:"925/1000"}
KA={4:-4,6:-2,8:-1,10:0,12:0,14:0,16:0,20:1,24:1}
B0=D(62)/D(10)**17
EP=D(2)**-54+D(2)**-112
def G(th):
    nu=1-th
    return th/nu*(nu*B0/th-1).exp() if nu*B0<=th else B0
def sci(x,sig=3):
    # round up to sig digits, return (mantissa int, exponent) as Coq literal m / 10^e
    e=0; y=x
    while y<D(10)**(sig-1): y*=10; e+=1
    m=int(y.to_integral_value(rounding="ROUND_CEILING"))
    return m,e
def lit3(x,sig=3):
    m,e=sci(x,sig); return f"{m} / 10 ^ {e}", D(m)/D(10)**e
out=[HEAD]
res={}
for N in ORDERS:
    A,dat=data(N)
    S=0
    for o in dat:
        th,sg=theta_of(A,o['tauhi'],o['k']); S+=o['whi']*G(th)
    E=A/(4*PI)*S*D("1.03")
    El,Ev=lit3(E)
    r=RHOD[N]; Tr=(A/2)*D(64)/(15*(1-1/(r*r))*r**(2*N))
    Tl,Tv=lit3(Tr/(2*PI)*D("1.03"))
    Sl,Sv=lit3((D(2)**(KA[N]-54)+D(2)**-62*D(2)**KA[N])/(2*PI)*D("1.03"))
    tot=D(2)**-54+D(2)**-900+D(2)**-90+2*EP+Ev+200*Z+Tv+Sv
    Bl,Bv=lit3(tot*D("1.005"),3)
    res[N]=Bv
    a={4:"556/10000",6:"2019/10000",8:"3903/10000",10:"571/1000",12:"7214/10000",14:"8486/10000",16:"9447/10000",20:"10979/10000",24:"11816/10000"}[N]
    out.append(f'''
Lemma dat_ok_{N} : List.Forall (dat_ok A{N}) dats_{N}.
Proof. unfold dats_{N}. all_dats. Qed.
Lemma br_ok_{N} : List.Forall (br_ok A{N} B0) dats_{N}.
Proof. unfold dats_{N}. all_brs. Qed.
Lemma sum_{N} : A{N} / (4 * PI) * sumD (gcl A{N} B0) dats_{N} <= {El}.
Proof. unfold dats_{N}. simpl. unfold A{N}. sum_goal. Qed.
Lemma trunc_{N} : trunc_bound A{N} R{N} {N} / (2 * PI) <= {Tl}.
Proof. unfold trunc_bound, A{N}, R{N}. interval with (i_prec 64). Qed.
Lemma shift_{N} : (bpow radix2 ({KA[N]} - 54) + bpow radix2 (-62) * bpow radix2 ({KA[N]})) / (2 * PI) <= {Sl}.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_{N} : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + ({El}) + 200 * z + ({Tl}) + ({Sl}) <= {Bl}.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_{N} (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= {LIM[N]} -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A{N} (rndF (asr / (2 * TAU)))) nodes dats_{N} -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A{N} R{N} {N} ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= {Bl}.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A{N} >= {LIM[N]} + 2 / 10000) by (destruct (asin_cover_{N}) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr ({LIM[N]}) A{N} (trunc_bound A{N} R{N} {N})
    ({El}) ({Tl}) ({Sl}) ({Bl}) ({KA[N]})%Z pxI pyI Phix Phiy nodes dats_{N}
    Hexp Hsin ltac:(lra) ltac:(unfold A{N}; lra) ltac:(unfold A{N}; lra) ltac:(lia) ltac:(lia) ltac:(unfold A{N}; simpl; lra)
    dat_ok_{N} br_ok_{N} sum_{N} ltac:(lra) trunc_{N} shift_{N} bd_{N}
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.
''')
BUDGET=''.join(out)


def data_file():
    return emit(list(ORDERS))
def main():
    files={'BvnData.v':data_file(),'BvnBudget.v':BUDGET}
    for name,text in files.items():
        p=ROOT/'formal/bivariate'/name
        if '--check' in sys.argv[1:]:
            if p.read_text()!=text: sys.exit(f'{p} differs from a fresh generation')
        else: p.write_text(text)
if __name__=="__main__": main()
