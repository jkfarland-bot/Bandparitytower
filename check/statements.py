# Numerical check of the Lean statements, exactly as formalized.
import cmath, math
from sympy import primerange, primitive_root, legendre_symbol as _leg
def leg(n,p): return int(_leg(n%p,p)) if n%p else 0
def s(x,p): return -1 if (x%p)%2 else 1
def band(x,p,e=2): return ((x%p)**e)//p
def v2(n): return (n & -n).bit_length()-1
def inv(x,p): return pow(x,p-2,p)
fails={}
def F(name): fails[name]=fails.get(name,0)+1
def quartic(p):
    # chi(n)=i^j, n^{(p-1)/4} = g^{j(p-1)/4}; returns dict n->complex int pair
    g=primitive_root(p); I=pow(g,(p-1)//4,p)
    pw={pow(I,j,p):j for j in range(4)}
    return {n:[1,1j,-1,-1j][pw[pow(n,(p-1)//4,p)]] for n in range(1,p)}
def pinned(p):
    c=quartic(p)
    if c[2]==1j: return c
    return {n:c[n].conjugate() for n in c}
for p in primerange(3,1500):
    a=v2(p-1); m=(p-1)>>a
    Ha=[x for x in range(1,p) if pow(x,m,p)==1]
    # Cor 4.4
    fa=sum(s(u,p)*s(u*u,p) for u in Ha)
    if (fa-m)%4: F('tower')
    bandform=sum((1 if pow(n,m,p)==1 else -1)*(-1)**band(n,p) for n in range(1,(p+1)//2) if pow(n,2*m,p)==1)
    if bandform!=fa: F('towerband')
    # Thm 4.3
    g=primitive_root(p); K=2**(a-1); zeta=cmath.exp(2j*math.pi/2**a)
    ind={pow(g,j,p):j for j in range(p-1)}
    for e in (2,4,6):
        lhs=sum(zeta**ind[n]*(-1)**band(n,p,e) for n in range(1,(p+1)//2))
        rhs=0
        for r in range(K):
            X={g**r*h%p for h in Ha}
            T=sum((1 if n in X else -1)*(-1)**band(n,p,e) for n in range(1,(p+1)//2) if n in X or (p-n) in X)
            Y={pow(x,e,p) for x in X}
            if (T-(m-2*sum(1 for x in X if x%2)-2*sum(1 for y in Y if y%2)))%4: F('cyclo_cong')
            rhs+=zeta**r*T
        if abs(lhs-rhs)>1e-6: F('cyclo_eq')
    if p%4!=1: continue
    twoH=[2*h%p for h in Ha]
    ea=sum(s(u,p)*s(u*u,p) for u in twoH)
    Na=sum(1 for n in range(1,p) if 4*n<p and any(pow(y,2**(a-1),p)==n for y in range(1,p)))
    if (ea-(2*Na-m))%4: F('elaw')
    if sum(s(u,p)*s(2*u,p) for u in twoH)!=2*Na-m: F('lag2')
    eband=sum((1 if pow(n*inv(2,p),m,p)==1 else -1)*(-1)**band(n,p) for n in range(1,(p+1)//2) if pow(n*inv(2,p),2*m,p)==1)
    if eband!=ea: F('eband')
    kappa=sum(leg(n,p) for n in range(1,p) if 4*n<p)
    if p%16==9:
        c=quartic(p); Om=sum(c[n] for n in range(1,p) if 4*n<p)
        if 2*(2*Na-m)!=kappa+2*Om.real: F('cor46a')
        if (2*ea-(kappa+2*Om.real))%8: F('cor46b')
    if any(pow(y,2**(a-1),p)==2 for y in range(1,p)):
        if pow(2,m,p)==1 and ea!=fa: F('coll1')
        if pow(2,m,p)!=1 and ea!=-fa: F('coll2')
        if any(pow(y,2**a,p)==2 for y in range(1,p)) != (Na%2==1): F('coll3')
    for k in range(1,40):
        if (p-1)%(2*k): continue
        if not any(pow(y,k,p)==2 for y in range(1,p)): continue
        nu=sum(1 for n in range(1,p) if 4*n<p and any(pow(y,k,p)==n for y in range(1,p)))
        if any(pow(y,2*k,p)==2 for y in range(1,p)) != (nu%2==((p-1)//(2*k))%2): F('lehmer')
    if p%8==1:
        for c in (quartic(p),):
            for cc in (c,{n:c[n].conjugate() for n in c}):
                C=sum(cc[n]*(-1)**band(n,p) for n in range(1,(p+1)//2))
                if (C.real-kappa)%4 or (C.imag-kappa)%4: F('onemod8')
    if p%8!=5 or p<13: continue
    Q=(p-1)//4; chi=pinned(p)
    beta=sum(chi[n]*n for n in range(1,p))/p; k=round(beta.real); t=round(beta.imag)
    H=[n for n in range(1,p) if chi[n]==1]; H2=[n for n in range(1,p) if chi[n]==1j]
    C=sum(chi[n]*(-1)**band(n,p) for n in range(1,(p+1)//2)); f=round(C.real); e=round(C.imag)
    alpha=sum(1 for x in H if x%2)
    for mm in range(1,9):
        d=math.gcd(mm,Q); Hd={pow(x,d,p) for x in H}
        Th=(-1)**(alpha+sum(1 for y in Hd if y%2))
        Ce=sum(chi[n]*(-1)**band(n,p,2*mm) for n in range(1,(p+1)//2))
        if (round(Ce.real)-(Q+1-Th))%4: F('pow_re')
        if (round(Ce.imag)-(-1)**(mm-1)*(kappa+1-Th))%4: F('pow_im')
    E=sum(1 for n in range(1,(p+1)//2) if inv(n,p)%2==0)
    if (E-(k+t))%4 or (E-(kappa-Q))%4: F('E')
    L=sum(chi[n]*(-1)**(n+inv(n,p)) for n in range(1,(p+1)//2))
    if (round(L.real)+t)%4 or (round(L.imag)+k)%4: F('L')
    D=lambda X: sum(1 for u in X if u%2 and (u*u%p)%2)
    if f!=4*D(H)+2*k+4*t-Q or e!=4*D(H2)-3*k-t-Q: F('delta')
    hm=(k*k+t*t)//2
    if (kappa-Q)%4==0:
        if (k+t-(hm-1))%8: F('mod8a')
    else:
        if (k+t-2)%4: F('mod8b')
        if hm%8==1 and (k-t)%8: F('mod8c')
    # e = -sum_H s(2h) s(-4h^2)
    if e!=-sum(s(2*h,p)*s(-4*h*h,p) for h in H): F('eP')
    for w in range(2,p):
        if pow(w,3,p)==1:
            i4=inv(4,p); i2=inv(2,p)
            rho=-(s(-w*i2,p)*s(-w*w*i4,p)+s(-w*w*i2,p)*s(-w*i4,p))
            x=w; exp=0 if x%4!=2 else (-2 if x%8==2 else 2)
            if rho!=exp: F('rho3')
            if s(w,p)*s(w*w,p)+s(w*w,p)*s(pow(w,4,p),p)!=2: F('cyc2')
    M=lambda aa: sum(s(u,p)*s(aa*u,p) for u in H)
    Cc=lambda aa: sum(1 for u in H if u%2 and (aa*u%p)%2)
    if any(M(aa)!=Q-4*alpha+4*Cc(aa) for aa in H): F('defect1')
    if sum(Cc(aa) for aa in H)!=alpha**2: F('defect2')
    rhs=sum(((aa%2)+(inv(aa,p)%2))%2*(M(aa)-Q) for aa in H if aa!=inv(aa,p))
    if (2*(f-Q)-rhs)%16: F('defect3')
    for aa in (1,3,5,7,9,11):
        if p%aa==0: continue
        l=M(aa); r1=sum((-1)**((aa*u)//p) for u in H); r2=sum((1+leg(n,p))*(-1)**((aa*n)//p) for n in range(1,p))
        if not(l==r1 and 4*l==r2): F('oddmult')
    if p%40==29:
        v=(p+1)//5
        R5=sum(1 for n in range(1,p) if p<5*n<2*p and leg(n,p)==1)
        xi=[0,1,1j,-1j,-1]
        S=sum(leg(n,p)*xi[n%5]*n for n in range(1,5*p))
        R=S.real/(5*p); Ii=S.imag/(5*p)
        if R!=round(R) or Ii!=round(Ii): F('fifth_int')
        R=round(R); Ii=round(Ii)
        if 4*R5!=2*v+Ii-R: F('fifth1')
        if 2*M(5)!=2*Q-2*v+R-Ii: F('fifth2')
        in5 = pow(5,Q,p)==1
        if in5 != ((R-Ii-2*v)%8==0): F('fifth3')
        if in5:
            d5=((5%2)+(inv(5,p)%2))%2
            if ((d5*(M(5)-Q)-4)%8==0) != ((R-Ii-2*v+8)%16==0): F('fifth4')
print('fails:',fails)
# Lemma 5.7 (iii) at all odd primes, with H = H_a
fails2=0;cnt=0
for p in primerange(3,1200):
    a=v2(p-1); m=(p-1)>>a
    H=[x for x in range(1,p) if pow(x,m,p)==1]
    f=sum(s(u,p)*s(u*u,p) for u in H)
    M=lambda aa: sum(s(u,p)*s(aa*u,p) for u in H)
    rhs=sum(((aa%2)+(inv(aa,p)%2))%2*(M(aa)-m) for aa in H if aa!=inv(aa,p))
    cnt+=1
    if (2*(f-m)-rhs)%16: fails2+=1
print('defect general:',cnt,fails2)
