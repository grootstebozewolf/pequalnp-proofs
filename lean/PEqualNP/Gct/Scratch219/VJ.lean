import PEqualNP.Gct.Scratch219.VJCore
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Embedding.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.Map
-- `grind` needs these two for ℂ: `Lean.Grind.IsCharP` and `NoNatZeroDivisors` (to divide by 3).
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Group.Torsion

/-! Scratch for L-gct-219, case vJ: the statement, the reduction and the assembly.

The reduction is L-gct-215's proof of its own case vJ (`aEn`, `aG7`, `xO`; lemmas copied
from `PEqualNP/Outside/L_gct_215.lean`, namespaces renamed), run one dimension lower:
`dim L ≤ 4 + dim P` where `P = L ∩ ker (row 0)`. L-gct-215 needed `dim P ≤ 3`; here vJ needs
`dim P ≤ 2`, which is `xO2`. `xO2` keeps `xO`'s split; its branch `∑ b = 0` is the finite
computation, `VJCore.core`, closed by explicit certificates. Changes against L-gct-215:
`xO` → `xO2`, the bound `7` → `6`, and the cube root of unity is written down
(`(-1 + √3 i)/2`) instead of taken from `IsAlgClosed`. -/

namespace PEqualNP.Gct.Scratch219.VJ
noncomputable section
open Finset
abbrev aC:=Fin 4×Fin 5→ℂ
abbrev aH:=Fin 5→ℂ
abbrev row (i:Fin 4):aC→ₗ[ℂ] aH:=LinearMap.funLeft ℂ ℂ fun j=>(i,j)
def aO (M:aC):ℂ:=∑e:Fin 4 ↪ Fin 5,∏r,M (r,e r)
abbrev aHw:=Fin 5×Fin 5×Fin 5×Fin 5
def yH:aHw≃(Fin 4→Fin 5) where
 toFun p:= ![p.1,p.2.1,p.2.2.1,p.2.2.2]
 invFun z:=(z 0,z 1,z 2,z 3)
 left_inv _:=rfl
 right_inv z:=by ext i;fin_cases i<;>rfl
lemma cK (M:aC):
  aO M=∑j,∑l,∑m,∑n,
   if j=l∨j=m∨j=n∨l=m∨l=n∨m=n then 0 else
   M (0,j)*M (1,l)*M (2,m)*M (3,n):=by
 classical
 let u (z:Fin 4→Fin 5):=∏r,M (r,z r)
 have A:aO M=∑z:Fin 4→Fin 5,if Function.Injective z then u z else 0:=by
  let E:=Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
  change(∑e:Fin 4 ↪ Fin 5,u e)=_;rw[←E.sum_comp (fun e:Fin 4 ↪ Fin 5=>u e),←Finset.sum_filter];exact(Finset.sum_subtype _ (by simp) u).symm
 rw[A,←yH.sum_comp (fun z=>if Function.Injective z then u z else 0)];simp only[Fintype.sum_prod_type];refine sum_congr rfl fun a _=>sum_congr rfl fun b _=>sum_congr rfl fun c _=>sum_congr rfl fun d _=> ?_
 let z:=yH (a,b,c,d)
 have p:z 0=a:=rfl;have q:z 1=b:=rfl;have s:z 2=c:=rfl;have t:z 3=d:=rfl;have f:Function.Injective z↔¬(a=b∨a=c∨a=d∨b=c∨b=d∨c=d):=by
  constructor
  ·intro o;have h (i j:Fin 4) (g:i≠j):z i≠z j:=fun h=>g (o h)
   exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
    (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
      (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
  ·intro g i j v;simp only[not_or] at g;fin_cases i<;>fin_cases j<;>first | rfl | grind
 change(if Function.Injective z then u z else 0)=_;by_cases g:a=b∨a=c∨a=d∨b=c∨b=d∨c=d
 ·have k:¬Function.Injective z:=fun h=>f.mp h g
  rw[ite_eq_right k,ite_eq_left g]
 ·rw[ite_eq_left (f.mpr g),ite_eq_right g];change(∏r,M (r,z r))=_;simp[Fin.prod_univ_succ,p,q,s,t,mul_assoc]
abbrev aD (L:Submodule ℂ aC):=∀t∈L,aO (1+t)=120
abbrev aX (L:Submodule ℂ aC):=Module.finrank ℂ L
def aZ (L:Submodule ℂ aC) (i:Fin 4):Submodule ℂ aC:=L⊓ ⨅ r:{r:Fin 4//r≠i},LinearMap.ker (row r.val)
abbrev u (L:Submodule ℂ aC) (i:Fin 4):=aX (aZ L i)
def G3 (j:Fin 5) (x y z:aH):ℂ:=∑l,∑m,∑n,if j=l∨j=m∨j=n∨l=m∨l=n∨m=n then 0 else x l*y m*z n
lemma sX (M:aC):
  aO M=∑j,M (0,j)*G3 j (fun l=>M (1,l)) (fun l=>M (2,l)) (fun l=>M (3,l)):=by
 rw[cK];simp only[G3,mul_sum,mul_ite,mul_zero,mul_assoc]
lemma cJ (j:Fin 5) (x y z:aH):
  G3 j x y z=((∑l,x l)-x j)*((∑l,y l)-y j)*((∑l,z l)-z j)
   -((∑l,x l)-x j)*((∑l,y l*z l)-y j*z j)
   -((∑l,y l)-y j)*((∑l,x l*z l)-x j*z j)
   -((∑l,z l)-z j)*((∑l,x l*y l)-x j*y j)
   +2*((∑l,x l*y l*z l)-x j*y j*z j):=by
 rcases (by revert j;decide:j=0∨j=1∨j=2∨j=3∨j=4) with rfl|rfl|rfl|rfl|rfl<;>
 ·simp(config:={decide:=true}) only[G3,Fin.sum_univ_five,ite_true,ite_false,
   zero_add,add_zero]
  ring
def S1 (j:Fin 5) (x y z:aH):ℂ:=((∑l,x l)-x j)+((∑l,y l)-y j)+((∑l,z l)-z j)
def Q2 (j:Fin 5) (x y z:aH):ℂ:=
 ((∑l,x l)-x j)*((∑l,y l)-y j)+((∑l,x l)-x j)*((∑l,z l)-z j)
   +((∑l,y l)-y j)*((∑l,z l)-z j)
   -
    (((∑l,x l*y l)-x j*y j)+((∑l,x l*z l)-x j*z j)
    +((∑l,y l*z l)-y j*z j))
lemma aEm (c:ℂ) (j:Fin 5) (x y z:aH):
  G3 j (fun l=>1+c*x l) (fun l=>1+c*y l) (fun l=>1+c*z l)=24+6*c*S1 j x y z+2*c^2*Q2 j x y z+c^3*G3 j x y z:=by
 simp only[cJ,S1,Q2,Fin.sum_univ_five];ring
lemma aBs (j:Fin 5):G3 j (fun _=>1) (fun _=>1) (fun _=>1)=24:=by simp[cJ];norm_num
lemma yI (σ:Equiv.Perm (Fin 4)) (M:aC):
  aO (fun p=>M (σ p.1,p.2))=aO M:=by
 rw[aO,aO,←(Equiv.embeddingCongr σ (.refl _)).sum_comp (fun e=>∏r,M (r,e r))];refine sum_congr rfl fun e _=> ?_
 rw[←Equiv.prod_comp σ (fun r=>M (r,_))];simp[Equiv.embeddingCongr_apply]
section
variable {P : Type*} [AddCommGroup P] [Module ℂ P]
lemma dE (f g:P→ₗ[ℂ] ℂ) (h:∀x,f x*g x=0):f=0∨g=0:=by by_contra! a;simp only[ne_eq,LinearMap.ext_iff,LinearMap.zero_apply,not_forall] at a;obtain⟨⟨x,b⟩,⟨y,c⟩⟩:=a;have:=h x;have:=h y;have:=h (x+y);simp only[map_add] at*;grind
variable [FiniteDimensional ℂ P]
lemma g3_eq (j:Fin 5) (x:aH):G3 j x x x=g3 j x:=by rw[cJ,g3];ring
/-- `xO` of L-gct-215 with `≤ 2` for `≤ 3`. -/
lemma xO2 (a b:Fin 5→P→ₗ[ℂ] ℂ)
  (E:∀x,(∀i,a i x=0)→(∀i,b i x=0)→x=0)
  (z:∀x i,(2*a i x- ∑j,a j x)*(2*b i x- ∑j,b j x)=(∑j,a j x)*(∑j,b j x))
  (M:∀x j,G3 j (a · x) (a · x) (a · x)+G3 j (b · x) (b · x) (b · x)=0):
  Module.finrank ℂ P≤2:=by
 classical
 by_cases g:∑j,b j=0∨∑j,a j=0
 ·wlog K:∑j,b j=0 generalizing a b
  ·exact this b a (fun x V U=>E x U V) (fun x i=>by simpa only[mul_comm] using z x i) (fun x j=>by simpa only[add_comm] using M x j) g.symm (g.resolve_left K)
  have o (x:P):∑j,b j x=0:=by simpa[LinearMap.sum_apply] using LinearMap.congr_fun K x
  refine core a b E o (fun i=> ?_) (fun x j=>by simpa only[g3_eq] using M x j)
  by_cases hbi:b i=0
  ·exact Or.inl hbi
  ·right;intro x
   have h:=(dE ((2:ℂ)•a i- ∑j,a j) ((2:ℂ)•b i)
    fun y=>by simpa[LinearMap.sum_apply,o y] using z y i).resolve_right (smul_ne_zero two_ne_zero hbi)
   exact sub_eq_zero.mp (by simpa[LinearMap.sum_apply] using LinearMap.congr_fun h x)
 ·obtain⟨K,hA⟩:=not_or.mp g
  let A:P→ₗ[ℂ] ℂ:=∑j,a j
  let B:P→ₗ[ℂ] ℂ:=∑j,b j
  obtain⟨y,a0⟩:∃y,A y*B y≠0:=by by_contra! hz;exact(dE A B hz).elim hA K
  simp only[A,B,LinearMap.sum_apply] at a0;refine(LinearMap.finrank_le_finrank_of_injective (f:=A.prod B) ?_).trans (by norm_num[Module.finrank_prod]);refine(injective_iff_map_eq_zero (A.prod B)).mpr fun x e=> ?_
  change(A x,B x)=0 at e;simp only[A,B,Prod.mk_eq_zero,LinearMap.sum_apply] at e;have J (i:Fin 5):a i x=0∧b i x=0:=by have h1:=z x i;have h2:=z y i;have h3:=z (x+y) i;simp only[map_add,sum_add_distrib,e.1,e.2,zero_add] at h1 h3;rcases mul_eq_zero.mp (show a i x*b i x=0 by grind) with h|h<;>grind
  exact E x (fun i=>(J i).1) (fun i=>(J i).2)
end
lemma vN (ω:ℂ) (hω:ω^2+ω+1=0) (j:Fin 5) (a b:aH):
  let x:=fun l=>a l+b l
  let y:=fun l=>ω*a l+ω^2*b l
  let z:=fun l=>ω^2*a l+ω*b l
  Q2 j x y z=3*((∑l,a l*b l)-(∑l,a l)*(∑l,b l)+a j*(∑l,b l)+(∑l,a l)*b j-2*(a j*b j))∧
  G3 j x y z=G3 j a a a+G3 j b b b:=by
 dsimp only;have g:(fun l=>a l+b l)=(fun l=>1*a l+1*b l):=by simp
 rw[g];have h (c d:ℂ):∑l,(c*a l+d*b l)=c*∑l,a l+d*∑l,b l:=by simp[sum_add_distrib,←mul_sum]
 have s2 (c d e f:ℂ):∑l,(c*a l+d*b l)*(e*a l+f*b l)=
   c*e*∑l,a l*a l+(c*f+d*e)*∑l,a l*b l+d*f*∑l,b l*b l:=by
  simp only[mul_sum,←sum_add_distrib];exact sum_congr rfl fun l _=>by ring
 have i:∑l,(1*a l+1*b l)*(ω*a l+ω^2*b l)*(ω^2*a l+ω*b l)=
   (∑l,a l*a l*a l)+∑l,b l*b l*b l:=by
  rw[←sum_add_distrib];exact sum_congr rfl fun l _=>by grind
 rw[Q2,cJ,cJ,cJ];simp only[h,s2,i];exact⟨by grind,by grind⟩
lemma aG6 (L:Submodule ℂ aC) (hL:aD L) (hu:4≤u L 0):aX L≤6:=by
 classical
 let y:Module.Dual ℂ aH:=∑l,(LinearMap.proj l:aH→ₗ[ℂ] ℂ)
 have z (v:aH):y v=∑l,v l:=by simp[y,LinearMap.sum_apply]
 have a2:Module.finrank ℂ (LinearMap.ker y)=4:=by
  have:=Module.Dual.finrank_ker_add_one_of_ne_zero (f:=y) fun h=>by have:=LinearMap.congr_fun h 1;simp[z] at this
  have:Module.finrank ℂ aH=5:=by simp[aH]
  omega
 let R:=aZ L 0
 have x {t:aC} (o:t∈R) (r:Fin 4) (B:r≠0) (c:Fin 5):t (r,c)=0:=congrFun ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp o).2 ⟨r,B⟩) c;have X:R.map (row 0)=LinearMap.ker y:=by
  have J:R.map (row 0)≤LinearMap.ker y:=by rintro _ ⟨t,o,rfl⟩;rw[LinearMap.mem_ker,z];change ∑l,t (0,l)=0;have h:=sX _▸hL t o.1;simp only[Pi.add_apply,Pi.one_apply,x o 1 (by decide),x o 2 (by decide),x o 3 (by decide),add_zero,aBs,←sum_mul,sum_add_distrib] at h;simp at h;linear_combination h/24
  have U:Function.Injective ((row 0).domRestrict R):=
   (injective_iff_map_eq_zero _).mpr fun t h=>Subtype.ext<| funext fun⟨r,c⟩=>
     if B:r=0 then B▸congrFun h c else x t.2 r B c
  have T:=LinearMap.finrank_range_of_inj U;rw[LinearMap.range_domRestrict] at T;have:=Submodule.finrank_mono J;have:4≤Module.finrank ℂ R:=hu;exact Submodule.eq_of_le_of_finrank_eq J (by omega)
 let e (t:aC) (k:Fin 4):aH:=fun l=>t (k,l)
 have F (t:aC) (o:t∈L):(∑l,t (0,l)=0)∧∀j,
   S1 j (e t 1) (e t 2) (e t 3)=0∧Q2 j (e t 1) (e t 2) (e t 3)=0∧G3 j (e t 1) (e t 2) (e t 3)=0:=by
  let g (c:ℂ) (j:Fin 5):ℂ:=G3 j (fun l=>1+c*e t 1 l) (fun l=>1+c*e t 2 l) (fun l=>1+c*e t 3 l)
  have H (c:ℂ) (w:aH) (hw:∑l,w l=0):∑j,(1+c*t (0,j)+w j)*g c j=120:=by obtain⟨s,C,a1⟩:=Submodule.mem_map.mp (X.symm▸(LinearMap.mem_ker.mpr ((z w).trans hw)));simpa[sX,g,e,←a1,row,x C 1 (by decide),x C 2 (by decide),x C 3 (by decide),add_assoc] using hL _ (L.add_mem (L.smul_mem c o) C.1)
  have aEx (c:ℂ):∑j,(1+c*t (0,j))*g c j=120:=by simpa using H c 0 (by simp)
  have G (c:ℂ) (j:Fin 5):g c j=g c 0:=by have h:=H c (Pi.single j 1-Pi.single 0 1) (by simp);have A:=aEx c;simp[add_mul,sub_mul,sum_add_distrib,Pi.single_apply] at h A;linear_combination h-A
  have prod (c:ℂ):(5+c*∑l,t (0,l))*g c 0=120:=by simpa[G c,←sum_mul,sum_add_distrib,←mul_sum] using aEx c
  have M:∑l,t (0,l)=0:=by by_contra a0;have h:=prod (-5/∑l,t (0,l));rw[div_mul_cancel₀ _ a0] at h;norm_num at h
  refine⟨M,fun j=> ?_⟩;have val (c:ℂ):g c j=24:=by rw[G c j];linear_combination(prod c-M*c*g c 0)/5
  have h1:=val 1;have h2:=val (-1);have V:=val 2;simp only[g,aEm] at h1 h2 V;exact⟨by grind,by grind,by grind⟩
 obtain⟨r,B⟩:∃r:ℂ,r^2=-3:=⟨⟨0,Real.sqrt 3⟩,by
  rw[sq];apply Complex.ext<;>simp[Real.mul_self_sqrt (show (0:ℝ)≤3 by norm_num)]⟩
 let ω:ℂ:=(-1+r)/2
 have hω:ω^2+ω+1=0:=by linear_combination B/4
 let P:Submodule ℂ aC:=L⊓LinearMap.ker (row 0)
 let mk (c d:ℂ) (j:Fin 5):P→ₗ[ℂ] ℂ:=
  ((1/3:ℂ)•((LinearMap.proj ((1:Fin 4),j):aC→ₗ[ℂ] ℂ)
    +c•LinearMap.proj ((2:Fin 4),j)+d•LinearMap.proj ((3:Fin 4),j)))∘ₗ P.subtype
 let a:=mk (ω^2) ω
 let b:=mk ω (ω^2)
 have q (c d:ℂ) (j:Fin 5) (p:P):mk c d j p=1/3*(p.1 (1,j)+c*p.1 (2,j)+d*p.1 (3,j)):=rfl;have jS (p:P) (l:Fin 5):p.1 (1,l)+p.1 (2,l)+p.1 (3,l)=0:=by
  have m:=sum_eq_zero fun j (_:j∈univ)=>((F p.1 p.2.1).2 j).1
  have Z:=((F p.1 p.2.1).2 l).1;simp only[S1,e,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at m Z;linear_combination m/4-Z
 have N (p:P):e p.1 1=fun l=>a l p+b l p:=funext fun l=>by have:=jS p l;dsimp[a,b,e];rw[q,q];grind
 have O (p:P):e p.1 2=fun l=>ω*a l p+ω^2*b l p:=funext fun l=>by have:=jS p l;dsimp[a,b,e];rw[q,q];grind
 have Q (p:P):e p.1 3=fun l=>ω^2*a l p+ω*b l p:=funext fun l=>by have:=jS p l;dsimp[a,b,e];rw[q,q];grind
 have C (p:P) (S:∀j,a j p=0) (A:∀j,b j p=0):p=0:=by
  ext ⟨i,l⟩;fin_cases i
  ·exact congrFun p.2.2 l
  ·simpa[e,S,A] using congrFun (N p) l
  ·simpa[e,S,A] using congrFun (O p) l
  ·simpa[e,S,A] using congrFun (Q p) l
 have hq (p:P) (j:Fin 5):
   (2*a j p- ∑l,a l p)*(2*b j p- ∑l,b l p)=(∑l,a l p)*(∑l,b l p):=by
  have K (E:Fin 5):=((vN ω hω E (a · p) (b · p)).1).symm.trans
   (N p▸O p▸Q p▸((F p.1 p.2.1).2 E).2.1)
  have m:=sum_eq_zero fun E (_:E∈univ)=>K E
  simp only[←mul_sum,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←sum_mul] at m;linear_combination(-2/3:ℂ)*K j+(2/9:ℂ)*m
 have hc (p:P) (j:Fin 5):G3 j (a · p) (a · p) (a · p)+G3 j (b · p) (b · p) (b · p)=0:=((vN ω hω j (a · p) (b · p)).2).symm.trans (N p▸O p▸Q p▸((F p.1 p.2.1).2 j).2.2);have V:=xO2 a b C hq hc;have d:Module.finrank ℂ (L.map (row 0))+Module.finrank ℂ P=Module.finrank ℂ L:=by
  rw[←(Submodule.submoduleOfEquivInf _ _).finrank_eq,
   ←((row 0).submoduleMap L).finrank_range_add_finrank_ker,
   LinearMap.range_submoduleMap,LinearMap.ker_submoduleMap]
  simp
 have hm:=Submodule.finrank_mono (show L.map (row 0)≤LinearMap.ker y by rintro _ ⟨t,o,rfl⟩;rw[LinearMap.mem_ker,z];exact(F t o).1);unfold aX;omega
/-- Case vJ of L-gct-219, in L-gct-215's vocabulary. -/
lemma vJ7:∀L,aD L→aX L=7→∀i,4≤u L i→False:=by
 intro L hL j i f
 let σ:Equiv.Perm (Fin 4):=Equiv.swap 0 i
 let Φ:aC≃ₗ[ℂ] aC:=LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodCongr σ (.refl _))
 let L':Submodule ℂ aC:=L.map Φ.toLinearMap
 have c:aD L':=by rintro _ ⟨t,a,rfl⟩;exact(yI σ (1+t)).trans (hL t a)
 have b:(aZ L i).map Φ.toLinearMap≤aZ L' 0:=by rintro _ ⟨t,a,rfl⟩;refine⟨⟨t,a.1,rfl⟩,Submodule.mem_iInf _|>.mpr fun⟨r,d⟩=> ?_⟩;exact(Submodule.mem_iInf _|>.mp (Submodule.mem_inf.mp a).2) ⟨σ r,fun h=>d (σ.injective (h.trans (Equiv.swap_apply_left 0 i).symm))⟩
 have g:=aG6 L' c
  (f.trans ((LinearEquiv.finrank_map_eq Φ _).symm.le.trans (Submodule.finrank_mono b)))
 have e:aX L'=aX L:=LinearEquiv.finrank_map_eq Φ L;omega
end

/-- **L-gct-219, case vJ.** No seven-dimensional complex space `L` of `4 × 5` matrices on which
the permanent at the all-ones matrix stays `120` has a part supported on a single row of
dimension at least four. Stated without any of the definitions above. -/
theorem vJ219 : ∀ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ),
    (∀ t ∈ L, (∑ e : Fin 4 ↪ Fin 5, ∏ r, (1 + t) (r, e r)) = 120) →
    Module.finrank ℂ L = 7 → ∀ i : Fin 4,
    4 ≤ Module.finrank ℂ ↥(L ⊓ ⨅ r : {r : Fin 4 // r ≠ i},
      LinearMap.ker (LinearMap.funLeft ℂ ℂ fun j : Fin 5 => ((r.val, j) : Fin 4 × Fin 5)) :
        Submodule ℂ (Fin 4 × Fin 5 → ℂ)) → False :=
  vJ7

end PEqualNP.Gct.Scratch219.VJ
