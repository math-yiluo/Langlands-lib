/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.FormallySmoothAdicClosedFiberCompletion
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiberComplete

/-!
# Adic formal smoothness from flatness and the closed fibre

Source: Stacks Project, More on Algebra, Proposition 15.41.5 (Tag 07NQ), (2) => (3)
(blueprint: lem-weil-pbc-flat-formally-smooth-closed-fibre-adic).
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom

private theorem completion_eval_ker
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
  ext x
  rw [AdicCompletion.maximalIdeal_eq_map, RingHom.mem_ker, ← Ideal.map_pow]
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (maximalIdeal R))]
  change AdicCompletion.evalₐ (maximalIdeal R) n x = 0 ↔
    AdicCompletion.eval (maximalIdeal R) R n x = 0
  let e := Ideal.quotientEquivAlgOfEq R
    (show ((maximalIdeal R) ^ n • ⊤ : Ideal R) = (maximalIdeal R) ^ n by simp)
  exact map_eq_zero_iff e e.injective

/-- The reverse completion reduction in Stacks Tag 07ED. -/
private theorem formallySmoothAdic_of_completion
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (ψ : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    [IsLocalHom ψ]
    (hcomm : ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp f)
    (hfs : letI := ψ.toAlgebra
      Algebra.FormallySmoothAdic (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B)
        (maximalIdeal (AdicCompletion (maximalIdeal B) B))) :
    let := f.toAlgebra
    Algebra.FormallySmoothAdic A B (maximalIdeal B) := by
  dsimp only
  let := f.toAlgebra
  intro D _ _ J hJ g hg
  obtain ⟨k, hk, hgk⟩ := hg
  let Ahat := AdicCompletion (maximalIdeal A) A
  let Bhat := AdicCompletion (maximalIdeal B) B
  let cA : A →+* Ahat := algebraMap A Ahat
  let cB : B →+* Bhat := algebraMap B Bhat
  have hcomm' (a : A) : ψ (cA a) = cB (f a) := RingHom.congr_fun hcomm a
  let α : A →+* D := algebraMap A D
  have hαJ : (maximalIdeal A) ^ k ≤ J.comap α := by
    intro a ha
    change α a ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hfa : f a ∈ (maximalIdeal B) ^ k := by
      exact (pow_le_pow_left' (map_maximalIdeal_le f) k)
        (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f ha)
    exact (g.commutes a).symm.trans (hgk (f a) hfa)
  have hαkill : ∀ a ∈ (maximalIdeal A) ^ (k + k), α a = 0 := by
    have hp : (maximalIdeal A) ^ (k + k) ≤ (J ^ 2).comap α := by
      rw [pow_add, pow_two]
      exact (Ideal.mul_mono hαJ hαJ).trans (Ideal.le_comap_mul _)
    rw [hJ] at hp
    exact fun a ha ↦ hp ha
  let αhat : Ahat →+* D :=
    (Ideal.Quotient.lift ((maximalIdeal A) ^ (k + k)) α hαkill).comp
      (AdicCompletion.evalₐ (maximalIdeal A) (k + k)).toRingHom
  have hαhat (a : A) : αhat (cA a) = α a := by
    change Ideal.Quotient.lift _ α hαkill
      (AdicCompletion.evalₐ (maximalIdeal A) (k + k) (cA a)) = α a
    rw [show AdicCompletion.evalₐ (maximalIdeal A) (k + k) (cA a) =
      Ideal.Quotient.mk ((maximalIdeal A) ^ (k + k)) a from
        AdicCompletion.evalₐ_of _ _ a]
    rfl
  let ghat : Bhat →+* D ⧸ J :=
    (Ideal.Quotient.lift ((maximalIdeal B) ^ k) g.toRingHom hgk).comp
      (AdicCompletion.evalₐ (maximalIdeal B) k).toRingHom
  have hghat (b : B) : ghat (cB b) = g b := by
    change Ideal.Quotient.lift _ g.toRingHom hgk
      (AdicCompletion.evalₐ (maximalIdeal B) k (cB b)) = g b
    rw [show AdicCompletion.evalₐ (maximalIdeal B) k (cB b) =
      Ideal.Quotient.mk ((maximalIdeal B) ^ k) b from AdicCompletion.evalₐ_of _ _ b]
    rfl
  have hghatkill : ∀ b ∈ maximalIdeal Bhat ^ k, ghat b = 0 := by
    intro b hb
    rw [← completion_eval_ker B k] at hb
    change Ideal.Quotient.lift _ g.toRingHom hgk
      (AdicCompletion.evalₐ (maximalIdeal B) k b) = 0
    rw [show AdicCompletion.evalₐ (maximalIdeal B) k b = 0 from hb, map_zero]
  let : Algebra Ahat Bhat := ψ.toAlgebra
  let : Algebra Ahat D := αhat.toAlgebra
  let ghatA : Bhat →ₐ[Ahat] D ⧸ J := ⟨ghat, by
    intro a
    obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) (k + k) a)
    have hd : a - cA a₀ ∈ maximalIdeal Ahat ^ (k + k) := by
      rw [← completion_eval_ker A (k + k), RingHom.mem_ker]
      change AdicCompletion.evalₐ (maximalIdeal A) (k + k) (a - cA a₀) = 0
      rw [map_sub, show AdicCompletion.evalₐ (maximalIdeal A) (k + k) (cA a₀) =
        Ideal.Quotient.mk ((maximalIdeal A) ^ (k + k)) a₀ from
          AdicCompletion.evalₐ_of _ _ a₀, ha₀, sub_self]
    have hψd : ψ (a - cA a₀) ∈ maximalIdeal Bhat ^ k := by
      apply Ideal.pow_le_pow_right (Nat.le_add_right k k)
      exact (pow_le_pow_left' (map_maximalIdeal_le ψ) (k + k))
        (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ψ hd)
    have hgd : ghat (ψ a) = ghat (ψ (cA a₀)) := by
      simpa only [map_sub, sub_eq_zero] using hghatkill _ hψd
    have hαa : αhat a = α a₀ := by
      change Ideal.Quotient.lift _ α hαkill
        (AdicCompletion.evalₐ (maximalIdeal A) (k + k) a) = α a₀
      rw [← ha₀]
      rfl
    change ghat (ψ a) = Ideal.Quotient.mk J (αhat a)
    rw [hgd, hcomm' a₀, hghat, hαa]
    exact g.commutes a₀⟩
  obtain ⟨l, hl⟩ := hfs J hJ ghatA ⟨k, hk, hghatkill⟩
  let lB : B →ₐ[A] D := ⟨l.toRingHom.comp cB, by
    intro a
    change l (cB (f a)) = α a
    rw [← hcomm' a]
    exact (l.commutes (cA a)).trans (hαhat a)⟩
  refine ⟨lB, ?_⟩
  ext b
  exact (AlgHom.congr_fun hl (cB b)).trans (hghat b)

/-- A flat local map of Noetherian local rings with adically formally smooth closed fibre
is formally smooth for the maximal-ideal-adic topology on the target.
The residue field and closed fibre are the canonical quotients, with the induced quotient
algebra structure. The image of `maximalIdeal B` in the closed fibre is its maximal ideal.
Source: Stacks Project, More on Algebra, Proposition 15.41.5 (Tag 07NQ), (2) => (3)
(blueprint: lem-weil-pbc-flat-formally-smooth-closed-fibre-adic).

Proof from the node, following Tag 07NQ:
1. *Reduction to complete local rings.* Put $A^\wedge=\varprojlim A/\mathfrak m_A^n$ and
$B^\wedge=\varprojlim B/\mathfrak m_B^n$ [def-weil-pbc-adic-completion]. By
[lem-weil-pbc-flat-completion], $A^\wedge\to B^\wedge$ is flat; by
[lem-weil-pbc-local-completion-local-ring] and [lem-weil-pbc-adic-completion-noetherian] these are
Noetherian complete local rings with the original residue fields. The closed fibre
$B^\wedge/\mathfrak m_A B^\wedge$ is the $\mathfrak m_{\overline B}$-adic completion of $\overline
B$: quotienting $B^\wedge$ by $\mathfrak m_A B^\wedge$ gives the inverse limit of $B/(\mathfrak
m_AB+\mathfrak m_B^n)$, which is $\varprojlim\overline B/\mathfrak m_{\overline B}^n$ by
[lem-weil-pbc-adic-completion-mod-power] and the Noetherian quotient identification
[lem-weil-pbc-local-completion-quotient]. Hence this fibre is formally smooth over $k$ by
[lem-weil-pbc-fs-adic-completion] applied to the hypothesis on $\overline B$. We prove the result
first for the complete map $A^\wedge\to B^\wedge$.

2. *Cohen presentation.* For the complete map, use
[lem-weil-pbc-complete-local-map-cohen-presentation] (Stacks 07NN): there is a commutative square
$R\xrightarrow{u}S$, $R\twoheadrightarrow A^\wedge$, $S\twoheadrightarrow B^\wedge$, with $R,S$
complete regular local power-series rings over fields or Cohen rings, $u$ local and flat, and a
regular system of parameters $t_1,\ldots,t_d$ of $R$ whose images extend to one of $S$; in residue
characteristic $p>0$ choose $t_1=p$. Put $\overline S=S/\mathfrak m_RS$. By
[lem-weil-pbc-regular-local-generators-regular-sequence], $\overline S$ is regular local. The
surjection $S\to B^\wedge$ induces a surjection $\overline
S\to\overline{B^\wedge}:=B^\wedge/\mathfrak m_{A^\wedge}B^\wedge$, since $R/\mathfrak m_R\cong
A^\wedge/\mathfrak m_{A^\wedge}=k$ (the horizontal surjection is local).

3. *Remove the regular-fibre equations.* The complete closed fibre $\overline{B^\wedge}$ is a
Noetherian local quotient of $B^\wedge$ by [lem-weil-pbc-surjective-image-noetherian] and
[lem-weil-pbc-quotient-local-structure]. It is formally smooth over $k$ by Step 1 and therefore
regular local by [lem-weil-pbc-fs-adic-field-geometrically-regular] (the trivial field extension
gives regularity). The regular local surjection $\overline S\twoheadrightarrow\overline{B^\wedge}$
has kernel generated by elements $\bar x_1,\ldots,\bar x_r$ forming part of a regular system of
parameters of $\overline S$, by [lem-weil-pbc-regular-local-quotient-kernel-parameters]. Lift each
$\bar x_i$ to $x_i$ in the kernel of $S\twoheadrightarrow B^\wedge$: a lift in $S$ maps to an
element of $\mathfrak m_{A^\wedge}B^\wedge$, hence subtracting a suitable element of $\mathfrak
m_RS$ makes it map to zero. In $\mathfrak m_S/\mathfrak m_S^2$, the classes of the $t_i$ are
independent and the classes of the $x_i$ are independent modulo their span; hence all these
classes are independent. Extend them to a basis and use Nakayama
[lem-weil-pbc-nakayama-local-generators] and [lem-weil-pbc-regular-local-cotangent-dimension] to
see that $t_1,\ldots,t_d,x_1,\ldots,x_r$ extend to a regular system of parameters of $S$.

4. Put $T=S/(x_1,\ldots,x_r)$. The map $S\to B^\wedge$ factors through $T$. By
[lem-weil-pbc-power-series-parameter-quotient] (Stacks 07NM), $T$ is again a complete local
power-series ring over the same kind of coefficient field or Cohen ring, with the images of
$t_1,\ldots,t_d$ among its parameters (and $t_1=p$ in mixed characteristic). By
[lem-weil-pbc-regular-local-generators-regular-sequence], these images form a regular sequence, so
$R\to T$ is flat by [lem-weil-pbc-flat-over-regular]. Its closed fibre $T/\mathfrak m_RT$ is
$\overline S/(\bar x_1,\ldots,\bar x_r)\cong\overline{B^\wedge}$ as a local $k$-algebra, with the
isomorphism induced by $T\to B^\wedge$. It is formally smooth over $k$ for its maximal-ideal-adic
topology by transport of the lifting property [theorem-finite-etale-covers-proper-henselian--2].

5. *Identify the completed target with a base change.* The Cohen presentation in Step 2 gives a
surjection $R\to A^\wedge$. Let $D=T\otimes_R A^\wedge\cong T/(\ker(R\to A^\wedge))T$
[lem-weil-pbc-tensor-quotient-base-change], and let $h:D\to B^\wedge$ be induced by $T\to
B^\wedge$ and $A^\wedge\to B^\wedge$. It is surjective because $T\to B^\wedge$ is. Both $D$ and
$B^\wedge$ are flat over $A^\wedge$: $D$ by [lem-weil-pbc-flat-module-base-change] from $R\to T$
flat (Step 4), and $B^\wedge$ by Step 1. Modulo $\mathfrak m_{A^\wedge}$, $h$ is the isomorphism
$T/\mathfrak m_RT\to\overline{B^\wedge}$ of Step 4. If $I=\ker h$, the exact sequence $0\to I\to
D\to B^\wedge\to0$ stays left exact after tensoring with $k$, because its last term is flat
[lem-weil-pbc-flat-quotient-tensor-injective]; the middle-to-last map is an isomorphism, so
$I/\mathfrak m_{A^\wedge}I=0$. The ring $D$ is a Noetherian local quotient of $T$ by
[lem-weil-pbc-surjective-image-noetherian] and [lem-weil-pbc-quotient-local-structure], so $I$ is
finitely generated. Since $\mathfrak m_{A^\wedge}D$ lies in the maximal ideal $\mathfrak m_D$, one
has $I/\mathfrak m_D I=0$ as a quotient of $I/\mathfrak m_{A^\wedge}I=0$. Nakayama
[lem-weil-pbc-nakayama-local-generators] with the empty generating family gives $I=0$. Thus $h$ is
an isomorphism.

6. *It remains to lift for $R\to T$.* If $T$ is formally smooth over $R$ for its
maximal-ideal-adic topology, [lem-weil-pbc-fs-adic-base-change] gives the same for $D=T\otimes_R
A^\wedge$ over $A^\wedge$ with the extended maximal ideal, which is the maximal ideal of $D$ since
$D$ is a local quotient of $T$. Transport through $h:D\cong B^\wedge$ (Step 5) gives formal
smoothness of $B^\wedge$ over $A^\wedge$ [theorem-finite-etale-covers-proper-henselian--2]. We now
prove the needed lifting property for $R\to T$ using its power-series coordinates. To lighten
notation write $S=T$, let $\mathfrak m$ be its maximal ideal, $k=R/\mathfrak m_R$, and
$K=S/\mathfrak m$.

7. *Reduce a square-zero lifting problem to a residue-vector-space kernel.* Take an $R$-algebra
$N$, a square-zero ideal $J\subseteq N$, and an $R$-algebra map $g:S\to N/J$ killing $\mathfrak
m^n$ for some $n\ge1$ [theorem-finite-etale-covers-proper-henselian--2]. The map $g$ makes $J$ an
$S$-module: $s\cdot j$ is $g(s)j$, independent of a lift of $g(s)$ because $J^2=0$; thus $\mathfrak
m^nJ=0$. Set $J_i=\{j\in J: \mathfrak m^i j=0\}$ for $0\le i\le n$. Then $0=J_0\subseteq
J_1\subseteq\cdots\subseteq J_n=J$, and $\mathfrak m(J_{i+1}/J_i)=0$. Each $J_i$ is an ideal of
$N$, and each map $N/J_i\to N/J_{i+1}$ has square-zero kernel $J_{i+1}/J_i$. Therefore it suffices
to solve the lifting problem for such a kernel, one quotient at a time. In that case $J$ is a
$K$-vector space since $S/\mathfrak m=K$ is a field.

8. *An unrestricted lift, then correction of the parameter values.* Assume $\mathfrak mJ=0$. By
[lem-weil-pbc-power-series-field-cohen-fs-adic] (Stacks 07NL), $S$ is formally smooth over
$\mathbf Q$ in residue characteristic zero and over $\mathbf Z$ in residue characteristic $p$. The
original map $g$ and the map from the prime ring to $N$ form a lifting diagram for this property.
In the characteristic-zero case, all nonzero integers are units in $N/J$ because $S$ contains
$\mathbf Q$; a unit modulo a square-zero ideal is a unit in $N$ (if $ab=1+j$, inverse $1-j$
corrects it), so $N$ is a $\mathbf Q$-algebra as required. Hence obtain a ring map $\psi:S\to N$
lifting $g$. The coordinates of $S$ after Step 4 are formal variables
$t_1,\ldots,t_d,y_1,\ldots,y_m$ over a coefficient field, or $t_2,\ldots,t_d,y_1,\ldots,y_m$ over
a Cohen ring with $t_1=p$. For each $i$, $\psi(t_i)$ and the prescribed image $\varphi(t_i)$ of
$R\to N$ differ by an element of $J$. Keep the coefficient-ring map fixed and substitute
$\varphi(t_i)$ for $\psi(t_i)$: all variable images are nilpotent because $g(\mathfrak m^n)=0$ and
$J^2=0$, so a formal series evaluates through a finite truncation. The resulting map still lifts
$g$ and satisfies $\psi(t_i)=\varphi(t_i)$ for every $i$ (automatic for $p$).

9. *The defect is a derivation from the residue field.* Since $\psi$ lifts $g$ and agrees with
$\varphi:R\to N$ on $t_1,\ldots,t_d$, the difference $\Delta=\psi\circ u-\varphi:R\to J$ is
additive, satisfies $\Delta(ab)=\varphi(a)\Delta(b)+\varphi(b)\Delta(a)$ (the product of two
elements of $J$ is zero), and kills all $t_i$. By [def-weil-pbc-kahler-differentials], it
corresponds to a linear map $\xi: \Omega_{R/\mathbf Z}\to J$. The $R$-action on $J$ factors
through $k$ because $u(\mathfrak m_R)\subseteq\mathfrak m$ and $\mathfrak mJ=0$; hence $\xi$ kills
$\mathfrak m_R\Omega_{R/\mathbf Z}$. It also kills $\mathrm dt_i$; these generate the image of
$\mathfrak m_R/\mathfrak m_R^2$ in $k\otimes_R\Omega_{R/\mathbf Z}$ because the $t_i$ generate
$\mathfrak m_R$. Exactness of the quotient differential sequence
[lem-weil-pbc-jacobi-zariski-differential-maps] therefore makes $\xi$ factor uniquely through a
$k$-linear map $\xi_0:\Omega_{k/\mathbf Z}\to J$. Tensor with $K$ to obtain a $K$-linear map
$\xi_K:\Omega_{k/\mathbf Z}\otimes_kK\to J$.

10. *Extend and subtract the defect.* The closed fibre $\overline S=S/\mathfrak m_RS$ is formally
smooth over $k$ (Step 4) and Noetherian local, so
[lem-weil-pbc-fs-adic-field-differentials-injective] makes $\Omega_{k/\mathbf
Z}\otimes_kK\to\Omega_{\overline S/\mathbf Z}\otimes_{\overline S}K$ injective. Extend $\xi_K$ to
a $K$-linear map $\xi':\Omega_{\overline S/\mathbf Z}\otimes_{\overline S}K\to J$ by extending a
basis of the image to a basis of the ambient vector space. Compose $S\to\overline S$, the
universal derivation $\mathrm d:\overline S\to\Omega_{\overline S/\mathbf Z}$
[def-weil-pbc-kahler-differentials], reduction to $K$, and $\xi'$ to obtain a derivation
$\Delta':S\to J$. For $r\in R$, its value equals $\xi_K(\mathrm d(r\bmod\mathfrak
m_R)\otimes1)=\xi_0(\mathrm d(r\bmod\mathfrak m_R))=\Delta(r)$ by Step 9. Thus
$\psi'=\psi-\Delta':S\to N$ is a ring homomorphism: additivity and unit are clear, and
$\psi'(a)\psi'(b)=\psi(ab)-\psi(a)\Delta'(b)-\psi(b)\Delta'(a)$ since $J^2=0$, equal to
$\psi(ab)-\Delta'(ab)$ by Leibniz. Also $\pi\psi'=g$ as $\Delta'$ lands in $J$, and $\psi'\circ
u=\varphi$ by the equality of defects. This solves the residue-vector-space case of Step 7;
induction along its filtration solves every square-zero lifting problem. Therefore $S$ is formally
smooth over $R$ for its $\mathfrak m$-adic topology.

11. *Return from completions.* Steps 6-10 prove that $B^\wedge$ is formally smooth over
$A^\wedge$. For an original lifting problem $A\to N$, $J^2=0$, $g:B\to N/J$ with $g(\mathfrak
m_B^n)=0$, the composite $A\to B\xrightarrow{g}N/J$ kills $\mathfrak m_A^n$ because $f$ is local.
Consequently $A\to N$ sends $\mathfrak m_A^n$ into $J$ and kills $\mathfrak m_A^{2n}$; it factors
uniquely through $A^\wedge$ using $A/\mathfrak m_A^{2n}\cong A^\wedge/(\mathfrak
m_AA^\wedge)^{2n}$ [lem-weil-pbc-adic-completion-mod-power]. Similarly $g$ factors through
$B/\mathfrak m_B^n\cong B^\wedge/(\mathfrak m_BB^\wedge)^n$, giving $g^\wedge:B^\wedge\to N/J$.
The two composites $A^\wedge\to N/J$ agree: each kills $(\mathfrak m_AA^\wedge)^{2n}$, each is
determined by its restriction to the surjective image of $A$ in $A^\wedge/(\mathfrak
m_AA^\wedge)^{2n}$, and those restrictions agree in the original lifting square. Formal smoothness
of $B^\wedge/A^\wedge$ supplies a lift $B^\wedge\to N$; restricting it along $B\to B^\wedge$
solves the original diagram. Hence $B$ is formally smooth over $A$ for the $\mathfrak m_B$-adic
topology. -/
theorem formallySmoothAdic_of_flat_closedFiber
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat) :
    letI : Algebra A B := f.toAlgebra
    let I : Ideal B := Ideal.map f (maximalIdeal A)
    letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal A ≤ I.comap (algebraMap A B))
    Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)) →
      Algebra.FormallySmoothAdic A B (maximalIdeal B) := by
  dsimp only
  let : Algebra A B := f.toAlgebra
  intro hfibre
  let Ahat := AdicCompletion (maximalIdeal A) A
  let Bhat := AdicCompletion (maximalIdeal B) B
  have : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing _
  have : IsNoetherianRing Bhat := AdicCompletion.isNoetherianRing _
  obtain ⟨ψ, _, hcomm, hψflat⟩ := flat_adicCompletion_of_flat_local A B f hflat
    (fun x hx ↦ map_maximalIdeal_le f (Ideal.mem_map_of_mem f hx))
  have : IsLocalHom ψ := by
    apply ((local_hom_TFAE ψ).out 1 3).mpr
    rw [AdicCompletion.maximalIdeal_eq_map (R := A), Ideal.map_map, hcomm,
      ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map (R := B)]
    exact Ideal.map_mono (map_maximalIdeal_le f)
  have hclosed := formallySmoothAdic_closedFiber_completion A B f ψ hcomm hfibre
  have hcomplete := formallySmoothAdic_of_flat_closedFiber_complete Ahat Bhat ψ
    hψflat hclosed
  exact formallySmoothAdic_of_completion A B f ψ hcomm hcomplete

end RingHom
