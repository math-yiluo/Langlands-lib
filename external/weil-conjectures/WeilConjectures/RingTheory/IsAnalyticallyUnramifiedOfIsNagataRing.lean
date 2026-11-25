/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.AnalyticallyUnramifiedPrincipalCriterion
import WeilConjectures.RingTheory.CompletionFiniteExtensionDecomposition
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.IntegralExtensionDimension
import WeilConjectures.RingTheory.NagataDomainN2
import WeilConjectures.RingTheory.NagataLocalization
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.RegularLocalDimOneIffNormal

/-!
# Reduced completion of a local Nagata domain

Source: Stacks Project, Algebra, Lemma Tag 0331
(blueprint: lem-weil-pbc-local-nagata-domain-analytically-unramified).
-/

@[expose] public section

universe u

/-- A field has zero maximal ideal, and its completion is the field itself. -/
private theorem analyticallyUnramified_of_field (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hf : IsField A) : IsAnalyticallyUnramified A := by
  let := hf.toField
  unfold IsAnalyticallyUnramified
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal A)).symm.toRingHom
    (AdicCompletion.ofAlgEquiv (⊥ : Ideal A)).symm.injective

/-- The positive-dimensional normal case of Stacks Tag 0331, using Tag 0330. -/
private theorem analyticallyUnramified_normal_step (n : ℕ)
    (ih : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsDomain B],
      IsNagataRing B → ringKrullDim B ≤ (n : WithBot ℕ∞) → IsAnalyticallyUnramified B)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] (hA : IsNagataRing A)
    (hdim : ringKrullDim A ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    IsAnalyticallyUnramified A := by
  classical
  by_cases hf : IsField A
  · exact analyticallyUnramified_of_field A hf
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    fun h ↦ hf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨x, hxm, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hle (p : Ideal A) (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
      Ideal.span {x} ≤ p := by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using hp.annihilator_le
  have hheight (p : Ideal A) (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
      p.height = 1 := Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span hx hp
  apply isAnalyticallyUnramified_of_principal_quotient A x hx hxm
  · intro p hp
    let : p.IsPrime := hp.isPrime
    refine ⟨⟨inferInstance, hle p hp⟩, ?_⟩
    intro q hq hqp
    let : q.IsPrime := hq.1
    by_contra hpq
    have hlt : q < p := lt_of_le_not_ge hqp hpq
    have hqbot : q ≠ ⊥ := by
      intro heq
      have : x ∈ q := hq.2 (Ideal.subset_span (Set.mem_singleton x))
      exact hx (by simpa [heq] using this)
    have hqheight : 1 ≤ q.height := Order.one_le_iff_ne_zero.mpr
      (Ideal.height_eq_zero_iff_eq_bot.not.mpr hqbot)
    have hbad := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hheight p hp] at hbad
    have htwo : (2 : ℕ∞) ≤ q.height + 1 := by
      calc
        (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ q.height + 1 := add_le_add hqheight le_rfl
    have : (2 : ℕ∞) ≤ 1 := htwo.trans hbad
    norm_num at this
  · intro p
    let : IsIntegrallyClosed (Localization.AtPrime p.1) :=
      isIntegrallyClosed_of_isLocalization _ p.1.primeCompl p.1.primeCompl_le_nonZeroDivisors
    apply (IsRegularLocalRing.iff_isDomain_and_isIntegrallyClosed_of_dim_one _ ?_).mpr
    · exact ⟨inferInstance, inferInstance⟩
    · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.1, hheight p.1 p.2]
      rfl
  · intro p hp
    let : p.IsPrime := hp.isPrime
    have hxp : x ∈ p := hle p hp (Ideal.subset_span (Set.mem_singleton x))
    have hsucc := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
      ((Ideal.Quotient.eq_zero_iff_mem).mpr hxp)
    let : IsLocalRing (A ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hdimq : ringKrullDim (A ⧸ p) ≤ (n : WithBot ℕ∞) := by
      have h := hsucc.trans hdim
      rw [Nat.cast_add, Nat.cast_one] at h
      exact ENat.WithBot.add_le_add_one_right_iff.mp h
    have hquot := ih (A ⧸ p) ((finite_over_nagata_is_nagata A A hA).2 p) hdimq
    refine ⟨inferInstance, ?_⟩
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hquot

/-- Reduced local completions of a finite extension force the base completion to be reduced.
This is the normalization reduction in Stacks Tag 0331, using the product in Tag 07N9. -/
private theorem analyticallyUnramified_finite_descent (A S : Type u) [CommRing A] [CommRing S]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra A S] [Module.Finite A S]
    (hinj : Function.Injective (algebraMap A S))
    (hred : ∀ p : (IsLocalRing.maximalIdeal A).primesOver S,
      IsReduced (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.1))
        (Localization.AtPrime p.1))) : IsAnalyticallyUnramified A := by
  let m := IsLocalRing.maximalIdeal A
  let L := Localization.AtPrime m
  let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
  let : Module.Flat L C := AdicCompletion.flat_of_isNoetherian _
  let : Module.Flat A C := Module.Flat.trans A L C
  let D := fun p : m.primesOver S ↦
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.1))
      (Localization.AtPrime p.1)
  let : ∀ p, IsReduced (D p) := hred
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := C) (B := S)
  obtain ⟨_, e, _, _, _⟩ := AdicCompletion.completion_finite_extension_decomposition A S m
  let : IsReduced (TensorProduct A C S) := isReduced_of_injective e.toRingHom e.injective
  let : IsReduced C := isReduced_of_injective
    (Algebra.TensorProduct.includeLeft : C →ₐ[A] TensorProduct A C S)
    (Algebra.TensorProduct.includeLeft_injective hinj)
  let eL : A ≃ₐ[A] L := IsLocalization.atUnits A m.primeCompl (by
    intro a ha
    exact not_not.mp ha)
  obtain ⟨eC, _⟩ := AdicCompletion.exists_ringEquiv m (IsLocalRing.maximalIdeal L)
    eL.toRingEquiv (IsLocalRing.map_ringEquiv_maximalIdeal eL.toRingEquiv).symm
  exact isReduced_of_injective eC.toRingHom eC.injective

/-- Apply finite descent to the explicitly constructed integral closure in the fraction field.
The normal local factors have dimension bounded by the original ring, as in Tag 0331. -/
private theorem analyticallyUnramified_normalization_descent (n : ℕ)
    (hnormal : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsDomain B] [IsIntegrallyClosed B], IsNagataRing B →
      ringKrullDim B ≤ (n : WithBot ℕ∞) → IsAnalyticallyUnramified B)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞)) :
    IsAnalyticallyUnramified A := by
  let S := integralClosure A (FractionRing A)
  let : Module.Finite A S := isN1_of_isN2 A (FractionRing A)
    (isN2_of_isNagataRing_domain A hA)
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  let : IsIntegrallyClosed S :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have hS : IsNagataRing S := (finite_over_nagata_is_nagata A S hA).1
  have hdimS : ringKrullDim S ≤ ringKrullDim A :=
    (RingHom.IsIntegral.ringKrullDim_le_and_isMaximal_comap (algebraMap A S)
      (Algebra.IsIntegral.isIntegral (R := A) (A := S))).1
  apply analyticallyUnramified_finite_descent A S (FaithfulSMul.algebraMap_injective A S)
  intro p
  let B := Localization.AtPrime p.1
  let : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B p.1.primeCompl
    p.1.primeCompl_le_nonZeroDivisors
  have hB := (isNagataRing_localization S p.1.primeCompl hS).2.1 p.1
  have hdimB : ringKrullDim B ≤ (n : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.1 B]
    exact (Ideal.height_le_ringKrullDim_of_isPrime (I := p.1)).trans (hdimS.trans hdim)
  exact hnormal B hB hdimB

/-- A Noetherian local Nagata integral domain has reduced maximal-ideal-adic completion.
Source: Stacks Project, Algebra, Lemma Tag 0331
(blueprint: lem-weil-pbc-local-nagata-domain-analytically-unramified).

Proof (the seven steps of the blueprint node):

1. Induct on the finite Krull dimension $d=\dim A$: it is finite because the maximal ideal of a
Noetherian local ring has finitely many generators and [lem-weil-pbc-noetherian-local-dimension-
le-generators] bounds its dimension by their number. If $d=0$, the only prime of the local domain
$A$ is $(0)=\mathfrak m$, so $A$ is a field; its $\mathfrak m$-adic completion is $A$, which is
reduced. In the inductive step assume the assertion for all Noetherian local Nagata domains of
dimension strictly less than $d$. Dependencies: def-weil-pbc-adic-completion, def-weil-pbc-krull-
dimension-ring, lem-weil-pbc-noetherian-local-dimension-le-generators.

2. Let $S$ be the integral closure of $A$ in $K=\operatorname{Frac}(A)$. Since $A$ is Nagata, its
quotient by $(0)$ is N-2 [def-weil-pbc-nagata-ring], so $S$ is a finite $A$-module [def-weil-pbc-
japanese-domain]. It is a normal domain with fraction field $K$ [lem-weil-pbc-integral-closure-
finite-extension-normal], and is Nagata [lem-weil-pbc-finite-over-nagata-nagata]. Finiteness makes
$S$ Noetherian [lem-weil-pbc-finite-algebra-noetherian] and integral over $A$ [lem-weil-pbc-
finite-algebra-is-integral], so $\dim S\le d$
[proposition-proper-direct-image-constructible-complexes]. The finite fibre $S/\mathfrak mS$ has
finitely many maximal ideals by [lem-weil-pbc-finite-over-zero- dim-local-discrete-spectrum]; their
preimages are exactly the finitely many maximal ideals $\mathfrak n_1,\ldots,\mathfrak n_r$ of $S$,
since each contracts to $\mathfrak m$ [lem-weil-pbc- finite-algebra-local-radical]. Dependencies:
def-weil-pbc-nagata-ring, def-weil-pbc-japanese- domain,
lem-weil-pbc-integral-closure-finite-extension-normal, lem-weil-pbc-finite-over-nagata- nagata,
lem-weil-pbc-finite-algebra-noetherian, lem-weil-pbc-finite-algebra-is-integral, lem-weil-
pbc-integral-extension-dimension, lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum, lem-
weil-pbc-finite-algebra-local-radical.

3. The inclusion $A\hookrightarrow S$ is an injection of finite $A$-modules, with finite cokernel
because $A$ is Noetherian. Exactness of completion on finite modules [lem-weil-pbc-completion-
exact-finite-modules] makes the induced ring map $\widehat A_{\mathfrak m}\hookrightarrow\widehat
S_{\mathfrak mS}$ injective. Hence reducedness of the latter implies reducedness of $\widehat
A_{\mathfrak m}$. Dependencies: lem-weil-pbc-completion-exact-finite-modules.

4. For each $n\ge1$, $A/\mathfrak m^n$ is Artinian local [lem-weil-pbc-noetherian-local-quotient-
artinian-local]. The finite algebra $B_n=S/\mathfrak m^nS$ over it has exactly the maximal ideals
$\mathfrak n_i/\mathfrak m^nS$ and Jacobson radical consisting of nilpotent elements [lem-weil-
pbc-finite-over-zero-dim-local-discrete-spectrum]. The product decomposition [lem-weil-pbc-
product-of-localizations-at-maximal], with each factor identified by [lem-weil-pbc-localization-
at-prime-of-quotient], gives $B_n\cong\prod_i S_{\mathfrak n_i}/\mathfrak m^nS_{\mathfrak n_i}$,
compatibly with reduction in $n$. Taking compatible inverse limits yields $\widehat S_{\mathfrak
mS}\cong\prod_i\varprojlim_n S_{\mathfrak n_i}/\mathfrak m^nS_{\mathfrak n_i}$. Put
$J=\bigcap_i\mathfrak n_i$. The ideal $J/\mathfrak mS$ is finitely generated, since $S/\mathfrak
mS$ is Noetherian [lem-weil-pbc-finite-algebra-noetherian] and [lem-weil-pbc-noetherian-submodule-
finite] applies; each generator is nilpotent by the finite-fibre result, so a sufficiently high
power of their ideal vanishes. Thus $J^N\subseteq\mathfrak mS$ for some $N$, whereas $\mathfrak
mS\subseteq J$. On localization at $\mathfrak n_i$, distinct maximal ideals become the unit ideal,
so $JS_{\mathfrak n_i}=\mathfrak n_iS_{\mathfrak n_i}$. Thus the powers of $\mathfrak
mS_{\mathfrak n_i}$ and $\mathfrak n_iS_{\mathfrak n_i}$ are cofinal, and [lem-weil-pbc-change-
ideal-completion] identifies each displayed inverse limit with $\widehat{S_{\mathfrak
n_i}}_{\mathfrak n_i}$. Consequently $\widehat S_{\mathfrak mS}\cong\prod_i\widehat{S_{\mathfrak
n_i}}_{\mathfrak n_i}$. Dependencies: lem-weil-pbc-noetherian-local-quotient-artinian-local, lem-
weil-pbc-finite-over-zero-dim-local-discrete-spectrum, lem-weil-pbc-product-of-localizations-at-
maximal, lem-weil-pbc-localization-at-prime-of-quotient, lem-weil-pbc-finite-algebra-noetherian,
lem-weil-pbc-noetherian-submodule-finite, lem-weil-pbc-change-ideal-completion.

5. Each $S_{\mathfrak n_i}$ is a Noetherian local normal domain of dimension at most $d$ by [lem-
weil-pbc-localization-dimension-chains-below-prime], and is Nagata by [lem-weil-pbc-nagata-
localization]. If its dimension is less than $d$, the induction hypothesis gives reduced
completion. For factors of dimension $d$ it remains to prove the assertion for a normal local
Nagata domain $R$ of dimension $d$; the argument in the next two steps does this. Products of
reduced rings are reduced, so this proves reducedness of $\widehat S_{\mathfrak mS}$ and then, by
step 3, of $\widehat A_{\mathfrak m}$. Dependencies: lem-weil-pbc-localization-normal-domain, lem-
weil-pbc-nagata-localization, lem-weil-pbc-localization-dimension-chains-below-prime.

6. Let $(R,\mathfrak n)$ be a Noetherian normal local Nagata domain with $\dim R=d>0$. Choose
$0\ne x\in\mathfrak n$. Since $xR=R\cap xR$ inside $\operatorname{Frac}(R)$, [lem-weil-pbc-normal-
domain-fractional-principal-quotient-ass] says $R/xR$ has no embedded associated primes and every
associated prime $\mathfrak p$ has height one. The localization $R_{\mathfrak p}$ is a one-
dimensional Noetherian normal local domain: normality comes from [lem-weil-pbc-localization-
normal-domain], and its dimension is one by [lem-weil-pbc-localization-dimension-chains-below-
prime]. Hence it is regular by [lem-weil-pbc-regular-local-dim-one-iff-normal]. This verifies
conditions (2) and (3)(a) of [lem-weil-pbc-analytic-unramified-principal-criterion], while $x\ne0$
and $x\in\mathfrak n$ verify its condition (1). Dependencies: lem-weil-pbc-normal-domain-
fractional-principal-quotient-ass, lem-weil-pbc-localization-normal-domain, lem-weil-pbc-
localization-dimension-chains-below-prime, lem-weil-pbc-regular-local-dim-one-iff-normal, lem-
weil-pbc-analytic-unramified-principal-criterion.

7. For each associated prime $\mathfrak p$ above, $R/\mathfrak p$ is a Noetherian local domain and
is Nagata by the quotient clause of [lem-weil-pbc-finite-over-nagata-nagata]. Its dimension is
strictly less than $d$: any chain of primes above $\mathfrak p$ lifts to a chain in $R$, and
prepending $(0)\subsetneq\mathfrak p$ lengthens it by one. The induction hypothesis therefore says
$R/\mathfrak p$ is analytically unramified, verifying condition (3)(b). Apply [lem-weil-pbc-
analytic-unramified-principal-criterion] with $t=x$ to obtain reducedness of $\widehat
R_{\mathfrak n}$, completing the normal case and the induction. Dependencies: lem-weil-pbc-finite-
over-nagata-nagata, lem-weil-pbc-analytic-unramified-principal-criterion. -/
theorem isAnalyticallyUnramified_of_isNagataRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] (hA : IsNagataRing A) :
    IsAnalyticallyUnramified A := by
  have hbound : ∀ n : ℕ, ∀ (B : Type u) [CommRing B] [IsNoetherianRing B]
      [IsLocalRing B] [IsDomain B], IsNagataRing B →
      ringKrullDim B ≤ (n : WithBot ℕ∞) → IsAnalyticallyUnramified B := by
    intro n
    induction n with
    | zero =>
      intro B _ _ _ _ _ hdim
      let : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.mpr hdim
      exact analyticallyUnramified_of_field B Ring.KrullDimLE.isField_of_isDomain
    | succ n ih =>
      intro B _ _ _ _ hB hdim
      apply analyticallyUnramified_normalization_descent (n + 1) ?_ B hB hdim
      intro R _ _ _ _ _ hR hdimR
      exact analyticallyUnramified_normal_step n ih R hR hdimR
  exact hbound (IsLocalRing.maximalIdeal A).spanFinrank A hA
    (ringKrullDim_le_spanFinrank_maximalIdeal A)
