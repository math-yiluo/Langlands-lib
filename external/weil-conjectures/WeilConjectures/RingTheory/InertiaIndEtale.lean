/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.GenericEtale
public import WeilConjectures.RingTheory.InertiaStrictHenselization
public import WeilConjectures.RingTheory.InertiaUnramifiedPoint
public import WeilConjectures.RingTheory.ProEtale.IndEtaleDirectedUnion

/-!
# The inertia invariants of `B_Q` are ind-étale

Let `R` be a domain with fraction field `K`, `Ω` a Galois extension of `K`, `B` the integral
closure of `R` in `Ω` and `Q` a prime of `B`. The ring `A = B_Q^{I_Q}` of invariants of the
inertia group of `Q` acting on the localization `B_Q` (`Ideal.inertiaInvariants`) is an
`R`-subalgebra of `B_Q`; for `Ω` separably closed it is strictly henselian
(`Ideal.isStrictlyHenselianLocalRing_inertiaInvariants`).

* Every element of `A` is a fraction `t / u` of inertia invariant elements of `B` with `u ∉ Q`
  (`Ideal.exists_mul_eq_of_mem_inertiaInvariants`), by multiplying numerator and denominator by
  the product over the (finite) inertia orbit of the denominator.
* For `R` a Dedekind domain and `Q` maximal over a maximal ideal `m` with perfect residue field,
  `A` is ind-étale over `R` (`Ideal.indEtale_inertiaInvariants`): every finite subset of `A` lies
  in an étale `R`-subalgebra (`Ideal.exists_etale_subalgebra_inertiaInvariants`), obtained from a
  localization of the integral closure of `R` in a finite subextension of `Ω^{I_Q} / K` at the
  point below `Q`, which is étale by generic étaleness
  (`Algebra.exists_etale_isLocalizationAway_integralClosure`) and since points fixed by inertia
  are étale (`Ideal.exists_etale_localization_away_of_inertia`).
* For `0 ≠ ϖ ∈ m`, the localization `A[1/ϖ]` is the fixed field `Ω^{I_Q}`
  (`Ideal.isLocalization_away_inertiaInvariants`): `A` is a local domain of dimension one.

This is the strict henselization at a boundary point of blueprint
`lemma-boundary-stalk--1`, as an ind-étale algebra over an affine chart.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace Ideal

section Invariants

variable {R : Type*} (K : Type*) {Ω : Type*} [CommRing R] [Field K] [Field Ω] [Algebra R K]
  [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]

/-- The ring `B_Q^{I_Q}` of inertia invariants of the localization `B_Q`, as an `R`-subalgebra.
(blueprint `lemma-boundary-stalk--1`) -/
noncomputable def inertiaInvariants : Subalgebra R (Localization.AtPrime Q) :=
  letI := inertiaAtPrimeAction Q Gal(Ω/K)
  { FixedPoints.subring (Localization.AtPrime Q) (Q.inertia Gal(Ω/K)) with
    algebraMap_mem' := fun r g ↦
      atPrimeMap_algebraMap_base Q g.1 (inertia_le_stabilizer Q g.2) r }

variable {K Q} in
lemma mem_inertiaInvariants {x : Localization.AtPrime Q} :
    x ∈ inertiaInvariants K Q ↔ ∀ σ (hσ : σ ∈ Q.inertia Gal(Ω/K)),
      atPrimeMap Q σ (inertia_le_stabilizer Q hσ) x = x := by
  have : x ∈ inertiaInvariants K Q ↔ ∀ g : Q.inertia Gal(Ω/K),
      atPrimeMap Q g.1 (inertia_le_stabilizer Q g.2) x = x := Iff.rfl
  rw [this]
  exact ⟨fun h σ hσ ↦ h ⟨σ, hσ⟩, fun h g ↦ h g.1 g.2⟩

/-- The inertia invariants of `B_Q` are strictly henselian. -/
theorem isStrictlyHenselianLocalRing_inertiaInvariants [IsSepClosed Ω]
    [Algebra.IsAlgebraic R Ω] (hR : Function.Injective (algebraMap R Ω)) :
    IsStrictlyHenselianLocalRing (inertiaInvariants K Q) := by
  let _ := inertiaAtPrimeAction Q Gal(Ω/K)
  have := isStrictlyHenselianLocalRing_fixedPoints_atPrime Q Gal(Ω/K) hR
  exact .of_ringEquiv (R := FixedPoints.subring (Localization.AtPrime Q) (Q.inertia Gal(Ω/K)))
    { toFun x := ⟨x.1, x.2⟩
      invFun x := ⟨x.1, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }

/-- The inclusion of the inertia invariants `B_Q^{I_Q} ⊆ Ω`. -/
noncomputable def inertiaInvariantsToField : inertiaInvariants K Q →ₐ[R] Ω where
  toRingHom := (atPrimeToField Q).comp (inertiaInvariants K Q).val.toRingHom
  commutes' r := by
    change atPrimeToField Q (algebraMap R (Localization.AtPrime Q) r) = _
    rw [IsScalarTower.algebraMap_apply R (integralClosure R Ω) (Localization.AtPrime Q),
      atPrimeToField_algebraMap]
    rfl

lemma inertiaInvariantsToField_apply (a : inertiaInvariants K Q) :
    inertiaInvariantsToField K Q a = atPrimeToField Q a :=
  rfl

lemma injective_inertiaInvariantsToField :
    Function.Injective (inertiaInvariantsToField K Q) :=
  (injective_atPrimeToField Q).comp Subtype.val_injective

lemma inertiaInvariantsToField_fixed (a : inertiaInvariants K Q) {σ : Gal(Ω/K)}
    (hσ : σ ∈ Q.inertia Gal(Ω/K)) :
    σ (inertiaInvariantsToField K Q a) = inertiaInvariantsToField K Q a := by
  have h := atPrimeToField_atPrimeMap Q σ (inertia_le_stabilizer Q hσ)
    (a : Localization.AtPrime Q)
  rw [mem_inertiaInvariants.1 a.2 σ hσ, AlgEquiv.smul_def] at h
  exact h.symm

/-- An element of `B` fixed by the inertia group, as an element of `B_Q^{I_Q}`. -/
noncomputable def inertiaInvariantsOfFixed (b : integralClosure R Ω)
    (hb : ∀ σ ∈ Q.inertia Gal(Ω/K), σ • b = b) : inertiaInvariants K Q :=
  ⟨algebraMap _ _ b, mem_inertiaInvariants.2 fun σ hσ ↦ by
    rw [atPrimeMap_algebraMap, hb σ hσ]⟩

@[simp]
lemma coe_inertiaInvariantsOfFixed (b : integralClosure R Ω)
    (hb : ∀ σ ∈ Q.inertia Gal(Ω/K), σ • b = b) :
    (inertiaInvariantsOfFixed K Q b hb : Localization.AtPrime Q) = algebraMap _ _ b :=
  rfl

@[simp]
lemma inertiaInvariantsToField_ofFixed (b : integralClosure R Ω)
    (hb : ∀ σ ∈ Q.inertia Gal(Ω/K), σ • b = b) :
    inertiaInvariantsToField K Q (inertiaInvariantsOfFixed K Q b hb) = b :=
  atPrimeToField_algebraMap Q b

/-- An element of `B_Q^{I_Q}` which is a unit of `B_Q` is a unit. -/
lemma isUnit_of_isUnit_coe {a : inertiaInvariants K Q}
    (ha : IsUnit (a : Localization.AtPrime Q)) : IsUnit a := by
  set b := (ha.unit⁻¹ : (Localization.AtPrime Q)ˣ).1
  have hba : b * a = 1 := ha.val_inv_mul
  have hb : b ∈ inertiaInvariants K Q := mem_inertiaInvariants.2 fun σ hσ ↦ by
    have h1 := congrArg (atPrimeMap Q σ (inertia_le_stabilizer Q hσ)) hba
    rw [map_mul, map_one, mem_inertiaInvariants.1 a.2 σ hσ] at h1
    calc atPrimeMap Q σ _ b = atPrimeMap Q σ _ b * (a * b) := by
          rw [mul_comm (a : Localization.AtPrime Q), hba, mul_one]
      _ = b := by rw [← mul_assoc, h1, one_mul]
  exact IsUnit.of_mul_eq_one (⟨b, hb⟩ : inertiaInvariants K Q) (Subtype.ext (by
    change (a : Localization.AtPrime Q) * b = 1
    rw [mul_comm, hba]))

lemma isUnit_inertiaInvariantsOfFixed (b : integralClosure R Ω)
    (hb : ∀ σ ∈ Q.inertia Gal(Ω/K), σ • b = b) (hbQ : b ∉ Q) :
    IsUnit (inertiaInvariantsOfFixed K Q b hb) :=
  isUnit_of_isUnit_coe K Q (IsLocalization.map_units _ (⟨b, hbQ⟩ : Q.primeCompl))

instance : IsLocalHom (inertiaInvariants K Q).val.toRingHom :=
  ⟨fun _ ha ↦ isUnit_of_isUnit_coe K Q ha⟩

variable [Algebra.IsAlgebraic K Ω]

/-- **Inertia invariant fractions.** Every element of `B_Q^{I_Q}` is a fraction `t / u` of
inertia invariant elements of `B` with `u ∉ Q`: the denominator of a fraction `b / c` is made
invariant by multiplying with the other members of the (finite) inertia orbit of `c`. -/
theorem exists_mul_eq_of_mem_inertiaInvariants (a : inertiaInvariants K Q) :
    ∃ t u : integralClosure R Ω, (∀ σ ∈ Q.inertia Gal(Ω/K), σ • t = t) ∧
      (∀ σ ∈ Q.inertia Gal(Ω/K), σ • u = u) ∧ u ∉ Q ∧
      algebraMap _ (Localization.AtPrime Q) u * a = algebraMap _ _ t := by
  classical
  set I := Q.inertia Gal(Ω/K)
  obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj Q.primeCompl (a : Localization.AtPrime Q)
  -- the inertia orbit of `c` is finite: it consists of roots of the minimal polynomial of `c`
  have hfin : (MulAction.orbit I (c : integralClosure R Ω)).Finite := by
    refine ((minpoly K (c.1 : Ω)).rootSet Ω).toFinite.preimage
      Subtype.val_injective.injOn |>.subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [Set.mem_preimage, Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := K) _), ?_⟩
    change Polynomial.aeval ((σ : Gal(Ω/K)) (c.1 : Ω)) _ = 0
    rw [← AlgEquiv.coe_toAlgHom, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set F := hfin.toFinset
  have hcF : (c : integralClosure R Ω) ∈ F := hfin.mem_toFinset.2 (MulAction.mem_orbit_self _)
  have hFQ : ∀ y ∈ F, y ∉ Q := by
    intro y hy
    obtain ⟨σ, rfl⟩ := hfin.mem_toFinset.1 hy
    intro h
    have hs : (σ : Gal(Ω/K)) • Q = Q := inertia_le_stabilizer Q σ.2
    apply c.2
    change (c : integralClosure R Ω) ∈ Q
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := (σ : Gal(Ω/K))), hs]
    exact h
  have hFinv : ∀ σ ∈ I, σ • ∏ y ∈ F, y = ∏ y ∈ F, y := by
    intro σ hσ
    rw [Finset.smul_prod']
    refine Finset.prod_nbij' (σ • ·) (σ⁻¹ • ·) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨τ, rfl⟩ := hfin.mem_toFinset.1 hy
      exact hfin.mem_toFinset.2 ⟨⟨σ, hσ⟩ * τ, mul_smul _ _ _⟩
    · intro y hy
      obtain ⟨τ, rfl⟩ := hfin.mem_toFinset.1 hy
      exact hfin.mem_toFinset.2 ⟨⟨σ, hσ⟩⁻¹ * τ, mul_smul _ _ _⟩
    · intro y _
      exact inv_smul_smul σ y
    · intro y _
      exact smul_inv_smul σ y
    · intro y _
      rfl
  set P' := ∏ y ∈ F.erase (c : integralClosure R Ω), y
  have hP : ∏ y ∈ F, y = c * P' := (Finset.mul_prod_erase F id hcF).symm
  have hPQ : ∏ y ∈ F, y ∉ Q := by
    intro h
    obtain ⟨y, hy, hyQ⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hFQ y hy hyQ
  have key : algebraMap _ (Localization.AtPrime Q) (∏ y ∈ F, y) * a =
      algebraMap _ _ (b * P') := by
    rw [hP, map_mul, map_mul, ← hbc]
    ring
  refine ⟨b * P', ∏ y ∈ F, y, ?_, hFinv, hPQ, key⟩
  intro σ hσ
  apply IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
  have h := congrArg (atPrimeMap Q σ (inertia_le_stabilizer Q hσ)) key
  rw [map_mul, atPrimeMap_algebraMap, atPrimeMap_algebraMap, hFinv σ hσ,
    mem_inertiaInvariants.1 a.2 σ hσ, key] at h
  exact h.symm

omit [Algebra.IsAlgebraic K Ω] in
/-- Let `φ : T' → B` be an injective `R`-algebra map with inertia invariant image and `g ∈ T'`
with `φ(g) ∉ Q` and `T'[1/g]` étale over `R`. Then elements of `B_Q^{I_Q}` which are fractions of
images of elements of `T'` with denominators outside `Q` lie in an étale `R`-subalgebra: the
image of a further localization `T'[1/(g u)]`. -/
theorem exists_etale_subalgebra_of_ringHom {T' : Type*} [CommRing T'] [Algebra R T']
    (φ : T' →+* integralClosure R Ω) (hφR : ∀ r, φ (algebraMap R T' r) = algebraMap R _ r)
    (hφinj : Function.Injective φ) (hφI : ∀ y, ∀ σ ∈ Q.inertia Gal(Ω/K), σ • φ y = φ y)
    (g : T') [Algebra.Etale R (Localization.Away g)] (hg : φ g ∉ Q)
    (S : Finset (inertiaInvariants K Q))
    (hS : ∀ s ∈ S, ∃ t' u' : T', φ u' ∉ Q ∧
      algebraMap _ (Localization.AtPrime Q) (φ u') * s = algebraMap _ _ (φ t')) :
    ∃ E : Subalgebra R (inertiaInvariants K Q), Algebra.Etale R E ∧ ∀ s ∈ S, s ∈ E := by
  classical
  choose! tT' uT' huQ htu using hS
  let Φ₁ : T' →+* inertiaInvariants K Q :=
    ((algebraMap _ (Localization.AtPrime Q)).comp φ).codRestrict
      (inertiaInvariants K Q) fun y ↦ (inertiaInvariantsOfFixed K Q _ (hφI y)).2
  have hΦ₁ (y : T') : Φ₁ y = inertiaInvariantsOfFixed K Q _ (hφI y) := rfl
  set U : T' := ∏ s ∈ S, uT' s
  have hgUQ : φ (g * U) ∉ Q := by
    rw [map_mul, map_prod]
    refine (inferInstance : Q.IsPrime).mul_notMem hg ?_
    intro h
    obtain ⟨s, hs, hsQ⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact huQ s hs hsQ
  have hunit : IsUnit (Φ₁ (g * U)) := by
    rw [hΦ₁]
    exact isUnit_inertiaInvariantsOfFixed K Q _ _ hgUQ
  -- the étale algebra `P = T'[1/(g U)]` and its map to `B_Q^{I_Q}`
  let P := Localization.Away (algebraMap T' (Localization.Away g) U)
  have : IsScalarTower R T' P := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away g) P,
      IsScalarTower.algebraMap_apply R T' (Localization.Away g),
      IsScalarTower.algebraMap_apply T' (Localization.Away g) P (algebraMap R T' r)]
  let Φr : P →+* inertiaInvariants K Q := IsLocalization.Away.lift (g * U) hunit
  have hΦr (y : T') : Φr (algebraMap T' P y) = Φ₁ y := IsLocalization.Away.lift_eq _ _ y
  have hΦ₁R (r : R) : Φ₁ (algebraMap R T' r) = algebraMap R _ r := by
    apply Subtype.ext
    change algebraMap _ (Localization.AtPrime Q) (φ (algebraMap R T' r)) = _
    rw [hφR, ← IsScalarTower.algebraMap_apply]
    rfl
  let Φ : P →ₐ[R] inertiaInvariants K Q :=
    { Φr with
      commutes' r := by
        change Φr (algebraMap R P r) = _
        rw [IsScalarTower.algebraMap_apply R T' P, hΦr, hΦ₁R] }
  have hΦP (y : T') : Φ (algebraMap T' P y) = Φ₁ y := hΦr y
  have hinj : Function.Injective Φ := by
    have hχ (y : T') : inertiaInvariantsToField K Q (Φ (algebraMap T' P y)) = φ y := by
      rw [hΦP, hΦ₁, inertiaInvariantsToField_ofFixed]
    refine (injective_iff_map_eq_zero Φ).2 fun z hz ↦ ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (g * U)) z
    have h := congrArg (fun z ↦ inertiaInvariantsToField K Q (Φ z))
      (IsLocalization.mk'_spec P a b)
    simp only [map_mul, hz, map_zero, zero_mul, hχ] at h
    have ha : a = 0 := hφinj (by rw [map_zero]; exact Subtype.ext h.symm)
    change IsLocalization.mk' P a b = 0
    rw [ha, IsLocalization.mk'_zero]
  refine ⟨Φ.range, Algebra.Etale.of_equiv (AlgEquiv.ofInjective Φ hinj), fun s hs ↦ ?_⟩
  -- `s = t / u` lies in the image
  set a : T' := tT' s * (∏ s' ∈ S.erase s, uT' s') * g
  refine ⟨IsLocalization.mk' P a (⟨g * U, Submonoid.mem_powers _⟩ : Submonoid.powers (g * U)),
    ?_⟩
  have hspec := congrArg Φ (IsLocalization.mk'_spec P a
    (⟨g * U, Submonoid.mem_powers _⟩ : Submonoid.powers (g * U)))
  rw [map_mul, hΦP, hΦP] at hspec
  refine (hunit.mul_left_inj).1 (hspec.trans ?_)
  have hU : U = uT' s * ∏ s' ∈ S.erase s, uT' s' := (Finset.mul_prod_erase S uT' hs).symm
  have hsu : s * Φ₁ (uT' s) = Φ₁ (tT' s) := by
    apply Subtype.ext
    change (s : Localization.AtPrime Q) * algebraMap _ _ (φ (uT' s)) = algebraMap _ _ (φ (tT' s))
    rw [mul_comm]
    exact htu s hs
  change Φ₁ a = s * Φ₁ (g * U)
  rw [hU, map_mul, map_mul, map_mul, map_mul, ← hsu]
  ring

omit [Algebra.IsAlgebraic K Ω] in
/-- If `R ⧸ m` is finite, the residue field of `B_Q^{I_Q}` is integral over `ℤ`: it embeds in the
residue field `B ⧸ Q` of `B_Q`, which is integral over the finite field `R ⧸ m`. -/
theorem isIntegralElem_residueField_inertiaInvariants [Q.IsMaximal] (m : Ideal R) [Q.LiesOver m]
    [Finite (R ⧸ m)] [IsLocalRing (inertiaInvariants K Q)]
    (y : IsLocalRing.ResidueField (inertiaInvariants K Q)) :
    (Int.castRingHom (IsLocalRing.ResidueField (inertiaInvariants K Q))).IsIntegralElem y := by
  let f : IsLocalRing.ResidueField (inertiaInvariants K Q) →+*
      IsLocalRing.ResidueField (Localization.AtPrime Q) :=
    IsLocalRing.ResidueField.map (inertiaInvariants K Q).val.toRingHom
  let e : IsLocalRing.ResidueField (Localization.AtPrime Q) ≃+* (integralClosure R Ω ⧸ Q) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Localization.AtPrime Q)).symm.toRingEquiv
  let g := e.toRingHom.comp f
  have hg : Function.Injective g := e.injective.comp f.injective
  have : Algebra.IsIntegral R (integralClosure R Ω) := integralClosure.AlgebraIsIntegral
  have : Algebra.IsIntegral ℤ (integralClosure R Ω ⧸ Q) := Algebra.IsIntegral.trans (R ⧸ m)
  obtain ⟨p, hp, hpy⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) (g y)
  refine ⟨p, hp, hg ?_⟩
  rw [map_zero, Polynomial.hom_eval₂, ← hpy]
  congr 1
  exact RingHom.ext_int _ _

section Decomposition

omit [Algebra.IsAlgebraic K Ω]

lemma atPrimeMap_congr {σ τ : Gal(Ω/K)} (h : σ = τ) (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q)
    (hτ : τ ∈ MulAction.stabilizer Gal(Ω/K) Q) (a : Localization.AtPrime Q) :
    atPrimeMap Q σ hσ a = atPrimeMap Q τ hτ a := by
  subst h
  rfl

omit [Q.IsPrime] in
/-- The inertia group is normalised by the decomposition group. -/
lemma inv_mul_mul_mem_inertia {σ τ : Gal(Ω/K)} (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q)
    (hτ : τ ∈ Q.inertia Gal(Ω/K)) : σ⁻¹ * τ * σ ∈ Q.inertia Gal(Ω/K) := by
  intro b
  have hσ' : σ⁻¹ • Q = Q := by
    rw [inv_smul_eq_iff]
    exact (MulAction.mem_stabilizer_iff.1 hσ).symm
  have h := Ideal.smul_mem_pointwise_smul σ⁻¹ _ _ (hτ (σ • b))
  rw [hσ', smul_sub, inv_smul_smul] at h
  rwa [mul_smul, mul_smul]

/-- The action on `B_Q^{I_Q}` of an element `σ` of the decomposition group of `Q`, which
normalises the inertia group. -/
noncomputable def inertiaInvariantsMap {σ : Gal(Ω/K)} (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q) :
    inertiaInvariants K Q →+* inertiaInvariants K Q :=
  ((atPrimeMap Q σ hσ).comp (inertiaInvariants K Q).val.toRingHom).codRestrict
    (inertiaInvariants K Q) fun a ↦ mem_inertiaInvariants.2 fun τ hτ ↦ by
      have hρ := inv_mul_mul_mem_inertia K Q hσ hτ
      change atPrimeMap Q τ _ (atPrimeMap Q σ hσ a) = atPrimeMap Q σ hσ a
      rw [← atPrimeMap_mul Q (inertia_le_stabilizer Q hτ) hσ,
        atPrimeMap_congr K Q (show τ * σ = σ * (σ⁻¹ * τ * σ) by group) _
          (mul_mem hσ (inertia_le_stabilizer Q hρ)),
        atPrimeMap_mul Q hσ (inertia_le_stabilizer Q hρ), mem_inertiaInvariants.1 a.2 _ hρ]

variable {K Q}

lemma coe_inertiaInvariantsMap {σ : Gal(Ω/K)} (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q)
    (a : inertiaInvariants K Q) :
    (inertiaInvariantsMap K Q hσ a : Localization.AtPrime Q) = atPrimeMap Q σ hσ a :=
  rfl

lemma inertiaInvariantsToField_inertiaInvariantsMap {σ : Gal(Ω/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q) (a : inertiaInvariants K Q) :
    inertiaInvariantsToField K Q (inertiaInvariantsMap K Q hσ a) =
      σ (inertiaInvariantsToField K Q a) := by
  rw [inertiaInvariantsToField_apply, coe_inertiaInvariantsMap, atPrimeToField_atPrimeMap,
    AlgEquiv.smul_def]
  rfl

lemma inertiaInvariantsMap_algebraMap {σ : Gal(Ω/K)} (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q)
    (r : R) : inertiaInvariantsMap K Q hσ (algebraMap R _ r) = algebraMap R _ r :=
  Subtype.ext (atPrimeMap_algebraMap_base Q σ hσ r)

lemma isUnit_of_isUnit_inertiaInvariantsMap {σ : Gal(Ω/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q) {a : inertiaInvariants K Q}
    (ha : IsUnit (inertiaInvariantsMap K Q hσ a)) : IsUnit a := by
  refine isUnit_of_isUnit_coe K Q ?_
  have h : IsUnit (atPrimeMap Q σ hσ (a : Localization.AtPrime Q)) :=
    ha.map (inertiaInvariants K Q).val
  exact (isUnit_map_iff (atPrimeMap Q σ hσ) _).1 h

end Decomposition

end Invariants

section IndEtale

variable {R : Type*} (K : Type*) {Ω : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Field Ω] [Algebra R K] [IsFractionRing R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] (m : Ideal R) [m.IsMaximal] [PerfectField m.ResidueField]
  (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] [Q.LiesOver m]

-- the elaboration of the localization and integral closure instances is slow
include m in
/-- **Finite subsets of `B_Q^{I_Q}` lie in étale subalgebras.** Write the elements as fractions
`t / u` of inertia invariant elements of `B` with `u ∉ Q`, let `L` be the (finite, inertia
invariant) subextension of `Ω / K` they generate and `T` the integral closure of `R` in `L`.
By generic étaleness `T[1/π]` is finite étale over `R[1/π]` for some `π ≠ 0`, and since its
image is fixed by inertia, the integral closure `T'` of `R` in `T[1/π]` is étale over `R` after
inverting some `g` not in the point below `Q`. Then `T'[1/(g ∏ u)]` embeds in `B_Q^{I_Q}` as an
étale `R`-subalgebra containing the given elements. -/
theorem exists_etale_subalgebra_inertiaInvariants (S : Finset (inertiaInvariants K Q)) :
    ∃ E : Subalgebra R (inertiaInvariants K Q), Algebra.Etale R E ∧ ∀ s ∈ S, s ∈ E := by
  classical
  set I := Q.inertia Gal(Ω/K)
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  choose t u ht hu huQ htu using exists_mul_eq_of_mem_inertiaInvariants K Q
  -- the finite inertia invariant subextension `L` generated by numerators and denominators
  let gens : Set Ω := (fun s ↦ (t s : Ω)) '' S ∪ (fun s ↦ (u s : Ω)) '' S
  have : Finite gens := ((S.finite_toSet.image _).union (S.finite_toSet.image _)).to_subtype
  let L : IntermediateField K Ω := IntermediateField.adjoin K gens
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  have hLI : ∀ σ ∈ I, ∀ x ∈ L, σ x = x := by
    intro σ hσ
    have hle : L ≤ IntermediateField.fixedField I := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;>
        refine (IntermediateField.mem_fixedField_iff _ _).2 fun τ hτ ↦ ?_
      · exact congrArg Subtype.val (ht s τ hτ)
      · exact congrArg Subtype.val (hu s τ hτ)
    exact fun x hx ↦ (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) σ hσ
  have htL : ∀ s ∈ S, (t s : Ω) ∈ L := fun s hs ↦
    IntermediateField.subset_adjoin K _ (Or.inl ⟨s, hs, rfl⟩)
  have huL : ∀ s ∈ S, (u s : Ω) ∈ L := fun s hs ↦
    IntermediateField.subset_adjoin K _ (Or.inr ⟨s, hs, rfl⟩)
  -- generic étaleness of the integral closure `T` of `R` in `L`
  let T := integralClosure R L
  obtain ⟨π, hπ, H⟩ :=
    Algebra.exists_etale_isLocalizationAway_integralClosure (R := R) (K := K) (L := L)
  let R' := Localization.Away π
  let A' := Localization (Algebra.algebraMapSubmonoid T (Submonoid.powers π))
  have : IsLocalization.Away (algebraMap R T π) A' := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  obtain ⟨_, _, _⟩ := H R' A'
  -- the map `T[1/π] → Ω`
  let gT : T →+* Ω := L.val.toRingHom.comp (integralClosure R L).val.toRingHom
  have hgT (y : Algebra.algebraMapSubmonoid T (Submonoid.powers π)) : IsUnit (gT y) := by
    obtain ⟨_, ⟨n, rfl⟩, hy⟩ := y.2
    rw [← hy]
    refine IsUnit.mk0 _ ?_
    change algebraMap R Ω (π ^ n) ≠ 0
    exact (map_ne_zero_iff _ hRΩ).2 (pow_ne_zero n hπ)
  let ψ₀r : A' →+* Ω := IsLocalization.lift hgT
  have hψ₀r (y : T) : ψ₀r (algebraMap T A' y) = gT y := IsLocalization.lift_eq hgT y
  let ψ₀ : A' →ₐ[R] Ω :=
    { ψ₀r with
      commutes' r := by
        change ψ₀r (algebraMap R A' r) = _
        rw [IsScalarTower.algebraMap_apply R T A', hψ₀r]
        rfl }
  have hI : ∀ σ ∈ I, ∀ x : A', σ (ψ₀ x) = ψ₀ x := by
    intro σ hσ x
    have : (σ.toRingHom).comp ψ₀r = ψ₀r :=
      IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid T (Submonoid.powers π))
        (RingHom.ext fun y ↦ by
          simp only [RingHom.comp_apply, hψ₀r]
          exact hLI σ hσ _ (y : L).2)
    exact RingHom.congr_fun this x
  -- points fixed by inertia are étale
  obtain ⟨g, hgQ, hgE⟩ :=
    exists_etale_localization_away_of_inertia m Q π (R' := R') (A := A') hπ ψ₀ hI
  let ψ' : integralClosure R A' →ₐ[R] Ω :=
    ψ₀.comp (IsScalarTower.toAlgHom R (integralClosure R A') A')
  have hψ'inj : Function.Injective ψ' := injective_of_isIntegral ψ' hRΩ
  -- elements of `B` in `L` come from `T'`
  have hT' (x : integralClosure R Ω) (hx : (x : Ω) ∈ L) :
      ∃ y : integralClosure R A', integralClosureMap ψ' y = x := by
    have hxL : IsIntegral R (⟨x, hx⟩ : L) := by
      rw [← isIntegral_algHom_iff (L.val.restrictScalars R) L.val.injective]
      exact x.2
    let yT : T := ⟨⟨x, hx⟩, hxL⟩
    refine ⟨⟨algebraMap T A' yT,
      (Algebra.IsIntegral.isIntegral (R := R) yT).map (IsScalarTower.toAlgHom R T A')⟩, ?_⟩
    exact Subtype.ext (hψ₀r yT)
  refine exists_etale_subalgebra_of_ringHom K Q (integralClosureMap ψ')
    (fun r ↦ Subtype.ext (ψ'.commutes r))
    (fun y z h ↦ hψ'inj (congrArg Subtype.val h)) (fun y σ hσ ↦ Subtype.ext (hI σ hσ _))
    g hgQ S fun s hs ↦ ?_
  obtain ⟨t', ht'⟩ := hT' (t s) (htL s hs)
  obtain ⟨u', hu'⟩ := hT' (u s) (huL s hs)
  exact ⟨t', u', hu' ▸ huQ s, by rw [ht', hu']; exact htu s⟩

omit [IsDedekindDomain R] [IsFractionRing R K] [IsGalois K Ω] [m.IsMaximal]
  [PerfectField m.ResidueField] in
include m in
/-- Elements of `R` outside `m` are units in `B_Q^{I_Q}`. -/
lemma isUnit_algebraMap_inertiaInvariants {r : R} (hr : r ∉ m) :
    IsUnit (algebraMap R (inertiaInvariants K Q) r) := by
  refine isUnit_of_isUnit_coe K Q ?_
  change IsUnit (algebraMap R (Localization.AtPrime Q) r)
  rw [IsScalarTower.algebraMap_apply R (integralClosure R Ω) (Localization.AtPrime Q)]
  refine IsLocalization.map_units _ (⟨algebraMap R _ r, fun h ↦ hr ?_⟩ : Q.primeCompl)
  rw [Ideal.over_def Q m]
  exact h

omit [PerfectField m.ResidueField] in
include m in
/-- `B_Q^{I_Q}` is a local domain of dimension one: a nonzero element divides a power of any
nonzero `ϖ ∈ m`. A prime containing it but not `ϖ` would meet `R` in a nonzero prime contained
in `m` (elements outside `m` being units), hence in `m`. -/
lemma exists_dvd_pow_inertiaInvariants {ϖ : R} (hϖ : ϖ ∈ m) {d : inertiaInvariants K Q}
    (hd : d ≠ 0) : ∃ n : ℕ, d ∣ algebraMap R _ ϖ ^ n := by
  by_contra! H
  have hdisj : Disjoint ((Ideal.span {d} : Ideal (inertiaInvariants K Q)) :
      Set (inertiaInvariants K Q))
      (Submonoid.powers (algebraMap R (inertiaInvariants K Q) ϖ) :
        Set (inertiaInvariants K Q)) := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨n, rfl⟩
    exact H n (Ideal.mem_span_singleton.1 hx)
  obtain ⟨P, hP, hdP, hPϖ⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  have hRK : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R Ω := Algebra.IsAlgebraic.trans R K Ω
  have halg : IsAlgebraic R d :=
    (isAlgebraic_algHom_iff (inertiaInvariantsToField K Q)
      (injective_inertiaInvariantsToField K Q)).1 (Algebra.IsAlgebraic.isAlgebraic _)
  have hne : P.comap (algebraMap R (inertiaInvariants K Q)) ≠ ⊥ :=
    Ideal.under_ne_bot_of_algebraic_mem hd (hdP (Ideal.mem_span_singleton_self d)) halg
  have hmax : (P.comap (algebraMap R (inertiaInvariants K Q))).IsMaximal :=
    (Ideal.IsPrime.comap _).isMaximal hne
  have hle : P.comap (algebraMap R (inertiaInvariants K Q)) ≤ m := fun r hr ↦ by
    by_contra hrm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hr
      (isUnit_algebraMap_inertiaInvariants K m Q hrm))
  have heq := hmax.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hle
  have hϖP : algebraMap R (inertiaInvariants K Q) ϖ ∈ P := by
    rw [← Ideal.mem_comap, heq]
    exact hϖ
  exact Set.disjoint_left.1 hPϖ hϖP (Submonoid.mem_powers _)

/-- `B_Q^{I_Q}` is contained in the fixed field `Ω^{I_Q}` of the inertia group. -/
noncomputable instance : Algebra (inertiaInvariants K Q)
    (IntermediateField.fixedField (Q.inertia Gal(Ω/K))) :=
  ((inertiaInvariantsToField K Q).toRingHom.codRestrict
    (IntermediateField.fixedField (Q.inertia Gal(Ω/K))) fun a ↦
      (IntermediateField.mem_fixedField_iff _ _).2 fun _ hσ ↦
        inertiaInvariantsToField_fixed K Q a hσ).toAlgebra

omit [IsDedekindDomain R] [IsFractionRing R K] [IsGalois K Ω] in
@[simp]
lemma coe_algebraMap_fixedField (a : inertiaInvariants K Q) :
    (algebraMap (inertiaInvariants K Q) (IntermediateField.fixedField (Q.inertia Gal(Ω/K))) a :
      Ω) = inertiaInvariantsToField K Q a :=
  rfl

omit [PerfectField m.ResidueField] in
include m in
/-- **The punctured spectrum of `B_Q^{I_Q}`.** For `0 ≠ ϖ ∈ m`, the localization `A[1/ϖ]` of
`A = B_Q^{I_Q}` is the fixed field `Ω^{I_Q}` of the inertia group.
(blueprint `lemma-boundary-stalk--1`) -/
theorem isLocalization_away_inertiaInvariants {ϖ : R} (hϖ : ϖ ∈ m) (hϖ0 : ϖ ≠ 0) :
    IsLocalization.Away (algebraMap R (inertiaInvariants K Q) ϖ)
      (IntermediateField.fixedField (Q.inertia Gal(Ω/K))) := by
  set A := inertiaInvariants K Q
  set K' := IntermediateField.fixedField (Q.inertia Gal(Ω/K))
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hinj : Function.Injective (algebraMap A K') := fun x y h ↦
    injective_inertiaInvariantsToField K Q (congrArg Subtype.val h)
  have hϖA : algebraMap R A ϖ ≠ 0 := fun h ↦ hϖ0 (hRΩ (by
    rw [map_zero, ← (inertiaInvariantsToField K Q).commutes, h, map_zero]))
  have hRK : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R Ω := Algebra.IsAlgebraic.trans R K Ω
  refine ⟨?_, fun y ↦ ?_, fun {x y} h ↦ ⟨1, by rw [hinj h]⟩⟩
  · rintro ⟨_, n, rfl⟩
    refine IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hϖA))
  · obtain ⟨d, hd0, hdy⟩ := IsAlgebraic.exists_integral_multiple
      (Algebra.IsAlgebraic.isAlgebraic (R := R) (y : Ω))
    have hfix : ∀ σ ∈ Q.inertia Gal(Ω/K),
        σ • (⟨d • (y : Ω), hdy⟩ : integralClosure R Ω) = ⟨d • (y : Ω), hdy⟩ := by
      intro σ hσ
      apply Subtype.ext
      change σ (d • (y : Ω)) = d • (y : Ω)
      rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R K Ω, AlgEquiv.commutes,
        (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ hσ]
    have hdA : algebraMap R A d ≠ 0 := fun h ↦ hd0 (hRΩ (by
      rw [map_zero, ← (inertiaInvariantsToField K Q).commutes, h, map_zero]))
    obtain ⟨n, c, hc⟩ := exists_dvd_pow_inertiaInvariants K m Q hϖ hdA
    refine ⟨⟨inertiaInvariantsOfFixed K Q _ hfix * c, ⟨_, n, rfl⟩⟩, Subtype.ext ?_⟩
    change (y : Ω) * inertiaInvariantsToField K Q (algebraMap R A ϖ ^ n) =
      inertiaInvariantsToField K Q (inertiaInvariantsOfFixed K Q _ hfix * c)
    rw [hc, map_mul, map_mul, inertiaInvariantsToField_ofFixed, AlgHom.commutes,
      ← mul_assoc]
    change _ = d • (y : Ω) * _
    rw [Algebra.smul_def, mul_comm (algebraMap R Ω d)]

end IndEtale

section IndEtaleUniverse

universe u

variable {R : Type u} (K : Type*) {Ω : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Field Ω] [Algebra R K] [IsFractionRing R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] (m : Ideal R) [m.IsMaximal] [PerfectField m.ResidueField]
  (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] [Q.LiesOver m]

include m in
/-- **The inertia invariants of `B_Q` are ind-étale** over `R`: they are the directed union of
their étale `R`-subalgebras. (blueprint `lemma-boundary-stalk--1`) -/
theorem indEtale_inertiaInvariants : Algebra.IndEtale R (inertiaInvariants K Q) := by
  classical
  refine Algebra.IndEtale.of_directedOn {E | Algebra.Etale R E} ?_ ?_ fun E hE ↦ hE
  · intro E₁ h₁ E₂ h₂
    have : Algebra.Etale R E₁ := h₁
    have : Algebra.Etale R E₂ := h₂
    obtain ⟨s₁, hs₁⟩ := (Subalgebra.fg_iff_finiteType E₁).2 inferInstance
    obtain ⟨s₂, hs₂⟩ := (Subalgebra.fg_iff_finiteType E₂).2 inferInstance
    obtain ⟨E, hE, hsE⟩ := exists_etale_subalgebra_inertiaInvariants K m Q (s₁ ∪ s₂)
    refine ⟨E, hE, ?_, ?_⟩
    · rw [← hs₁]
      exact Algebra.adjoin_le fun x hx ↦ hsE x (Finset.mem_union_left _ hx)
    · rw [← hs₂]
      exact Algebra.adjoin_le fun x hx ↦ hsE x (Finset.mem_union_right _ hx)
  · intro x
    obtain ⟨E, hE, hxE⟩ := exists_etale_subalgebra_inertiaInvariants K m Q {x}
    exact ⟨E, hE, hxE x (Finset.mem_singleton_self x)⟩

end IndEtaleUniverse

end Ideal
