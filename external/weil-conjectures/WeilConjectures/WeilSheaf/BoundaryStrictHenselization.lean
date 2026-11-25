/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.InertiaIndEtale
public import WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants

/-!
# The strict henselization at a boundary point as a pro-étale neighbourhood

Let `C₀` be an integral scheme over a finite field `k₀`, `W` an affine open with Dedekind ring
of sections `R = Γ(C₀, W)`, `x ∈ W` a point with finite residue field, `Ω` a separably closed
Galois extension of the function field `K = k(C₀)` and `Q` a maximal ideal over `x` of the
integral closure `B` of `R` in `Ω`. The ring `A = B_Q^{I_Q}` of inertia invariants is strictly
henselian and ind-étale over `R` (`Ideal.indEtale_inertiaInvariants`).

We show that `Spec A` is a weakly étale neighbourhood of the geometric point `x̄` over `x` of the
geometric fiber `C̄ = C₀ ×_{k₀} k̄`, for a suitable embedding `k̄ ⊆ A`, through the closed point of
`Spec A`. If `j : U₀ ⟶ C₀` is an open immersion with `U₀ ∩ W = D(ϖ)` for some `ϖ` in the prime
of `x`, the punctured part `Spec A ×_C̄ Ū` is the spectrum of the fixed field `K' = Ω^{I_Q}`
(`Ideal.isLocalization_away_inertiaInvariants`), and `Gal(Ω / K')` is the inertia group
(`Ideal.fixingSubgroup_fixedField_inertia`). These are the data required by
`AlgebraicGeometry.WeilSheaf.exists_injective_stalk_directImage_range_eq_invariants`, which
computes the boundary stalk of `j_* F` for a lisse Weil sheaf `F` as Galois invariants
(blueprint `lemma-boundary-stalk--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry

section ClosedPoint

variable {C : Scheme.{u}} {W : C.Opens} (hW : IsAffineOpen W) (x : C.finitePoints)
  (hxW : x.1 ∈ W)

/-- The quotient of the sections over an affine open by the prime of a point with finite residue
field is finite: it embeds in the residue field. -/
lemma IsAffineOpen.finite_quotient_primeIdealOf :
    Finite (Γ(C, W) ⧸ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal) := by
  let z : W := ⟨x.1, hxW⟩
  let _ : Algebra Γ(C, W) (C.presheaf.stalk z) := TopCat.Presheaf.algebra_section_stalk _ z
  have := hW.isLocalization_stalk z
  have : Finite (C.residueField x.1) := C.mem_finitePoints.1 x.2
  let f : Γ(C, W) →+* C.residueField x.1 :=
    (IsLocalRing.residue _).comp (algebraMap Γ(C, W) (C.presheaf.stalk z))
  have hker : RingHom.ker f = (hW.primeIdealOf z).asIdeal := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue,
      ← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal (C.presheaf.stalk z)
        (hW.primeIdealOf z).asIdeal]
  have : Finite (Γ(C, W) ⧸ RingHom.ker f) := Finite.of_injective _ (RingHom.kerLift_injective f)
  exact Finite.of_equiv _ (Ideal.quotEquivOfEq hker).toEquiv

/-- The prime of a point with finite residue field is maximal. -/
lemma IsAffineOpen.isMaximal_primeIdealOf :
    (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.IsMaximal := by
  have := hW.finite_quotient_primeIdealOf x hxW
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

end ClosedPoint

namespace Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The geometric point over a point with finite residue field lies over `Spec ι` for a
`k`-embedding `ι : κ(x) ↪ k̄`. -/
lemma exists_geometricFiberPointOfFinitePoint_comp_geometricFiberProj (x : X.finitePoints) :
    ∃ ι : X.residueField x.1 ⟶ CommRingCat.of (AlgebraicClosure k),
      ι.hom.comp (f.residueFieldAlgebraMap x.1) = algebraMap k _ ∧
      f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberProj =
        Spec.map ι ≫ X.fromSpecResidueField x.1 := by
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  exact ⟨CommRingCat.ofHom
    (IsAlgClosed.lift : X.residueField x.1 →ₐ[k] AlgebraicClosure k).toRingHom,
    RingHom.ext fun c ↦
      (IsAlgClosed.lift : X.residueField x.1 →ₐ[k] AlgebraicClosure k).commutes c,
    f.geometricFiberPoint_comp_geometricFiberProj (K := X.residueField x.1) IsAlgClosed.lift
      (X.fromSpecResidueField x.1) (f.specMap_residueFieldAlgebraMap x.1).symm⟩

lemma geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure
    (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  f.geometricFiberPoint_comp_geometricFiberToAlgebraicClosure (K := X.residueField x.1)
    IsAlgClosed.lift (X.fromSpecResidueField x.1) (f.specMap_residueFieldAlgebraMap x.1).symm

/-- The embedding `κ(x) ↪ k̄` of the geometric point over a point with finite residue field. -/
noncomputable def geometricFiberPointEmb (x : X.finitePoints) :
    X.residueField x.1 →+* AlgebraicClosure k :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  (IsAlgClosed.lift : X.residueField x.1 →ₐ[k] AlgebraicClosure k).toRingHom

lemma geometricFiberPointEmb_comp_residueFieldAlgebraMap (x : X.finitePoints) :
    (f.geometricFiberPointEmb x).comp (f.residueFieldAlgebraMap x.1) =
      algebraMap k (AlgebraicClosure k) :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  RingHom.ext fun c ↦
    (IsAlgClosed.lift : X.residueField x.1 →ₐ[k] AlgebraicClosure k).commutes c

lemma geometricFiberPointOfFinitePoint_comp_geometricFiberProj (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberProj =
      Spec.map (CommRingCat.ofHom (f.geometricFiberPointEmb x)) ≫ X.fromSpecResidueField x.1 :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  f.geometricFiberPoint_comp_geometricFiberProj (K := X.residueField x.1) IsAlgClosed.lift
    (X.fromSpecResidueField x.1) (f.specMap_residueFieldAlgebraMap x.1).symm

end Scheme.Hom

lemma specMap_apply_asIdeal {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B')
    (y : Spec (.of B')) :
    (Spec.map (CommRingCat.ofHom f) y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

/-- The image of a localization away from `a` consists of the primes not containing `a`. -/
private lemma specMap_mem_range_of_isLocalizationAway {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (a : A) [IsLocalization.Away a B] (q : Spec (.of A)) :
    q ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔ a ∉ q.asIdeal := by
  change q ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) ↔ _
  rw [PrimeSpectrum.localization_away_comap_range B a]
  exact Iff.rfl

/-- A ring map from a local ring to a field whose kernel is the maximal ideal maps the closed
point to the closed point. -/
lemma specMap_closedPoint_of_forall_eq_zero_iff {B L : Type u} [CommRing B] [IsLocalRing B]
    [Field L] (r : B →+* L) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a) :
    Spec.map (CommRingCat.ofHom r) (closedPoint L) = closedPoint B := by
  have : IsLocalHom r := ⟨fun a ha ↦ not_not.1 fun h ↦ ha.ne_zero ((hr a).2 h)⟩
  exact IsLocalRing.comap_closedPoint r

section Boundary

variable {k₀ : Type u} [Field k₀] [Finite k₀] {C : Scheme.{u}} [C.Over (Spec (.of k₀))]
  [IsIntegral C] {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W] [IsDedekindDomain Γ(C, W)]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal]

include hW

omit [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma injective_algebraMap_sections_of_isAffineOpen :
    Function.Injective (algebraMap Γ(C, W) Ω) := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  rw [IsScalarTower.algebraMap_eq Γ(C, W) C.functionField Ω]
  exact (algebraMap C.functionField Ω).injective.comp (IsFractionRing.injective _ _)

omit [IsDedekindDomain Γ(C, W)] [IsSepClosed Ω] in
lemma isAlgebraic_sections_of_isAffineOpen : Algebra.IsAlgebraic Γ(C, W) Ω := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have : Algebra.IsAlgebraic Γ(C, W) C.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(C, W))
  exact Algebra.IsAlgebraic.trans _ C.functionField Ω

omit [IsDedekindDomain Γ(C, W)] in
/-- The inertia invariants `B_Q^{I_Q}` are strictly henselian. -/
theorem isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen :
    IsStrictlyHenselianLocalRing (Ideal.inertiaInvariants C.functionField Q) :=
  have := isAlgebraic_sections_of_isAffineOpen hW (Ω := Ω)
  Ideal.isStrictlyHenselianLocalRing_inertiaInvariants _ Q
    (injective_algebraMap_sections_of_isAffineOpen hW)

variable (x : C.finitePoints) (hxW : x.1 ∈ W) [Q.LiesOver (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal]

omit [IsSepClosed Ω] in
include hxW in
/-- The inertia invariants `B_Q^{I_Q}` are ind-étale over `Γ(C, W)`. -/
theorem indEtale_inertiaInvariants_of_isAffineOpen :
    Algebra.IndEtale Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have := hW.isMaximal_primeIdealOf x hxW
  have := hW.finite_quotient_primeIdealOf x hxW
  have : Finite (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField _).2
  exact Ideal.indEtale_inertiaInvariants _ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal Q

/-- The structure map `k₀ ⟶ Γ(C, W)` of the affine chart. -/
noncomputable abbrev sectionsStructHom : k₀ →+* Γ(C, W) :=
  (Spec.preimage (hW.fromSpec ≫ (C ↘ Spec (.of k₀)))).hom

-- the codomain restrictions of the embedding of `k̄` unfold slowly
omit [IsDedekindDomain Γ(C, W)] [Finite k₀] in
include hxW in
/-- **An algebraic closure of `k₀` in `B_Q^{I_Q}`.** Let `ε₀ : k̄ ⟶ Ω` be an embedding over `k₀`.
Its image lies in `B_Q^{I_Q}`: it consists of elements integral over `k₀`, which are fixed by
inertia since a nonzero element integral over `k₀` is a unit of `B`. This gives
`ε : k̄ ⟶ B_Q^{I_Q}`, and `r : B_Q^{I_Q} ⟶ k̄` with kernel the maximal ideal such that
`r ∘ ε = id`: the residue field of `B_Q^{I_Q}` is algebraic over `k₀`, hence its embedding of
`k̄` is an isomorphism, whose inverse gives `r`. -/
theorem exists_algebraicClosure_inertiaInvariants (ε₀ : AlgebraicClosure k₀ →+* Ω)
    (hε₀ : ε₀.comp (algebraMap k₀ (AlgebraicClosure k₀)) =
      (algebraMap Γ(C, W) Ω).comp (sectionsStructHom hW)) :
    ∃ (ε : AlgebraicClosure k₀ →+* Ideal.inertiaInvariants C.functionField Q)
      (r : Ideal.inertiaInvariants C.functionField Q →+* AlgebraicClosure k₀),
      r.comp ε = RingHom.id _ ∧ (∀ a, r a = 0 ↔ ¬ IsUnit a) ∧
      (∀ y, Ideal.inertiaInvariantsToField _ Q (ε y) = ε₀ y) ∧
      (algebraMap Γ(C, W) _).comp (sectionsStructHom hW) =
        ε.comp (algebraMap k₀ (AlgebraicClosure k₀)) := by
  classical
  set K := C.functionField
  set A := Ideal.inertiaInvariants K Q
  have hRΩ := injective_algebraMap_sections_of_isAffineOpen hW (Ω := Ω)
  have := isAlgebraic_sections_of_isAffineOpen hW (Ω := Ω)
  have := isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen hW Q
  have := hW.isMaximal_primeIdealOf x hxW
  have := hW.finite_quotient_primeIdealOf x hxW
  -- the `k₀`-structures
  set φ₀ := sectionsStructHom (k₀ := k₀) hW
  let : Algebra k₀ Ω := ((algebraMap Γ(C, W) Ω).comp φ₀).toAlgebra
  let : Algebra k₀ Γ(C, W) := φ₀.toAlgebra
  have : IsScalarTower k₀ Γ(C, W) Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ε₀A : AlgebraicClosure k₀ →ₐ[k₀] Ω :=
    { ε₀ with commutes' := fun c ↦ RingHom.congr_fun hε₀ c }
  have hint₀ (z : AlgebraicClosure k₀) : _root_.IsIntegral k₀ (ε₀ z) :=
    (Algebra.IsIntegral.isIntegral (R := k₀) z).map ε₀A
  have hint (z : AlgebraicClosure k₀) : _root_.IsIntegral Γ(C, W) (ε₀ z) := (hint₀ z).tower_top
  -- inertia fixes the image of `ε₀`
  have hfix (z : AlgebraicClosure k₀) : ∀ σ ∈ Q.inertia Gal(Ω/K),
      σ • (⟨ε₀ z, hint z⟩ : integralClosure Γ(C, W) Ω) = ⟨ε₀ z, hint z⟩ := by
    intro σ hσ
    let σ' : Ω →ₐ[k₀] Ω :=
      { σ.toRingHom with
        commutes' c := by
          change σ (algebraMap Γ(C, W) Ω (φ₀ c)) = algebraMap Γ(C, W) Ω (φ₀ c)
          rw [IsScalarTower.algebraMap_apply Γ(C, W) K Ω, AlgEquiv.commutes] }
    set w : integralClosure Γ(C, W) Ω := σ • ⟨ε₀ z, hint z⟩ - ⟨ε₀ z, hint z⟩
    have hwQ : w ∈ Q := hσ _
    have hwint : _root_.IsIntegral k₀ (w : Ω) := ((hint₀ z).map σ').sub (hint₀ z)
    by_contra hne
    have hw0 : (w : Ω) ≠ 0 := fun h ↦ hne (sub_eq_zero.1 (Subtype.ext h))
    have hinv : _root_.IsIntegral Γ(C, W) ((w : Ω)⁻¹) :=
      (isAlgebraic_iff_isIntegral.1 hwint.isAlgebraic.inv).tower_top
    have h1 : (⟨(w : Ω)⁻¹, hinv⟩ : integralClosure Γ(C, W) Ω) * w = 1 :=
      Subtype.ext (inv_mul_cancel₀ hw0)
    exact (Ideal.IsMaximal.ne_top inferInstance)
      ((Ideal.eq_top_iff_one _).2 (h1 ▸ Q.mul_mem_left _ hwQ))
  let ε₁ : AlgebraicClosure k₀ →+* integralClosure Γ(C, W) Ω :=
    ε₀.codRestrict (integralClosure Γ(C, W) Ω) hint
  let ε : AlgebraicClosure k₀ →+* A :=
    ((algebraMap _ (Localization.AtPrime Q)).comp ε₁).codRestrict A fun z ↦
      (Ideal.inertiaInvariantsOfFixed K Q _ (hfix z)).2
  have hε (z : AlgebraicClosure k₀) : Ideal.inertiaInvariantsToField K Q (ε z) = ε₀ z :=
    Ideal.atPrimeToField_algebraMap Q (ε₁ z)
  -- the residue field of `A` is `k̄`
  let ρ : AlgebraicClosure k₀ →+* ResidueField A := (residue A).comp ε
  have hρ : Function.Bijective ρ := IsAlgClosed.ringHom_bijective_of_isIntegral ρ fun y ↦ by
    obtain ⟨p, hp, hpy⟩ := Ideal.isIntegralElem_residueField_inertiaInvariants K Q
      (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hpy]
    congr 1
    exact RingHom.ext_int _ _
  let θ := (RingEquiv.ofBijective ρ hρ).symm
  refine ⟨ε, θ.toRingHom.comp (residue A), ?_, fun a ↦ ?_, hε, ?_⟩
  · ext z
    exact (RingEquiv.ofBijective ρ hρ).symm_apply_apply z
  · change θ (residue A a) = 0 ↔ _
    rw [map_eq_zero_iff θ θ.injective, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  · refine RingHom.ext fun c ↦ ?_
    apply Ideal.injective_inertiaInvariantsToField K Q
    change Ideal.inertiaInvariantsToField K Q (algebraMap Γ(C, W) A (φ₀ c)) =
      Ideal.inertiaInvariantsToField K Q (ε (algebraMap k₀ (AlgebraicClosure k₀) c))
    rw [AlgHom.commutes, hε]
    exact (RingHom.congr_fun hε₀ c).symm

/-- The morphism `Spec B_Q^{I_Q} ⟶ Spec Γ(C, W) ⟶ C`. -/
noncomputable abbrev specInertiaInvariantsTo :
    Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶ C :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q))) ≫
    hW.fromSpec

omit [Finite k₀] [C.Over (Spec (.of k₀))] [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω]
  [IsSepClosed Ω] [Q.IsMaximal] in
include hxW in
lemma algebraMap_inertiaInvariants_mem_nonunits_iff [Q.IsMaximal] (a : Γ(C, W)) :
    ¬ IsUnit (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a) ↔
      a ∈ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal := by
  set m := (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal
  refine ⟨fun hu ↦ by_contra fun ham ↦
    hu (Ideal.isUnit_algebraMap_inertiaInvariants _ m Q ham), fun ham hu ↦ ?_⟩
  have hu' : IsUnit (algebraMap Γ(C, W) (Localization.AtPrime Q) a) :=
    hu.map (Ideal.inertiaInvariants C.functionField Q).val
  rw [IsScalarTower.algebraMap_apply Γ(C, W) (integralClosure Γ(C, W) Ω)
    (Localization.AtPrime Q), IsLocalization.AtPrime.isUnit_to_map_iff _ Q] at hu'
  rw [Ideal.over_def Q m] at ham
  exact hu' ham

omit hW in
omit [Finite k₀] [C.Over (Spec (.of k₀))] [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω]
  [IsSepClosed Ω] [Q.LiesOver (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal] in
/-- An element of `B_Q^{I_Q}` whose image in `Ω` lies in `Q` is a nonunit. -/
lemma not_isUnit_of_inertiaInvariantsToField_mem {a : Ideal.inertiaInvariants C.functionField Q}
    {b : integralClosure Γ(C, W) Ω} (hbQ : b ∈ Q)
    (hab : Ideal.inertiaInvariantsToField _ Q a = b) : ¬ IsUnit a := by
  intro hu
  have hu' : IsUnit (a : Localization.AtPrime Q) := hu.map (Ideal.inertiaInvariants _ Q).val
  have : (a : Localization.AtPrime Q) = algebraMap _ _ b :=
    Ideal.injective_atPrimeToField Q (by rw [Ideal.atPrimeToField_algebraMap]; exact hab)
  rw [this, IsLocalization.AtPrime.isUnit_to_map_iff _ Q] at hu'
  exact hu' hbQ

/-- The map `Γ(C, W) ⟶ κ(x)` for `x ∈ W`. -/
noncomputable abbrev sectionsResidue : Γ(C, W) ⟶ C.residueField x.1 :=
  C.presheaf.germ W x.1 hxW ≫ C.residue x.1

omit [Finite k₀] [C.Over (Spec (.of k₀))] [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω]
  [IsIntegral C]
  [IsSepClosed Ω] [Nonempty W] [Q.LiesOver (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal] in
lemma specMap_comp_fromSpecResidueField {L : CommRingCat.{u}} (ι : C.residueField x.1 ⟶ L) :
    Spec.map ι ≫ C.fromSpecResidueField x.1 =
      Spec.map (sectionsResidue x hxW ≫ ι) ≫ hW.fromSpec := by
  rw [Scheme.fromSpecResidueField, ← hW.fromSpecStalk_eq_fromSpecStalk hxW,
    IsAffineOpen.fromSpecStalk, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]

omit [Finite k₀] [C.Over (Spec (.of k₀))] [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω]
  [IsSepClosed Ω] [Q.LiesOver (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal] in
/-- **Compatibility of `Q` with a geometric point.** If `ε₀(ι(ā)) ≡ a mod Q` for all
`a ∈ Γ(C, W)`, then `Spec r ⟶ Spec B_Q^{I_Q} ⟶ C` is `Spec ι ⟶ Spec κ(x) ⟶ C`. -/
lemma specMap_comp_specInertiaInvariantsTo_of_compatible
    (ε₀ : AlgebraicClosure k₀ →+* Ω)
    (ε : AlgebraicClosure k₀ →+* Ideal.inertiaInvariants C.functionField Q)
    (r : Ideal.inertiaInvariants C.functionField Q →+* AlgebraicClosure k₀)
    (hrε : r.comp ε = RingHom.id _) (hr : ∀ a, r a = 0 ↔ ¬ IsUnit a)
    (hε : ∀ y, Ideal.inertiaInvariantsToField _ Q (ε y) = ε₀ y)
    (ι : C.residueField x.1 →+* AlgebraicClosure k₀)
    (hQ : ∀ a : Γ(C, W), ∃ b ∈ Q,
      (b : Ω) = ε₀ (ι (sectionsResidue x hxW a)) - algebraMap Γ(C, W) Ω a) :
    Spec.map (CommRingCat.ofHom r) ≫ specInertiaInvariantsTo hW Q =
      Spec.map (CommRingCat.ofHom ι) ≫ C.fromSpecResidueField x.1 := by
  rw [specMap_comp_fromSpecResidueField hW x hxW, specInertiaInvariantsTo, ← Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  change r (algebraMap Γ(C, W) _ a) = ι (sectionsResidue x hxW a)
  obtain ⟨b, hbQ, hb⟩ := hQ a
  set c := ι (sectionsResidue x hxW a)
  have hd : ¬ IsUnit (ε c - algebraMap Γ(C, W) _ a) :=
    not_isUnit_of_inertiaInvariantsToField_mem Q hbQ (by
      rw [map_sub, hε, AlgHom.commutes, hb])
  have h0 := (hr _).2 hd
  rw [r.map_sub, sub_eq_zero, show r (ε c) = c from RingHom.congr_fun hrε c] at h0
  exact h0.symm

/-- The neighbourhood `Spec B_Q^{I_Q} ⟶ C̄` given by `Spec B_Q^{I_Q} ⟶ C` and an embedding
`ε : k̄ ⟶ B_Q^{I_Q}` compatible with `k₀`. -/
noncomputable abbrev specInertiaInvariantsToGeometricFiber
    (ε : AlgebraicClosure k₀ →+* Ideal.inertiaInvariants C.functionField Q)
    (hε : specInertiaInvariantsTo hW Q ≫ (C ↘ Spec (.of k₀)) =
      Spec.map (CommRingCat.ofHom ε) ≫ (Scheme.specAlgebraicClosure k₀).hom) :
    Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
      (C ↘ Spec (.of k₀)).geometricFiber :=
  pullback.lift _ _ hε

omit [IsSepClosed Ω] in
include x hxW in
/-- The neighbourhood `Spec B_Q^{I_Q} ⟶ C̄` is weakly étale. -/
lemma weaklyEtale_specInertiaInvariantsToGeometricFiber
    (ε : AlgebraicClosure k₀ →+* Ideal.inertiaInvariants C.functionField Q)
    (hε : specInertiaInvariantsTo hW Q ≫ (C ↘ Spec (.of k₀)) =
      Spec.map (CommRingCat.ofHom ε) ≫ (Scheme.specAlgebraicClosure k₀).hom) :
    WeaklyEtale (specInertiaInvariantsToGeometricFiber hW Q ε hε) := by
  have := indEtale_inertiaInvariants_of_isAffineOpen hW Q x hxW
  have : Algebra.IndEtale k₀ (AlgebraicClosure k₀) :=
    Algebra.IndEtale.of_isSeparable k₀ (AlgebraicClosure k₀)
  have : WeaklyEtale (Scheme.specAlgebraicClosure k₀).hom := by
    change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀))))
    infer_instance
  have : WeaklyEtale (specInertiaInvariantsToGeometricFiber hW Q ε hε ≫
      (C ↘ Spec (.of k₀)).geometricFiberProj) := by
    rw [Scheme.Hom.geometricFiberProj, pullback.lift_fst]
    infer_instance
  have : WeaklyEtale (C ↘ Spec (.of k₀)).geometricFiberProj := by
    rw [Scheme.Hom.geometricFiberProj]
    infer_instance
  exact WeaklyEtale.of_comp _ (C ↘ Spec (.of k₀)).geometricFiberProj

omit [IsIntegral C] in
omit [Finite k₀] [IsDedekindDomain Γ(C, W)] [Nonempty W] [IsGalois C.functionField Ω]
  [IsSepClosed Ω] [Q.LiesOver (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal] in
/-- The structure map of the residue field at `x ∈ W` factors through `Γ(C, W)`. -/
lemma residueFieldAlgebraMap_eq_comp :
    (C ↘ Spec (.of k₀)).residueFieldAlgebraMap x.1 =
      (sectionsResidue x hxW).hom.comp (sectionsStructHom (k₀ := k₀) hW) := by
  apply_fun (fun f ↦ Spec.map (CommRingCat.ofHom f)) using fun f g h ↦ by
    simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  dsimp only
  rw [Scheme.Hom.specMap_residueFieldAlgebraMap]
  have h := specMap_comp_fromSpecResidueField hW x hxW (𝟙 _)
  rw [Spec.map_id, Category.id_comp, Category.comp_id] at h
  simp only [h, sectionsResidue, Category.assoc, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, Spec.map_preimage]

omit [IsDedekindDomain Γ(C, W)] [Finite k₀] in
/-- **The embedding of the residue field induced by a point over `x`.** For an embedding
`ε₀ : k̄ ↪ Ω` over `k₀` and a maximal ideal `Q` over `x`, there is a `k₀`-embedding
`ι₀ : κ(x) ↪ k̄` such that `ε₀(ι₀(ā)) ≡ a mod Q` for `a ∈ Γ(C, W)`. -/
theorem exists_residueField_emb_compatible (ε₀ : AlgebraicClosure k₀ →+* Ω)
    (hε₀ : ε₀.comp (algebraMap k₀ (AlgebraicClosure k₀)) =
      (algebraMap Γ(C, W) Ω).comp (sectionsStructHom hW)) :
    ∃ ι₀ : C.residueField x.1 →+* AlgebraicClosure k₀,
      ι₀.comp ((C ↘ Spec (.of k₀)).residueFieldAlgebraMap x.1) =
        algebraMap k₀ (AlgebraicClosure k₀) ∧
      ∀ a : Γ(C, W), ∃ b ∈ Q,
        (b : Ω) = ε₀ (ι₀ (sectionsResidue x hxW a)) - algebraMap Γ(C, W) Ω a := by
  obtain ⟨ε, r, hrε, hr, hε, hφ⟩ := exists_algebraicClosure_inertiaInvariants hW Q x hxW _ hε₀
  have := isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen hW Q
  have hgm (a : Γ(C, W)) :
      r (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a) = 0 ↔
        a ∈ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal := by
    rw [hr, algebraMap_inertiaInvariants_mem_nonunits_iff hW Q x hxW]
  -- `r ∘ algebraMap` factors through the stalk at `x` and its residue field
  let z' : W := ⟨x.1, hxW⟩
  let _ : Algebra Γ(C, W) (C.presheaf.stalk z') := TopCat.Presheaf.algebra_section_stalk _ z'
  have := hW.isLocalization_stalk z'
  have hunit (s : (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.primeCompl) :
      IsUnit ((r.comp (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q))) s) :=
    isUnit_iff_ne_zero.2 fun h ↦ s.2 ((hgm s).1 h)
  let g' : C.presheaf.stalk z' →+* AlgebraicClosure k₀ := IsLocalization.lift hunit
  have hg' (a : Γ(C, W)) : g' (algebraMap _ _ a) =
      r (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a) :=
    IsLocalization.lift_eq hunit a
  have : IsLocalHom g' := ⟨fun y hy ↦ by
    by_contra hns
    obtain ⟨⟨a, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.primeCompl y
    have ha := (IsLocalization.AtPrime.mk'_mem_maximal_iff
      (C.presheaf.stalk z') (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal a s).1
      ((mem_maximalIdeal _).2 hns)
    have h0 : g' (IsLocalization.mk' _ a s) = 0 :=
      (IsLocalization.lift_mk'_spec _ _ _ _).2 (by
        rw [mul_zero]
        exact (hgm a).2 ha)
    rw [h0] at hy
    exact not_isUnit_zero hy⟩
  let ι₀ : C.residueField x.1 →+* AlgebraicClosure k₀ := IsLocalRing.ResidueField.lift g'
  have hι₀ (a : Γ(C, W)) : ι₀ (sectionsResidue x hxW a) =
      r (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a) := by
    change IsLocalRing.ResidueField.lift g' (IsLocalRing.residue _ (algebraMap _ _ a)) = _
    rw [IsLocalRing.ResidueField.lift_residue_apply, hg']
  refine ⟨ι₀, ?_, fun a ↦ ?_⟩
  · refine RingHom.ext fun c ↦ ?_
    have h1 := RingHom.congr_fun (residueFieldAlgebraMap_eq_comp hW x hxW) c
    rw [RingHom.comp_apply, h1, RingHom.comp_apply, hι₀]
    have h2 := RingHom.congr_fun hφ c
    rw [RingHom.comp_apply, RingHom.comp_apply] at h2
    rw [h2]
    exact RingHom.congr_fun hrε _
  · obtain ⟨c, hc⟩ : ∃ c, r (algebraMap Γ(C, W)
        (Ideal.inertiaInvariants C.functionField Q) a) = c := ⟨_, rfl⟩
    rw [hι₀, hc]
    have hd : ¬ IsUnit
        (ε c - algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a) := by
      rw [← hr, r.map_sub, show r (ε c) = c from RingHom.congr_fun hrε c, hc, sub_self]
    let : Algebra k₀ Γ(C, W) := (sectionsStructHom (k₀ := k₀) hW).toAlgebra
    let : Algebra k₀ Ω := ((algebraMap Γ(C, W) Ω).comp (sectionsStructHom (k₀ := k₀) hW)).toAlgebra
    have : IsScalarTower k₀ Γ(C, W) Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let eK : AlgebraicClosure k₀ →ₐ[k₀] Ω :=
      { toRingHom := ε₀, commutes' := RingHom.congr_fun hε₀ }
    have hint : _root_.IsIntegral Γ(C, W) (ε₀ c - algebraMap Γ(C, W) Ω a) :=
      (((Algebra.IsIntegral.isIntegral (R := k₀) c).map eK).tower_top).sub isIntegral_algebraMap
    refine ⟨⟨_, hint⟩, ?_, rfl⟩
    by_contra hb
    apply hd
    refine Ideal.isUnit_of_isUnit_coe _ Q ?_
    have heq : ((ε c - algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a :
        Ideal.inertiaInvariants _ Q) : Localization.AtPrime Q) =
        algebraMap _ _ (⟨_, hint⟩ : integralClosure Γ(C, W) Ω) := by
      apply Ideal.injective_atPrimeToField Q
      rw [Ideal.atPrimeToField_algebraMap]
      change Ideal.inertiaInvariantsToField _ Q
        (ε c - algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) a) = _
      rw [map_sub, hε, AlgHom.commutes]
    rw [heq]
    exact IsLocalization.map_units _ (⟨_, hb⟩ : Q.primeCompl)

section Punctured

variable {U : Scheme.{u}} [U.Over (Spec (.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [j.IsOver (Spec (.of k₀))]

omit [Finite k₀] [IsSepClosed Ω] in
include x hxW in
/-- **The punctured neighbourhood.** If `U ∩ W = D(ϖ)` for some `0 ≠ ϖ` in the prime of `x`, the
pullback of a neighbourhood `h : Spec B_Q^{I_Q} ⟶ C̄` lying over `Spec B_Q^{I_Q} ⟶ C` along
`Ū ⟶ C̄` is the spectrum of the fixed field `K' = Ω^{I_Q}`, mapping to `Spec B_Q^{I_Q}` by the
inclusion. -/
theorem exists_iso_pullback_geometricFiberMap
    (ϖ : Γ(C, W)) (hϖ : j.opensRange ⊓ W = C.basicOpen ϖ)
    (hϖx : ϖ ∈ (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal) (hϖ0 : ϖ ≠ 0)
    (h : Spec (.of (Ideal.inertiaInvariants C.functionField Q)) ⟶
      (C ↘ Spec (.of k₀)).geometricFiber)
    (hh : h ≫ (C ↘ Spec (.of k₀)).geometricFiberProj = specInertiaInvariantsTo hW Q) :
    ∃ e : Spec (.of (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField)))) ≅
        pullback h (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (.of k₀)))),
      e.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap
        (Ideal.inertiaInvariants C.functionField Q)
        (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField))))) := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have := hW.isMaximal_primeIdealOf x hxW
  have := hW.finite_quotient_primeIdealOf x hxW
  have : Finite (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField _).2
  have := Ideal.isLocalization_away_inertiaInvariants C.functionField
    (hW.primeIdealOf ⟨x.1, hxW⟩).asIdeal Q hϖx hϖ0
  set iU := Spec.map (CommRingCat.ofHom (algebraMap (Ideal.inertiaInvariants C.functionField Q)
    (IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField)))))
  have : IsOpenImmersion iU := IsOpenImmersion.of_isLocalization
    (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) ϖ)
  have H' : (specInertiaInvariantsTo hW Q) ⁻¹ᵁ j.opensRange = iU.opensRange := by
    ext q
    have hW' : (specInertiaInvariantsTo hW Q) q ∈ W := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨_, rfl⟩
    have h1 : (specInertiaInvariantsTo hW Q) q ∈ j.opensRange ↔
        (specInertiaInvariantsTo hW Q) q ∈ C.basicOpen ϖ := by
      rw [← hϖ]
      exact ⟨fun h ↦ ⟨h, hW'⟩, fun h ↦ h.1⟩
    have h2 : (specInertiaInvariantsTo hW Q) q ∈ C.basicOpen ϖ ↔
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q)))
          q ∈ PrimeSpectrum.basicOpen ϖ := by
      rw [← hW.fromSpec_preimage_basicOpen]
      rfl
    change (specInertiaInvariantsTo hW Q) q ∈ j.opensRange ↔ q ∈ Set.range iU
    rw [h1, h2]
    exact (specMap_mem_range_of_isLocalizationAway
      (B := IntermediateField.fixedField (Q.inertia Gal(Ω/C.functionField)))
      (algebraMap Γ(C, W) (Ideal.inertiaInvariants C.functionField Q) ϖ) q).symm
  have hrange : Set.range (iU ≫ (specInertiaInvariantsTo hW Q)) ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    have h : iU y ∈ iU.opensRange := Scheme.Hom.mem_opensRange.2 ⟨y, rfl⟩
    rw [← H', Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange] at h
    obtain ⟨u, hu⟩ := h
    exact ⟨u, hu.trans (Scheme.Hom.comp_apply _ _ _).symm⟩
  let kU := IsOpenImmersion.lift j (iU ≫ (specInertiaInvariantsTo hW Q)) hrange
  have sq1 : IsPullback kU iU j (specInertiaInvariantsTo hW Q) :=
    IsOpenImmersion.isPullback kU iU j (specInertiaInvariantsTo hW Q)
      (IsOpenImmersion.lift_fac _ _ _).symm H'
  have sq2 := (IsPullback.of_hasPullback h
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (.of k₀))))).flip.paste_horiz
      (Scheme.Hom.isPullback_geometricFiberMap j (comp_over j (Spec (.of k₀)))).flip
  rw [hh] at sq2
  exact ⟨sq1.isoIsPullback _ _ sq2, IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

end Punctured

end Boundary

end AlgebraicGeometry
