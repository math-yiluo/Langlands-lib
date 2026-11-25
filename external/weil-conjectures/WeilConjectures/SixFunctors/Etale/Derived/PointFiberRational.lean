/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.Shrink
public import WeilConjectures.CategoryTheory.DerivedCategory.ExtendScalarsLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.PrincipalIdealDevissage
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral
public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage

/-!
# Rational constructible complexes over a geometric point

Let `Λ` be a complete discrete valuation ring with finite residue field and maximal ideal
`I = (ϖ)` (in the blueprint `Λ = 𝒪_E`), `M` a submonoid of `Λ` and `K` a field which is the
localization of `Λ` at `M` (in the blueprint `M = Λ ∖ {0}` and `K = E`). Following blueprint
`proposition-inverting-ell--2`, the rational stage over a scheme `X` is the rationalization

`Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[M⁻¹]`

(`CategoryTheory.Rationalization M` of the integral stage). For `s = Spec k` with `k` separably
closed, the evaluation at the geometric point of `s` followed by `- ⊗_Λ K` is a triangulated
functor `Dᵇc(s, 𝒪_E) ⥤ D(K)` sending multiplication by `r` to multiplication by its image in `K`,
hence it factors through the rationalization. The resulting functor

`Fib_s : Dᵇc(s, E) ⥤ Dᵇ_fd(E)`

(`AlgebraicGeometry.Etale.pointFiberRational`) is an equivalence onto the bounded complexes of
`K`-vector spaces with finite-dimensional cohomology
(`AlgebraicGeometry.Etale.pointFiberRationalEquivalence`).

## Proof

* Full faithfulness: the integral stage over `s` is equivalent, through `D(Γ)`, to `Dᵇ_fg(Λ)`
  (`AlgebraicGeometry.Etale.pointFiberIntegralEquivalence`), whose objects lie in every
  triangulated subcategory containing `Λ[0]` (`DerivedCategory.prop_of_boundedFiniteCohomology`);
  so every object of the rationalization lies in every triangulated subcategory containing the
  image `G` of the constant sheaf `Λ[0]`. By the five lemma it suffices that `Fib_s` is bijective
  on the morphisms `G ⟶ G⟦n⟧` (`CategoryTheory.Functor.fullyFaithfulOfGenerator`), which reduces
  to the fact that `Hom(Λ, Λ[n]) ⟶ Hom(K, K[n])` is the localization map at `M`
  (`ModuleCat.locHomBijective_derivedExtendScalars_single`).
* Essential surjectivity: the essential image of the fully faithful triangulated functor
  `Fib_s` is a triangulated subcategory containing `K[0]`, hence all of `Dᵇ_fd(K)`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. This single instance is used throughout the file. -/
local instance essentiallySmall_etale_pointFiberRational (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section RationalPoint

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) [IsNoetherianRing Λ] [Finite (Λ ⧸ I)]
  [IsAdicComplete I Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ]
  [Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]
  (M : Submonoid Λ) (K : Type (u + 1)) [Field K] [Algebra Λ K] [IsLocalization M K]
  (k : Type u) [Field k] [IsSepClosed k]

set_option hygiene false in
/-- The integral stage `Dᵇc(Spec k, Λ)`. -/
local notation "𝐂" =>
  (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).FullSubcategory

omit [IsNoetherianRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] in
include M in
lemma flat_algebraMap_of_isLocalization : (algebraMap Λ K).Flat :=
  RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K M)

/-- The restriction of `D(Γ)` to the integral stage over `Spec k`. -/
noncomputable abbrev integralPointSections : 𝐂 ⥤ DerivedCategory (ModuleCat.{u + 1} Λ) :=
  (DerivedCategory.boundedConstructibleIntegral I (Spec (.of k))).ι ⋙
    (pointSections Λ k).mapDerivedCategory

/-- The evaluation at the geometric point of `Spec k` followed by the extension of scalars to
`K`, on the integral stage. -/
noncomputable abbrev pointFiberRationalAux : 𝐂 ⥤ DerivedCategory (ModuleCat.{u + 1} K) :=
  integralPointSections I k ⋙
    ModuleCat.derivedExtendScalars (algebraMap Λ K) (flat_algebraMap_of_isLocalization M K)

omit [IsNoetherianRing Λ] [Finite (Λ ⧸ I)] [IsAdicComplete I Λ] [IsDomain Λ]
  [IsPrincipalIdealRing Λ] [Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})] in
lemma pointFiberRationalAux_map_smul_id (r : Λ) (X : 𝐂) :
    (pointFiberRationalAux I M K k).map (r • 𝟙 X) =
      algebraMap Λ K r • 𝟙 ((pointFiberRationalAux I M K k).obj X) := by
  change (ModuleCat.derivedExtendScalars _ _).map ((integralPointSections I k).map (r • 𝟙 X)) = _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id,
    ModuleCat.derivedExtendScalars_map_smul_id]
  rfl

/-- The evaluation at the geometric point of `s = Spec k` on the rational stage
`Dᵇc(s, E) = Dᵇc(s, 𝒪_E)[M⁻¹]`, with values in `D(K)`: the functor induced on the
rationalization by `D(Γ)` followed by `- ⊗_Λ K`. -/
noncomputable abbrev pointFiberRationalToDerived :
    Rationalization M 𝐂 ⥤ DerivedCategory (ModuleCat.{u + 1} K) :=
  Rationalization.lift M K (pointFiberRationalAux I M K k)
    (pointFiberRationalAux_map_smul_id I M K k)

/-- The constant sheaf `Λ` on `Spec k` placed in degree `0`, as an object of the integral
stage. -/
noncomputable def unitIntegral : 𝐂 :=
  ⟨unitSingle Λ k 0, boundedConstructibleIntegral_unitSingle (k := k)
    (Fact.out : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ}).choose_spec.1
    (Fact.out : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ}).choose_spec.2⟩

/-- `D(Γ)(Λ[0]) ≅ Λ[0]`. -/
noncomputable def integralPointSectionsUnitIso :
    (integralPointSections I k).obj (unitIntegral I k) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj (ModuleCat.of Λ Λ) :=
  ((pointSections Λ k).mapDerivedCategorySingleFunctor 0).app (unitSheaf Λ k) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheafEquivalenceOfIsSepClosed Λ (k := k)).unitIso.app (ModuleCat.of Λ Λ)).symm

/-- Every object of the rational stage lies in every triangulated subcategory, closed under
isomorphisms, containing `Λ[0]`. -/
lemma prop_of_unitIntegral (P : ObjectProperty (Rationalization M 𝐂)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (hP : P ((Rationalization.Q M 𝐂).obj (unitIntegral I k)))
    (X : Rationalization M 𝐂) : P X := by
  let P₁ := P.inverseImage (Rationalization.Q M 𝐂)
  let P₂ := P₁.map (integralPointSections I k)
  have : (integralPointSections I k).Full := inferInstance
  have : (integralPointSections I k).IsTriangulated := inferInstance
  have : P₁.IsTriangulated := inferInstance
  have h₀ : P₂ ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ Λ)) :=
    ⟨unitIntegral I k, hP, ⟨integralPointSectionsUnitIso I k⟩⟩
  obtain ⟨L, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
  obtain ⟨L', hL', ⟨e'⟩⟩ := DerivedCategory.prop_of_boundedFiniteCohomology P₂ h₀
    ((pointFiberIntegral I k).obj L).property
  exact P.prop_of_iso
    ((Rationalization.Q M 𝐂).mapIso ((integralPointSections I k).preimageIso e') ≪≫ e) hL'

omit [IsDomain Λ] [IsPrincipalIdealRing Λ] in
lemma locHomBijective_unitIntegral (n : ℤ) :
    Rationalization.LocHomBijective M K (pointFiberRationalAux I M K k) (unitIntegral I k)
      ((unitIntegral I k)⟦n⟧) :=
  Rationalization.LocHomBijective.of_comp (integralPointSections I k)
    ((ModuleCat.locHomBijective_derivedExtendScalars_single M
      (flat_algebraMap_of_isLocalization M K) n).of_iso (integralPointSectionsUnitIso I k).symm
      ((shiftFunctor _ n).mapIso (integralPointSectionsUnitIso I k).symm ≪≫
        (((integralPointSections I k).commShiftIso n).app _).symm))

/-- `Fib_s : Dᵇc(s, E) ⥤ D(K)` is fully faithful. -/
noncomputable def fullyFaithfulPointFiberRationalToDerived :
    (pointFiberRationalToDerived I M K k).FullyFaithful :=
  Functor.fullyFaithfulOfGenerator _ (G := (Rationalization.Q M 𝐂).obj (unitIntegral I k))
    (fun P _ _ hP X ↦ prop_of_unitIntegral I M k P hP X)
    (Functor.homBijectiveShifts_of_forall fun n ↦
      (Rationalization.homBijective_lift_obj M K _ _
        (locHomBijective_unitIntegral I M K k n)).of_iso (Iso.refl _)
        (((Rationalization.Q M 𝐂).commShiftIso n).app _))

omit [IsDomain Λ] [IsPrincipalIdealRing Λ] in
/-- `Fib_s` takes values in `Dᵇ_fd(K)`. -/
lemma boundedFiniteCohomology_pointFiberRationalToDerived_obj (X : Rationalization M 𝐂) :
    DerivedCategory.boundedFiniteCohomology K ((pointFiberRationalToDerived I M K k).obj X) := by
  obtain ⟨L, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
  exact (DerivedCategory.boundedFiniteCohomology K).prop_of_iso
    (((Rationalization.liftFac M K _ _).app L).symm ≪≫
      (pointFiberRationalToDerived I M K k).mapIso e)
    (ModuleCat.boundedFiniteCohomology_derivedExtendScalars_obj _ _
      ((pointFiberIntegral I k).obj L).property)

/-- Every object of `Dᵇ_fd(K)` is in the essential image of `Fib_s`. -/
lemma exists_iso_pointFiberRationalToDerived_obj {V : DerivedCategory (ModuleCat.{u + 1} K)}
    (hV : DerivedCategory.boundedFiniteCohomology K V) :
    ∃ X, Nonempty ((pointFiberRationalToDerived I M K k).obj X ≅ V) := by
  have := (fullyFaithfulPointFiberRationalToDerived I M K k).full
  have h₀ : (pointFiberRationalToDerived I M K k).essImage
      ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of K K)) :=
    ⟨(Rationalization.Q M 𝐂).obj (unitIntegral I k),
      ⟨(Rationalization.liftFac M K _ _).app (unitIntegral I k) ≪≫
        (ModuleCat.derivedExtendScalars _ _).mapIso (integralPointSectionsUnitIso I k) ≪≫
        ModuleCat.derivedExtendScalarsSingleIso _ _⟩⟩
  exact DerivedCategory.prop_of_boundedFiniteCohomology _ h₀ hV

/-- The evaluation at the geometric point of `s = Spec k`, `Fib_s : Dᵇc(s, E) ⥤ Dᵇ_fd(E)`, on
the rational stage `Dᵇc(s, E) = Dᵇc(s, 𝒪_E)[M⁻¹]`: the functor induced on the rationalization by
`D(Γ)` followed by `- ⊗_Λ K`, with values in the bounded complexes of `K`-vector spaces with
finite-dimensional cohomology. -/
noncomputable def pointFiberRational :
    Rationalization M 𝐂 ⥤ DerivedCategory.BoundedFiniteCohomology K :=
  (DerivedCategory.boundedFiniteCohomology K).lift (pointFiberRationalToDerived I M K k)
    (boundedFiniteCohomology_pointFiberRationalToDerived_obj I M K k)

instance : (pointFiberRational I M K k).Full :=
  (Functor.FullyFaithful.ofCompFaithful (F := pointFiberRational I M K k)
    (G := (DerivedCategory.boundedFiniteCohomology K).ι)
    (fullyFaithfulPointFiberRationalToDerived I M K k)).full

instance : (pointFiberRational I M K k).Faithful :=
  (Functor.FullyFaithful.ofCompFaithful (F := pointFiberRational I M K k)
    (G := (DerivedCategory.boundedFiniteCohomology K).ι)
    (fullyFaithfulPointFiberRationalToDerived I M K k)).faithful

instance : (pointFiberRational I M K k).EssSurj where
  mem_essImage V := by
    obtain ⟨X, ⟨e⟩⟩ := exists_iso_pointFiberRationalToDerived_obj I M K k V.property
    exact ⟨X, ⟨(DerivedCategory.boundedFiniteCohomology K).isoMk e⟩⟩

instance : (pointFiberRational I M K k).IsEquivalence where

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finite coefficient categories over a point
(rational stage `E`).

Let `Λ` be a complete discrete valuation ring with finite residue field and maximal ideal
`I = (ϖ)`, and `K` the localization of `Λ` at a submonoid `M` (in the blueprint `Λ = 𝒪_E`,
`K = E`, see `AlgebraicGeometry.Etale.pointFiberFieldEquivalence`), and `k` a separably closed
field. The evaluation at the geometric point of `s = Spec k`,
`Fib_s : Dᵇc(s, E) ⥤ Dᵇ_fd(E)` (`AlgebraicGeometry.Etale.pointFiberRational`), is an equivalence
from the rational stage `Dᵇc(s, E) = Dᵇc(s, 𝒪_E)[M⁻¹]` (the rationalization of the integral
stage, blueprint `proposition-inverting-ell--2`) onto the bounded complexes of `K`-vector
spaces with finite-dimensional cohomology, that is the bounded derived category of
finite-dimensional `K`-vector spaces. -/
noncomputable def pointFiberRationalEquivalence :
    Rationalization M 𝐂 ≌ DerivedCategory.BoundedFiniteCohomology K :=
  (pointFiberRational I M K k).asEquivalence

lemma pointFiberRationalEquivalence_functor :
    (pointFiberRationalEquivalence I M K k).functor = pointFiberRational I M K k :=
  rfl

end RationalPoint

section Field

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] [IsSepClosed k]

/-- The universe `u + 1` copy `Shrink E` of `E` as an algebra over the universe `u + 1` copy
`Shrink 𝒪_E` of its ring of integers. -/
noncomputable instance _root_.PadicAlgCl.algebraShrinkShrink :
    Algebra (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} E) :=
  ((Shrink.ringEquiv E).symm.toRingHom.comp
    (algebraMap (Shrink.{u + 1} (PadicAlgCl.integers l E)) E)).toAlgebra

/-- `Shrink E` is the fraction field of `Shrink 𝒪_E`. -/
instance _root_.PadicAlgCl.isFractionRing_shrinkShrink :
    IsFractionRing (Shrink.{u + 1} (PadicAlgCl.integers l E)) (Shrink.{u + 1} E) :=
  IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := (Shrink.ringEquiv E).symm) fun _ ↦ rfl)

/-- The maximal ideal of `Shrink 𝒪_E` is generated by a nonzerodivisor. -/
local instance fact_maximalIdealShrink :
    Fact (∃ ϖ ∈ nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)),
      PadicAlgCl.maximalIdealShrink l E = Ideal.span {ϖ}) :=
  ⟨PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finite coefficient categories over a point
(rational stage `E`).

For a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and a separably closed field `k`, evaluation at
the geometric point of `s = Spec k` is an equivalence `Fib_s : Dᵇc(s, E) ≌ Dᵇ_fd(E)` between the
rational stage `Dᵇc(s, E) = Dᵇc(s, 𝒪_E)[1/ϖ_E]` (the rationalization of the integral stage at
the nonzero elements of `𝒪_E`, blueprint `proposition-inverting-ell--2`) and the bounded
complexes of `E`-vector spaces with finite-dimensional cohomology, i.e. the bounded derived
category of finite-dimensional `E`-vector spaces (`E` being represented by its universe `u + 1`
copy `Shrink E`). This is `AlgebraicGeometry.Etale.pointFiberRationalEquivalence` for
`Λ = 𝒪_E`; the integral stage is `AlgebraicGeometry.Etale.pointFiberIntegerRingEquivalence`. -/
noncomputable def pointFiberFieldEquivalence :
    Rationalization (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E)
        (Spec (.of k))).FullSubcategory ≌
      _root_.DerivedCategory.BoundedFiniteCohomology (Shrink.{u + 1} E) :=
  pointFiberRationalEquivalence _ _ _ k

end Field

end Etale

end AlgebraicGeometry
