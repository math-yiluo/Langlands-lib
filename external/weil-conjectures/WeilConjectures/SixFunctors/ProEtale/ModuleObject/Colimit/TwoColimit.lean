/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurj

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.SplitCoefficientDerivedFaithful
import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparison
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteModelProofAPI
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.CategoryTheory.HomColimitExtension
import WeilConjectures.CategoryTheory.DirectedTriangulatedImage
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationDescent
import WeilConjectures.AlgebraicGeometry.CondensedSheafExtContinuity
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexPresentation
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement
/-!

# The bounded constructible `ℚ̄_ℓ`-complexes as the 2-colimit over the finite subextensions

Let `ℓ` be a prime and `X` a scheme. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`), let `C_E(X) = D^b_cons(X, E)` be the bounded
constructible derived category of modules over `E_X = p_X^* E̲`
(`ProEtale.BoundedConstructible (padicSubfieldRingObj X ℓ E)`, the full subcategory of the
unbounded `D(Mod_{E_X})` of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`),
and let `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` be the one of modules over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`. The
derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -
```
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars` are
shown to preserve bounded constructibility
(`ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`,
`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`), and hence restrict to
functors
```
ProEtale.constructibleExtendScalars h : C_E(X) ⥤ C_F(X)   (E ≤ F),
ProEtale.constructibleToPadicAlgCl E : C_E(X) ⥤ C_Ω(X),
```
compatible with each other through the transitivity of extension of scalars
(`ProEtale.constructibleToPadicAlgClCompIso`). Together these form a cocone of categories
`ProEtale.constructibleCocone X ℓ` on the directed system `E ↦ C_E(X)`, with vertex `C_Ω(X)`,
in the sense of `WeilConjectures.CategoryTheory.FilteredTwoColimit`.

The main statement, **`ℚ̄_ℓ` is a 2-colimit** (`ProEtale.constructibleCocone_isFilteredTwoColimit`),
is that this cocone is a filtered 2-colimit: the comparison functor
`2-colim_E C_E(X) ⟶ C_Ω(X)`, `(E, K_E) ↦ T^X_{E,Ω} K_E`, is an equivalence of ordinary
categories. By `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` this is the conjunction of

* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: every bounded constructible
  `ℚ̄_ℓ,X`-complex `K` is isomorphic to `T^X_{E,Ω} K_E` for some finite subextension `E` and some
  bounded constructible `E_X`-complex `K_E` (descent of constructible objects);
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` in `D(Mod_{ℚ̄_ℓ,X})` is defined over some finite
  subextension `H ⊇ E, F`, and two morphisms over `H` with the same image are equal over some
  finite subextension `H' ⊇ H`. Since the bounded constructible complexes are stable under
  shifts, this includes the statement for the shifted targets `L_F[n]`, which is what the
  compatibility with the triangulated structures requires.

These are stated for a topologically noetherian `X`, the setting in which the bounded
constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj`, for the rings `E_X`). They
are *not* formal consequences of the identification `ℚ̄_ℓ,X ≃ colim_E E_X` of
`ProEtale.isColimitPadicAlgClRingObjCocone`, and they are false for the unbounded derived
categories; see the module docstring of `WeilConjectures.CategoryTheory.FilteredTwoColimit` for
the ordinary-category model of the 2-colimit that they describe.

## Proofs

* `ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj` and
  `ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`: the extension of scalars
  is exact, so it commutes with the cohomology sheaves, and it preserves constructibility
  (`ProEtale.boundedConstructible_leftDerivedExtendScalars_obj`).
* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: the complexes that descend to some `E` form a
  triangulated subcategory (the cone step uses (Hom)); it contains every constructible module in
  degree `0`, by finite presentation of constructible `ℚ̄_ℓ,X`-modules and descent of their
  presentations; the dévissage of a bounded constructible complex into its cohomology sheaves
  (`ProEtale.prop_of_boundedConstructibleModule`) concludes.
* **(Hom)** `ProEtale.constructibleCocone_homSurj`: `ℚ̄_ℓ,X ⊗ Y = colim_H H_X ⊗ Y`, and `Hom`
  out of a bounded constructible complex commutes with this filtered colimit (dévissage to
  constructible modules, which are finitely presented, `ProEtale.condensed_sheaf_ext_continuity`);
  `ProEtale.constructibleCocone_homInj`: the extension of scalars to `ℚ̄_ℓ` is faithful, `E_X` being
  an `E_X`-linear direct summand of `ℚ̄_ℓ,X` (`ProEtale.faithful_derivedExtendScalarsToPadicAlgCl`).

These proofs do not use the lemmas `ProEtale.exists_iso_derivedExtendScalarsToPadicAlgCl_obj` and
`ProEtale.exists_derivedExtendScalarsToPadicAlgCl_map_eq`.

This is the input needed to transport base change theorems from finite to `ℚ̄_ℓ`-coefficients:
by (Obj) every constructible `K` is `T^X_{E,Ω} K_E`, and the compatibility of the base change
maps with the extension of scalars (built from the (Pull) and (Push) comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`) then shows that the
base change map at `K` is the extension of scalars of the one at `K_E`. This compatibility of
the base change maps of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems`
with the extension of scalars is not yet formalized.

-/

attribute [local instance 20000]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape

set_option maxSynthPendingDepth 0

@[expose] public section

attribute [local instance 2000] CategoryTheory.Sheaf.instHasColimitsOfSize
  CategoryTheory.Sheaf.instHasColimitsOfShape CategoryTheory.Sheaf.instHasFiniteColimits
  CategoryTheory.Sheaf.hasLimitsOfSize CategoryTheory.Sheaf.instHasFiniteLimits

attribute [local instance 2000] CategoryTheory.Mod.monoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local instance 2000] CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.upperStarFromPointComp
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_pointUpperStar
  AlgebraicGeometry.ProEtale.oplaxMonoidal_pointUpperStar

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The bounded constructible categories and the functors between them -/

section Constructible

open scoped CondensedRing

/-- The bounded constructible derived category `C_E(X) = D^b_cons(X, E)` of `E_X`-modules, for
a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev PadicSubfieldConstructible (E : FiniteIntermediateField ℓ) : Type _ :=
  BoundedConstructible (padicSubfieldRingObj X ℓ E)

/-- The bounded constructible derived category `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` of
`ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev PadicAlgClConstructible : Type _ :=
  BoundedConstructible (padicAlgClRingObj X ℓ)

/-- Extension of scalars along `E_X ⟶ F_X` preserves bounded constructible complexes.
See the module docstring. -/
lemma boundedConstructible_derivedExtendScalarsSubfield_obj {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (padicSubfieldRingObj X ℓ F)
      ((derivedExtendScalarsSubfield X ℓ h).obj K.obj) :=
  ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K.obj K.property

/-- Extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes.
See the module docstring. -/
lemma boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj (E : FiniteIntermediateField ℓ)
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (padicAlgClRingObj X ℓ)
      ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj) :=
  ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K.obj K.property

/-- The extension of scalars `T^X_{E,F} : C_E(X) ⥤ C_F(X)` on bounded constructible complexes,
for finite subextensions `E ≤ F`. -/
noncomputable def constructibleExtendScalars {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicSubfieldConstructible X ℓ F :=
  (boundedConstructible (padicSubfieldRingObj X ℓ F)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K)

/-- The extension of scalars `T^X_{E,Ω} : C_E(X) ⥤ C_Ω(X)` on bounded constructible complexes,
for a finite subextension `E`: the functors of the cocone whose vertex
is the bounded constructible `ℚ̄_ℓ`-complexes. -/
noncomputable def constructibleToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicAlgClConstructible X ℓ :=
  (boundedConstructible (padicAlgClRingObj X ℓ)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)

/-- The functors to the bounded constructible `ℚ̄_ℓ`-complexes are compatible with the extensions
of scalars between finite subextensions: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` on bounded
constructible complexes, by `derivedExtendScalarsCompIso` and the full faithfulness of the
inclusion of the bounded constructible complexes. -/
noncomputable def constructibleToPadicAlgClCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F ≅
      constructibleToPadicAlgCl X ℓ E :=
  Functor.fullyFaithfulCancelRight (boundedConstructible (padicAlgClRingObj X ℓ)).ι
    ((Iso.refl ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) :
      (constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F) ⋙
          (boundedConstructible (padicAlgClRingObj X ℓ)).ι ≅
        (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
          (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) ≪≫
      Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (derivedExtendScalarsCompIso X ℓ h))

/-- The cocone of categories `E ↦ C_E(X)` with vertex `C_Ω(X)`: the directed system of the
bounded constructible `E`-complexes over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the
extensions of scalars as transition functors, and the extensions of scalars to `ℚ̄_ℓ` as
functors to the vertex. -/
noncomputable def constructibleCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (PadicAlgClConstructible X ℓ) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := constructibleToPadicAlgCl X ℓ E
  iso h := constructibleToPadicAlgClCompIso X ℓ h

end Constructible

end AlgebraicGeometry.ProEtale

/-! ### (Obj) and (Hom)-surjectivity by dévissage -/

section

set_option maxSynthPendingDepth 0

attribute [local instance 2000] CategoryTheory.Sheaf.instHasColimitsOfSize
  CategoryTheory.Sheaf.instHasColimitsOfShape CategoryTheory.Sheaf.instHasFiniteColimits
  CategoryTheory.Sheaf.hasLimitsOfSize CategoryTheory.Sheaf.instHasFiniteLimits

attribute [local instance 2000] CategoryTheory.Mod.monoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local instance 2000] CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf


set_option backward.isDefEq.respectTransparency false

open ZeroObject

attribute [local instance 100]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape

section ExactDerived
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [hClosed : MonoidalClosed C] [BraidedCategory C] [HasColimitsOfSize.{v₁, v₁} C]
  [HasExactColimitsOfShape ℤ C] [HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
private noncomputable def exactDerivedIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.leftDerivedFunctor ≅ F.mapDerivedCategory :=
  F.leftDerivedFunctorIsoMapDerivedCategory
private noncomputable def singleExactDerivedIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    DerivedCategory.singleFunctor C 0 ⋙ F.leftDerivedFunctor ≅
      F ⋙ DerivedCategory.singleFunctor D 0 :=
  F.singleFunctorCompLeftDerivedFunctorIso
@[instance_reducible]
private noncomputable def exactDerivedShift (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso (exactDerivedIso F).symm ℤ
private theorem exactDerivedTriangulated (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    letI := exactDerivedShift F
    F.leftDerivedFunctor.IsTriangulated := by
  let _ := exactDerivedShift F
  have := Functor.CommShift.ofIso_compatibility (exactDerivedIso F).symm ℤ
  exact Functor.isTriangulated_of_iso (exactDerivedIso F).symm
end ExactDerived

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
section TwoColimit

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
variable [TopologicalSpace.NoetherianSpace X]

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false

@[instance_reducible, local instance]
private noncomputable def algClCommShift (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ :=
  exactDerivedShift
    (C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (D := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

omit [TopologicalSpace.NoetherianSpace X] in
@[local instance]
private lemma algClTriangulated (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated :=
  exactDerivedTriangulated
    (C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (D := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] finiteCoefficientDerivedHomEquiv
  finiteCoefficientDerivedAlgClHomEquiv finiteCoefficientDerivedRestriction
  finiteCoefficientDerivedFromAlgCl finiteCoefficientDerivedAdjunction
  finiteCoefficientDerivedAlgClAdjunction algClCommShift

omit [TopologicalSpace.NoetherianSpace X] in
private lemma bounded_factors_cocone
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ℤ)
    (c : Cocone N) (hc : IsColimit c)
    (hsingle : ∀ M, IsConstructibleModuleObject R M → ∀ n : ℤ,
      IsIso (colimit.desc _
        ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
          preadditiveCoyoneda.obj
            (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj M))).mapCocone
          (colimit.cocone N))))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hK : boundedConstructible R K) :
    ∀ f : K ⟶ DerivedCategory.Q.obj c.pt,
      ∃ (i : J) (g : K ⟶ DerivedCategory.Q.obj (N.obj i)),
        f = g ≫ DerivedCategory.Q.map (c.ι.app i) := by
  let : HasColimit N := ⟨⟨c, hc⟩⟩
  let D := N ⋙ DerivedCategory.Q
  let d := DerivedCategory.Q.mapCocone (colimit.cocone N)
  let P := homColimitProperty D d
  have hP : ∀ M, IsConstructibleModuleObject R M →
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    intro M hM
    exact hsingle M hM
  have h : P K := prop_of_boundedConstructibleModule P hP hK
  exact CategoryTheory.factors_of_colimit_cocone N DerivedCategory.Q c hc K
    (CategoryTheory.factors_iso _ ((shiftFunctorZero _ ℤ).app K)
      (CategoryTheory.shiftFactors_of_hom_colimit N DerivedCategory.Q K h 0))

omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_eq {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsCompIso X ℓ h = finiteCoefficientDerivedTensorCompIso X ℓ h := rfl

attribute [local irreducible] derivedExtendScalarsCompIso

set_option backward.isDefEq.respectTransparency true in
omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency true in
omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_inv {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).inv.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).inv.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  exact Category.comp_id _

omit [TopologicalSpace.NoetherianSpace X] in
private lemma toAlgCl_map_hom {E : FiniteIntermediateField ℓ}
    {K L : PadicSubfieldConstructible X ℓ E} (g : K ⟶ L) :
    ((constructibleToPadicAlgCl X ℓ E).map g).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map g.hom := rfl

set_option backward.isDefEq.respectTransparency true in
/-- **(Hom), surjectivity**: every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` between extensions of
scalars of bounded constructible complexes is the extension of scalars of a morphism
`T^X_{E,H} K_E ⟶ T^X_{F,H} L_F` for some finite subextension `H ⊇ E, F`. See the module
docstring. -/
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj := by
  intro E F K L f
  let G := IsFiltered.max E F
  let I := AsSmall.{u + 1} (Under G)
  let H : I ⥤ FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := Under G)).inverse ⋙ Under.forget G
  let : H.Final :=
    Functor.final_equivalence_comp (AsSmall.equiv (C := Under G)).inverse (Under.forget G)
  have he (i : I) : E ≤ H.obj i :=
    le_trans (leOfHom (IsFiltered.leftToMax E F)) (leOfHom (ULift.down i).hom)
  have hf (i : I) : F ≤ H.obj i :=
    le_trans (leOfHom (IsFiltered.rightToMax E F)) (leOfHom (ULift.down i).hom)
  have pres := exists_condensed_coefficient_complex_presentation
    X ℓ E F L.obj L.property.1.1 H he hf
  rcases pres with ⟨N, pres⟩
  rcases pres with ⟨c, hc, hN, pres⟩
  rcases hc with ⟨hc⟩
  rcases pres with ⟨eΩ, ei, hcomp⟩
  let adj := finiteCoefficientDerivedAlgClHomEquiv X ℓ E K.obj
    ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj L.obj)
  have hfactor : ∀ f : K.obj ⟶ DerivedCategory.Q.obj c.pt,
      ∃ (i : I) (g : K.obj ⟶ DerivedCategory.Q.obj (N.obj i)),
        f = g ≫ DerivedCategory.Q.map (c.ι.app i) :=
    bounded_factors_cocone X (padicSubfieldRingObj X ℓ E) N c hc
    (fun M hM n ↦ isIso_constructible_condensed_sheaf_hom_colimit X ℓ E M hM N hN n)
    K.obj K.property
  have ff : {a : K.obj ⟶ DerivedCategory.Q.obj c.pt // a = adj f.hom ≫ eΩ.inv} :=
    ⟨_, rfl⟩
  have hres : ∃ (i : I) (g : K.obj ⟶ DerivedCategory.Q.obj (N.obj i)),
      ff.val = g ≫ DerivedCategory.Q.map (c.ι.app i) := hfactor ff.val
  obtain ⟨i, g, hg⟩ := hres
  let g' : (derivedExtendScalarsSubfield X ℓ (he i)).obj K.obj ⟶
      (derivedExtendScalarsSubfield X ℓ (hf i)).obj L.obj :=
    (finiteCoefficientDerivedHomEquiv X ℓ (he i) K.obj _).symm
    (g ≫ (ei i).hom)
  refine ⟨H.obj i, he i, hf i, ObjectProperty.homMk g', ?_⟩
  apply (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map_injective
  change f.hom = _
  simp only [constructibleCocone, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, tensorComp_inv, tensorComp_hom,
    toAlgCl_map_hom, ObjectProperty.homMk]
  apply adj.injective
  have hh' : adj f.hom = (g ≫ DerivedCategory.Q.map (c.ι.app i)) ≫ eΩ.hom :=
    eΩ.comp_inv_eq.mp (ff.property.symm.trans hg)
  exact hh'.trans ((Category.assoc _ _ _).trans (hcomp i K.obj g).symm)

private noncomputable def ambientCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicAlgClRingObj X ℓ))) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E
  iso h := (Functor.associator (constructibleExtendScalars X ℓ h)
    (constructibleToPadicAlgCl X ℓ _) (boundedConstructible (padicAlgClRingObj X ℓ)).ι).symm ≪≫
    Functor.isoWhiskerRight (constructibleToPadicAlgClCompIso X ℓ h)
      (boundedConstructible (padicAlgClRingObj X ℓ)).ι

set_option backward.isDefEq.respectTransparency true in
@[instance_reducible]
private noncomputable def ambientCommShift (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
    (derivedExtendScalarsToPadicAlgCl X ℓ E) ℤ _ _ _ _
    (inferInstance) (algClCommShift X ℓ E)

set_option backward.isDefEq.respectTransparency true in
private lemma ambientTriangulated (E : FiniteIntermediateField ℓ) :
    letI := ambientCommShift X ℓ E
    ((ambientCocone X ℓ).Φ E).IsTriangulated := by
  let _ := ambientCommShift X ℓ E
  have htri : (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated :=
    algClTriangulated X ℓ E
  exact inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated)

set_option backward.isDefEq.respectTransparency true in
private lemma ambientHomSurj : (ambientCocone X ℓ).HomSurj := by
  intro i j K L f
  have hdesc : ∃ (k : FiniteIntermediateField ℓ) (hi : i ≤ k) (hj : j ≤ k)
      (g : (constructibleExtendScalars X ℓ hi).obj K ⟶
        (constructibleExtendScalars X ℓ hj).obj L),
      ObjectProperty.homMk f =
        (constructibleToPadicAlgClCompIso X ℓ hi).inv.app K ≫
          (constructibleToPadicAlgCl X ℓ k).map g ≫
            (constructibleToPadicAlgClCompIso X ℓ hj).hom.app L :=
    constructibleCocone_homSurj X ℓ i j K L (ObjectProperty.homMk f)
  obtain ⟨k, hi, hj, g, hg⟩ := hdesc
  refine ⟨k, hi, hj, g, ?_⟩
  change f =
    (((constructibleToPadicAlgClCompIso X ℓ hi).inv.app K).hom ≫ 𝟙 _) ≫
      (derivedExtendScalarsToPadicAlgCl X ℓ k).map g.hom ≫
        (𝟙 _ ≫ ((constructibleToPadicAlgClCompIso X ℓ hj).hom.app L).hom)
  simpa only [Category.comp_id, Category.id_comp, constructibleCocone, ambientCocone,
    constructibleToPadicAlgCl, ObjectProperty.lift, ObjectProperty.homMk,
    Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, toAlgCl_map_hom] using congrArg (·.hom) hg

set_option backward.isDefEq.respectTransparency false in
private lemma single_model (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ)) (hM : IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M) :
    ∃ E, ((ambientCocone X ℓ).Φ E).essImage ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨E, M_E, hE, ⟨e⟩⟩ := exists_constructible_finiteCoefficient_model X ℓ M hM
  refine ⟨E, ⟨(DerivedCategory.singleFunctor _ 0).obj M_E,
    CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject _ 0 hE⟩,
    ⟨?_⟩⟩
  let F := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  have es : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj
        ((DerivedCategory.singleFunctor _ 0).obj M_E) ≅
      (DerivedCategory.singleFunctor _ 0).obj (F.obj M_E) :=
    (singleExactDerivedIso
      (C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
      (D := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) F).app M_E
  exact es ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e

set_option backward.isDefEq.respectTransparency true in
/-- **(Obj)** (blueprint `proposition-dctf-x-qbar-2-colimit--2`): every bounded constructible
`ℚ̄_ℓ,X`-complex is isomorphic to the extension of
scalars `T^X_{E,Ω} K_E` of a bounded constructible `E_X`-complex `K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. See the module docstring. -/
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj := by
  intro K
  let commShift : ∀ E, ((ambientCocone X ℓ).Φ E).CommShift ℤ := ambientCommShift X ℓ
  have triangulated : ∀ E, ((ambientCocone X ℓ).Φ E).IsTriangulated :=
    ambientTriangulated X ℓ
  let P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))) :=
    fun Y ↦ ∃ E, ((ambientCocone X ℓ).Φ E).essImage Y
  have : P.IsTriangulated :=
    CategoryCocone.isTriangulated_exists_essImage _ (ambientHomSurj X ℓ)
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨E, hE⟩ ↦ ⟨E, ((ambientCocone X ℓ).Φ E).essImage.prop_of_iso e hE⟩⟩
  have hP : ∀ M, IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M →
      P ((DerivedCategory.singleFunctor _ 0).obj M) := single_model X ℓ
  obtain ⟨E, K_E, ⟨e⟩⟩ := prop_of_boundedConstructibleModule P hP K.property
  exact ⟨E, K_E, ⟨(boundedConstructible (padicAlgClRingObj X ℓ)).ι.preimageIso e⟩⟩

end TwoColimit

end AlgebraicGeometry.ProEtale

end

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℚ̄_ℓ` is a 2-colimit -/

section TwoColimit

variable [TopologicalSpace.NoetherianSpace X]

omit [TopologicalSpace.NoetherianSpace X] in
/-- **(Hom), injectivity**: two morphisms of bounded constructible `H_X`-complexes with the same
extension of scalars to `ℚ̄_ℓ,X` have the same extension of scalars to `H'_X` for some finite
subextension `H' ⊇ H`. See the module docstring. -/
theorem constructibleCocone_homInj : (constructibleCocone X ℓ).HomInj :=
  fun k _ _ g g' h ↦ by
    have hΦ {K L : PadicSubfieldConstructible X ℓ k} (g : K ⟶ L) :
        (((constructibleCocone X ℓ).Φ k).map g).hom =
        (derivedExtendScalarsToPadicAlgCl X ℓ k).map g.hom := rfl
    have h' := congrArg InducedCategory.Hom.hom h
    rw [hΦ, hΦ] at h'
    rw [InducedCategory.hom_ext
      ((derivedExtendScalarsToPadicAlgCl X ℓ k).map_injective h')]
    exact ⟨k, le_rfl, rfl⟩

/-- **`ℚ̄_ℓ` is a 2-colimit**: the bounded constructible derived category `D^b_cons(X, ℚ̄_ℓ)`
of `ℚ̄_ℓ,X`-modules, with the extensions of scalars from the bounded constructible derived
categories `D^b_cons(X, E)` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, is the filtered
2-colimit of the latter: the comparison functor `2-colim_E D^b_cons(X, E) ⟶ D^b_cons(X, ℚ̄_ℓ)`,
`(E, K_E) ↦ ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E`, is an equivalence of ordinary categories. -/
theorem constructibleCocone_isFilteredTwoColimit :
    (constructibleCocone X ℓ).IsFilteredTwoColimit where
  essSurjObj := constructibleCocone_essSurjObj X ℓ
  homSurj := constructibleCocone_homSurj X ℓ
  homInj := constructibleCocone_homInj X ℓ

end TwoColimit

end AlgebraicGeometry.ProEtale
