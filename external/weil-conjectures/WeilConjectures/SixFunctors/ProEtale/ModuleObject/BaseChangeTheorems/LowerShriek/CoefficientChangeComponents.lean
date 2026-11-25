/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback

/-!
# Components of the bounded constructible six functors on the ambient derived categories

The bounded constructible functors `Dᵇc(-)⟦Λ⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` are restrictions
of the six functors on the ambient derived categories. This file records that the units and
counits of the restricted adjunctions `Lf^* ⊣ Rf_*` and `j_! ⊣ Lj^*` are, on the ambient derived
categories, those of the ambient adjunctions, and that the restricted functors act on morphisms
as the ambient ones.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section UpperLowerStar

variable {Λ} (f : X ⟶ Y)
  (hR : ∀ K : Dᵇc(X.left)⟦Λ⟧, boundedConstructible (condensedRingObj Λ Y.left)
    ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj))

/-- On the ambient derived category, the unit of the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` to bounded constructible complexes
is the unit of the ambient adjunction. -/
lemma restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_unit_app_hom
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    (((derivedUpperStarLowerStarAdjunction Λ f.left).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
      (ObjectProperty.liftCompιIso _ _ hR).symm).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).unit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (ObjectProperty.liftCompιIso _ _ hR).symm K).trans ?_
  simp [boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso]

/-- On the ambient derived category, the counit of the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` to bounded constructible complexes
is the counit of the ambient adjunction. -/
lemma restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_counit_app_hom
    (K : Dᵇc(X.left)⟦Λ⟧) :
    (((derivedUpperStarLowerStarAdjunction Λ f.left).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
      (ObjectProperty.liftCompιIso _ _ hR).symm).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).counit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (ObjectProperty.liftCompιIso _ _ hR).symm K).trans ?_
  simp only [boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso, Iso.symm_inv, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end UpperLowerStar

section PadicAlgCl

variable (f : X ⟶ Y)

lemma boundedConstructibleLowerStar_obj_obj (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerStar ℓ f).obj K).obj =
      (lowerStar (Profinite.padicAlgClRingObj ℓ) f.left).rightDerivedFunctor.obj K.obj :=
  rfl

lemma boundedConstructibleLowerStar_map_hom
    {K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : K ⟶ L) :
    ((boundedConstructibleLowerStar ℓ f).map φ).hom =
      (lowerStar (Profinite.padicAlgClRingObj ℓ) f.left).rightDerivedFunctor.map φ.hom :=
  rfl

/-- On the ambient derived category, the unit of `Lf^* ⊣ Rf_*` on bounded constructible complexes
is the unit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom'
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).unit.app
        K.obj :=
  restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_unit_app_hom ℓ f _ K

/-- On the ambient derived category, the counit of `Lf^* ⊣ Rf_*` on bounded constructible
complexes is the counit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom'
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).counit.app
        K.obj :=
  restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_counit_app_hom ℓ f _ K

end PadicAlgCl

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y)

lemma boundedConstructibleLowerStar_obj_obj (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStar ℓ E f).obj K).obj =
      (lowerStar (Profinite.continuousMapRingObj E) f.left).rightDerivedFunctor.obj K.obj :=
  rfl

lemma boundedConstructibleLowerStar_map_hom
    {K L : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧} (φ : K ⟶ L) :
    ((boundedConstructibleLowerStar ℓ E f).map φ).hom =
      (lowerStar (Profinite.continuousMapRingObj E) f.left).rightDerivedFunctor.map φ.hom :=
  rfl

/-- On the ambient derived category, the unit of `Lf^* ⊣ Rf_*` on bounded constructible complexes
is the unit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom'
    (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) f.left).unit.app
        K.obj :=
  restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_unit_app_hom ℓ f _ K

/-- On the ambient derived category, the counit of `Lf^* ⊣ Rf_*` on bounded constructible
complexes is the counit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom'
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) f.left).counit.app
        K.obj :=
  restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_counit_app_hom ℓ f _ K

end ContinuousMapRingObj

section OpenImmersion

variable (j : X ⟶ Y) [IsOpenImmersion j.left]

lemma boundedConstructibleOpenImmersionLowerShriek_obj_obj (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K).obj =
      (openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj K.obj :=
  rfl

lemma boundedConstructibleOpenImmersionLowerShriek_map_hom {K L : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ L) :
    ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).map φ).hom =
      (openImmersionLowerShriek Λ j.left).mapDerivedCategory.map φ.hom :=
  rfl

/-- On the ambient derived category, the unit of `j_! ⊣ Lj^*` on bounded constructible complexes
is the unit of the ambient adjunction `D(j_!) ⊣ Lj^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom
    (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app K).hom =
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm).unit.app
          K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm K).trans ?_
  simp [boundedConstructibleOpenImmersionLowerShriekCompatibility,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso]

/-- On the ambient derived category, the counit of `j_! ⊣ Lj^*` on bounded constructible
complexes is the counit of the ambient adjunction `D(j_!) ⊣ Lj^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).counit.app K).hom =
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm).counit.app
          K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
    (boundedConstructibleUpperStarCompatibility Λ ℓ j).symm K).trans ?_
  simp only [boundedConstructibleOpenImmersionLowerShriekCompatibility,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.symm_inv,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
