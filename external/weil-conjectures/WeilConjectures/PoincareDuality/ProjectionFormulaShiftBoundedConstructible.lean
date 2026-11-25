/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekShift

/-!
# The exceptional projection morphism on bounded constructible complexes commutes with the shifts

The exceptional projection morphism `PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded
constructible complexes commutes with the shifts in `B`
(`ProEtale.CondensedRing.commShift_boundedConstructibleExceptionalProjectionNatTrans`): through
the fully faithful inclusions it is the exceptional projection morphism of the ambient derived
categories, which does
(`ProEtale.CondensedRing.commShift_exceptionalProjectionMorphismOfCompactificationNatTrans`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y}

/-- The exceptional projection morphism `PF^!_{c,K,-}` of a compactification `c` of `f` on
bounded constructible complexes, as a natural transformation
`Rf_!^c K ⊗ᴸ - ⟶ Rf_!^c (K ⊗ᴸ Lf^* -)`. -/
@[simps]
noncomputable def boundedConstructibleExceptionalProjectionOfCompactificationNatTrans
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (curriedTensor _).obj ((boundedConstructibleLowerShriekOfCompactification ℓ c).obj K) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙ (curriedTensor _).obj K)
          ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c where
  app B := ObjectProperty.homMk
    (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
    (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
      (K ⊗ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj B))
    (exceptionalProjectionMorphismOfCompactification (Profinite.padicAlgClRingObj ℓ) c K.obj B.obj)
  naturality _ _ h :=
    boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_right ℓ f c K h

set_option linter.flexible false in
set_option synthInstance.maxSize 4096 in
-- the instance problems for the composite functors are large
-- the instances of the composite functors are large
/-- The exceptional projection morphism of a compactification on bounded constructible complexes
commutes with the shifts in its second variable. -/
instance commShift_boundedConstructibleExceptionalProjectionOfCompactificationNatTrans
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    NatTrans.CommShift
      (boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ c K) ℤ := by
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) X.left
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) Y.left
  let := commShiftTensorRightFamily (Profinite.padicAlgClRingObj ℓ) X.left
  let := commShiftTensorRightFamily (Profinite.padicAlgClRingObj ℓ) Y.left
  have : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι.Faithful
      :=
    ObjectProperty.faithful_ι _
  let e₂ : ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙ (curriedTensor
      _).obj K) ⋙
      boundedConstructibleLowerShriekOfCompactification ℓ c) ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι ≅
      (boundedConstructible _).ι ⋙ ((L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ (curriedTensor
          _).obj K.obj) ⋙
        Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationCompatibility
        ℓ c) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (ObjectProperty.tensorLeftCompιIso _ K) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility
            (Profinite.padicAlgClRingObj ℓ) ℓ f) _ ≪≫
        Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift e₂.hom ℤ := by
    dsimp only [e₂, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  refine NatTrans.CommShift.of_whiskerRight_eq _ (boundedConstructible _).ι
    (ObjectProperty.tensorLeftCompιIso _
      ((boundedConstructibleLowerShriekOfCompactification ℓ c).obj K)) e₂
    (Functor.whiskerLeft (boundedConstructible _).ι
      (exceptionalProjectionMorphismOfCompactificationNatTrans (Profinite.padicAlgClRingObj ℓ) c
          K.obj)) ?_
  refine NatTrans.ext (funext fun B ↦ ?_)
  simp [e₂, ObjectProperty.tensorLeftCompιIso, ObjectProperty.tensorLeftIsoLift,
    ObjectProperty.liftFullSubcategoryCompιIso, boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerShriekOfCompactificationCompatibility,
    boundedConstructibleLowerStarOfIsProperCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

section PadicAlgCl

/-- The exceptional projection morphism of the canonical compactification of `f` is an
isomorphism at every object. -/
instance isIso_boundedConstructibleExceptionalProjectionOfCompactificationNatTrans_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (f : X ⟶ Y) :
    IsIso ((boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ
      (compactificationOverField f) K).app B) :=
  isIso_boundedConstructibleExceptionalProjectionMorphism ℓ f K B

/-- The exceptional projection morphism of the canonical compactification of `f` is a natural
isomorphism. -/
instance isIso_boundedConstructibleExceptionalProjectionOfCompactificationNatTrans
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (f : X ⟶ Y) :
    IsIso (boundedConstructibleExceptionalProjectionOfCompactificationNatTrans ℓ
      (compactificationOverField f) K) :=
  NatIso.isIso_of_isIso_app _

end PadicAlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
