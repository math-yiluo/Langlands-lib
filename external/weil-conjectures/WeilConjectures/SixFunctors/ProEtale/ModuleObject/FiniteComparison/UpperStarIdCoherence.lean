/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarIdCoherence

/-!
# The finite-coefficient comparison and the identity pullbacks

Let `T` be a finite discrete commutative ring and `Φ = ProEtale.finiteCoefficientModEquivalence`.
For the identity of a scheme `X`, the commutation `(𝟙 X)^* ⋙ Φ ≅ Φ ⋙ (𝟙 X)^*`
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso`) is the composite of the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭` of module objects over `T̲` and of sheaves of `T`-modules
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso_hom_app_id`), and the same holds for the
derived comparison (`ProEtale.finiteCoefficientDerivedUpperStarIso_hom_app_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] (X : Scheme.{u})

/-- The isomorphism `lowerStarFiniteCoefficientModEquivalenceIso` for the identity is compatible
with the identity isomorphisms of the pushforwards. -/
lemma lowerStarFiniteCoefficientModEquivalenceIso_id
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (finiteCoefficientModEquivalence X T).functor.map
        ((CondensedRing.lowerStarId (Profinite.continuousMapRingObj T) X).hom.app N) =
      (lowerStarFiniteCoefficientModEquivalenceIso (𝟙 X) T).hom.app N ≫
        (ProEtale.lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).hom.app
          ((finiteCoefficientModEquivalence X T).functor.obj N) := by
  apply (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) Ab.{u + 1})).map_injective
  rfl

/-- The inverse form of `lowerStarFiniteCoefficientModEquivalenceIso_id`. -/
lemma lowerStarFiniteCoefficientModEquivalenceIso_id_inv
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (finiteCoefficientModEquivalence X T).functor.map
        ((CondensedRing.lowerStarId (Profinite.continuousMapRingObj T) X).inv.app N) =
      (ProEtale.lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).inv.app
          ((finiteCoefficientModEquivalence X T).functor.obj N) ≫
        (lowerStarFiniteCoefficientModEquivalenceIso (𝟙 X) T).inv.app N := by
  rw [← cancel_epi ((finiteCoefficientModEquivalence X T).functor.map
      ((CondensedRing.lowerStarId (Profinite.continuousMapRingObj T) X).hom.app N)),
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    lowerStarFiniteCoefficientModEquivalenceIso_id]
  simp

/-- **The finite-coefficient comparison commutes with the pullback along the identity** through
the identity isomorphisms of the pullbacks. -/
theorem upperStarFiniteCoefficientModEquivalenceIso_hom_app_id
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (upperStarFiniteCoefficientModEquivalenceIso (𝟙 X) T).hom.app M ≫
        (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).hom.app
          ((finiteCoefficientModEquivalence X T).functor.obj M) =
      (finiteCoefficientModEquivalence X T).functor.map
        ((CondensedRing.upperStarId (Profinite.continuousMapRingObj T) X).hom.app M) := by
  have key : (upperStarFiniteCoefficientModEquivalenceIso (𝟙 X) T).hom ≫
      Functor.whiskerLeft _ (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).hom ≫
        (Functor.rightUnitor _).hom =
      Functor.whiskerRight (CondensedRing.upperStarId (Profinite.continuousMapRingObj T) X).hom
        (finiteCoefficientModEquivalence X T).functor ≫ (Functor.leftUnitor _).hom := by
    apply (conjugateEquiv (finiteCoefficientModEquivalence X T).toAdjunction
      ((CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T)
        (𝟙 X)).comp (finiteCoefficientModEquivalence X T).toAdjunction)).injective
    rw [← conjugateEquiv_comp _ ((finiteCoefficientModEquivalence X T).toAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) (𝟙 X))),
      ← conjugateEquiv_comp _
        ((finiteCoefficientModEquivalence X T).toAdjunction.comp Adjunction.id),
      ← conjugateEquiv_comp _
        (Adjunction.id.comp (finiteCoefficientModEquivalence X T).toAdjunction),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom,
      conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft]
    have h₀ : conjugateEquiv ((finiteCoefficientModEquivalence X T).toAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) (𝟙 X)))
        ((CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T)
          (𝟙 X)).comp (finiteCoefficientModEquivalence X T).toAdjunction)
        (upperStarFiniteCoefficientModEquivalenceIso (𝟙 X) T).hom =
        (Iso.inverseCompIso (Iso.isoCompInverse (lowerStarFiniteCoefficientModEquivalenceIso
          (𝟙 X) T) ≪≫ Functor.associator _ _ _)).inv := by
      rw [upperStarFiniteCoefficientModEquivalenceIso,
        Adjunction.symm_conjugateIsoEquiv_symm_apply, ← conjugateIsoEquiv_apply_hom,
        Equiv.apply_symm_apply, Iso.symm_hom]
    have h₁ := congrArg Iso.hom
      (ProEtale.conjugateIsoEquiv_upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X)
    have h₂ := congrArg Iso.hom
      (CondensedRing.conjugateIsoEquiv_upperStarId (Profinite.continuousMapRingObj T) X)
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at h₁ h₂
    rw [h₀, h₁, h₂]
    ext N : 2
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Category.id_comp]
    apply (finiteCoefficientModEquivalence X T).functor.map_injective
    rw [Functor.map_comp,
      Adjunction.functor_map_inverseCompIso_isoCompInverse_inv_app, Equivalence.fun_inv_map,
      lowerStarFiniteCoefficientModEquivalenceIso_id_inv]
    have hn := (ProEtale.lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).inv.naturality
      ((finiteCoefficientModEquivalence X T).counit.app N)
    rw [Functor.id_map] at hn
    rw [Category.assoc, Category.assoc]
    erw [Iso.inv_hom_id_app_assoc, reassoc_of% hn]
    rw [← Functor.map_comp_assoc]
    erw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa using NatTrans.congr_app key M

/-- **The derived finite-coefficient comparison commutes with the pullback along the identity**
through the identity isomorphisms `L(𝟙)^* ≅ 𝟭` of the derived pullbacks. -/
theorem finiteCoefficientDerivedUpperStarIso_hom_app_id
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    (finiteCoefficientDerivedUpperStarIso T (𝟙 X)).hom.app M ≫
        (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).hom.app
          ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.obj M) =
      (finiteCoefficientModEquivalence X T).functor.mapDerivedCategory.map
        ((CondensedRing.leftDerivedUpperStarId (Profinite.continuousMapRingObj T) X).hom.app
          M) := by
  simp only [finiteCoefficientDerivedUpperStarIso, CondensedRing.leftDerivedUpperStarId,
    ProEtale.leftDerivedUpperStarId, Functor.leftDerivedFunctorIdIso,
    Functor.leftDerivedFunctorNatIso,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have h := Functor.mapDerivedCategoryNatIso_hom_app_id
    (finiteCoefficientModEquivalence X T).functor
    (CondensedRing.upperStarId (Profinite.continuousMapRingObj T) X)
    (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} T)) X)
    (upperStarFiniteCoefficientModEquivalenceIso (𝟙 X) T).symm (fun N ↦ by
      rw [Iso.symm_hom, ← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom,
        upperStarFiniteCoefficientModEquivalenceIso_hom_app_id])
    M
  rw [Functor.mapDerivedCategoryNatIso_symm] at h
  rw [cancel_epi, ← h]
  simp

end AlgebraicGeometry.ProEtale
