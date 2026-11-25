/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural

/-!

# Reduction modulo `ℓⁿ` commutes with the pushforward on bounded constructible complexes

For a morphism `d : Z ⟶ Y` of separated `k`-schemes of finite type, the comparison
`γ : Rd_*^{𝒪_E} ⋙ red_Y ⟶ red_Z ⋙ Rd_*^{𝒪_E ⧸ ℓⁿ}` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction`) is, on the
underlying complexes, the comparison on the full derived categories
(`ProEtale.CondensedRing.derivedLowerStarIntegersModPowReduction`): both are mates of the
inverse of (Pull), and the adjunctions and (Pull) on bounded constructible complexes are
restrictions of those on the derived categories. Hence `γ` is an isomorphism as soon as the
comparison on the derived categories is
(`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_isIso`),
in particular under the compatibilities of (Pull) with the natural reduction triangle
(`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible`).
This is blueprint `lemma-change-coefficients-direct-image` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, for every `d`
(proper or not), modulo the two compatibilities.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [TopologicalSpace.NoetherianSpace Z.left]
  [TopologicalSpace.NoetherianSpace Y.left] (d : Z ⟶ Y)

/-- The restricted (Pull) is (Pull) on the underlying complexes. -/
lemma boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n d).inv.app K).hom =
      (integersModPowReductionUpperStarIso ℓ E n d.left).inv.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleUpperStarIntegersModPowReductionIso,
    Functor.whiskeringRight_obj_obj, boundedConstructibleIntegersModPowReductionCompatibility,
    ObjectProperty.liftCompιIso, boundedConstructibleUpperStarCompatibility,
    Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Iso.refl_hom, Category.assoc, Functor.isoWhiskerRight_inv, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- **Reduction modulo `ℓⁿ` commutes with the pushforward on bounded constructible complexes**,
as soon as it does on the full derived categories. -/
theorem isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_isIso
    (h : IsIso (derivedLowerStarIntegersModPowReduction ℓ E n d.left)) :
    IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have hK : IsIso ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction _ d.left)
      (derivedUpperStarLowerStarAdjunction _ d.left)
      (integersModPowReductionUpperStarIso ℓ E n d.left).symm).app K.obj) := by
    rw [Adjunction.exchangeRight_eq_mateEquiv]
    exact (NatTrans.isIso_iff_isIso_app _).1 h K.obj
  have := Adjunction.isIso_exchangeRight_restrictFullyFaithful_app
    (derivedUpperStarLowerStarAdjunction _ d.left) (derivedUpperStarLowerStarAdjunction _ d.left)
    (integersModPowReductionUpperStarIso ℓ E n d.left).symm _
    (fun K ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E d K) _
    (fun K ↦ IntegersModPowRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E n d K) _ _
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n d).symm
    (boundedConstructibleUpperStarIntegersModPowReductionIso_inv_app_hom ℓ E n d) K hK
  rw [Adjunction.exchangeRight_eq_mateEquiv] at this
  rw [boundedConstructibleLowerStarIntegersModPowReduction]
  exact this

/-- **Reduction modulo `ℓⁿ` commutes with the pushforward on bounded constructible complexes**
(blueprint `lemma-change-coefficients-direct-image` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`), for an arbitrary morphism
`d`, given the compatibilities of (Pull) with the units and the connecting morphisms of the
natural reduction triangles. -/
theorem isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible
    (hη : IntegersModPowPullUnitCompatible ℓ E n d.left)
    (hδ : IntegersModPowPullδCompatible ℓ E n d.left) :
    IsIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n d) :=
  isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_isIso ℓ E n d
    (isIso_derivedLowerStarIntegersModPowReduction_of_compatible ℓ E n d.left hη hδ)

end AlgebraicGeometry.ProEtale.CondensedRing
