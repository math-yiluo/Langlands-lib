/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.LeftUnitorShift
public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
public import WeilConjectures.CategoryTheory.Monoidal.SubcategoryShiftNatTrans
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraidingShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

/-!
# The monoidal structure of bounded constructible complexes commutes with the shifts

For an `ℓ`-adic coefficient ring `Λ`, the following natural transformations of `Dᵇc(X)⟦Λ⟧`
commute with the shifts, since their analogues on `D(Mod_{Λ_X})` do
(`WeilConjectures.CategoryTheory.Monoidal.SubcategoryShiftNatTrans`):

* `g ⊗ -` and `- ⊗ g` for a morphism `g`;
* the associator, natural in its first or in its middle variable;
* the left unitor `𝟙 ⊗ - ⟶ 𝟭`;
* the Koszul braiding, natural in either variable
  (`ProEtale.CondensedRing.boundedConstructibleBraidingNatTrans₁`,
  `ProEtale.CondensedRing.boundedConstructibleBraidingNatTrans₂`); for the first variable this
  uses that the braiding is symmetric
  (`ProEtale.CondensedRing.boundedConstructible_braiding_hom_braiding_hom`).

## Implementation notes

The instance problems `∀ K, ((curriedTensor D(Mod_{Λ_X})).obj K).CommShift ℤ` of the generic
statements time out; the families are given explicitly
(`ProEtale.CondensedRing.commShiftTensorLeftFamily`,
`ProEtale.CondensedRing.commShiftTensorRightFamily`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The commutations of the derived tensor products `K ⊗ᴸ -` of `D(Mod_{Λ_X})` with the shifts, as
a family (instance search for the family times out). -/
noncomputable abbrev commShiftTensorLeftFamily (X : Scheme.{u}) :
    ∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), ((curriedTensor (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).obj K).CommShift ℤ :=
  fun K ↦ DerivedCategory.commShiftTensorLeft _ K

/-- The commutations of the derived tensor products `- ⊗ᴸ K` of `D(Mod_{Λ_X})` with the shifts, as
a family. -/
noncomputable abbrev commShiftTensorRightFamily (X : Scheme.{u}) :
    ∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), ((curriedTensor (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).flip.obj
          K).CommShift ℤ :=
  fun K ↦ DerivedCategory.commShiftTensorRight _ K

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

instance commShift_boundedConstructible_curriedTensor_map {K K' :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : K ⟶ K') : NatTrans.CommShift ((curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj
        ℓ⟧)).map g) ℤ := by
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) X.left
  let := commShiftTensorRightFamily (Profinite.padicAlgClRingObj ℓ) X.left
  have := commShift_curriedTensor_map (Profinite.padicAlgClRingObj ℓ) g.hom
  exact ObjectProperty.commShift_curriedTensor_map _ g

instance commShift_boundedConstructible_curriedTensor_flip_map {K K' :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : K ⟶ K') : NatTrans.CommShift ((curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj
        ℓ⟧)).flip.map g) ℤ := by
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) X.left
  let := commShiftTensorRightFamily (Profinite.padicAlgClRingObj ℓ) X.left
  have := Functor.CommShift₂.commShift_flip_map
    (G := curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))) (h := .int) g.hom
  exact ObjectProperty.commShift_curriedTensor_flip_map _ g

instance commShift_boundedConstructible_associatorNatTrans₁ (K L :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    NatTrans.CommShift (associatorNatTrans₁ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) K L) ℤ :=
        by
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) X.left
  let := commShiftTensorRightFamily (Profinite.padicAlgClRingObj ℓ) X.left
  have : NatTrans.CommShift (associatorNatTrans₁ (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left))) K.obj L.obj)
      ℤ := inferInstance
  exact ObjectProperty.commShift_associatorNatTrans₁ _ K L

instance commShift_boundedConstructible_associatorNatTrans₂ (K L :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    NatTrans.CommShift (associatorNatTrans₂ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) K L) ℤ :=
        by
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) X.left
  let := commShiftTensorRightFamily (Profinite.padicAlgClRingObj ℓ) X.left
  have : NatTrans.CommShift (associatorNatTrans₂ (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left))) K.obj L.obj)
      ℤ := inferInstance
  exact ObjectProperty.commShift_associatorNatTrans₂ _ K L

instance commShift_boundedConstructible_leftUnitorNatTrans :
    NatTrans.CommShift (leftUnitorNatTrans (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ℤ := by
  let := commShiftTensorLeftFamily (Profinite.padicAlgClRingObj ℓ) X.left
  have : NatTrans.CommShift (leftUnitorNatTrans (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) X.left)))) ℤ :=
    ⟨fun n ↦ by
      ext K
      simpa using DerivedCategory.leftUnitor_commShift_app _ K n⟩
  exact ObjectProperty.commShift_leftUnitorNatTrans _

section Braiding

attribute [local instance] boundedConstructibleBraiding

/-- The Koszul braiding of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is symmetric. -/
lemma boundedConstructible_braiding_hom_braiding_hom (K M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj
    ℓ⟧) :
    (β_ K M).hom ≫ (β_ M K).hom = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ ?_
  exact DerivedCategory.braiding_hom_braiding_hom _
    (fun A B ↦ SymmetricCategory.symmetry A B) K.obj M.obj

/-- The braiding `K ⊗ M ⟶ M ⊗ K` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, natural in its second variable `M`. -/
@[simps]
noncomputable def boundedConstructibleBraidingNatTrans₂ (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj
    ℓ⟧) :
    (curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K ⟶ (curriedTensor
        (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).flip.obj K where
  app M := (β_ K M).hom
  naturality _ _ f := BraidedCategory.braiding_naturality_right K f

/-- The braiding `M ⊗ K ⟶ K ⊗ M` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, natural in its first variable `M`. -/
@[simps]
noncomputable def boundedConstructibleBraidingNatTrans₁ (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj
    ℓ⟧) :
    (curriedTensor (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).flip.obj K ⟶ (curriedTensor
        (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K where
  app M := (β_ M K).hom
  naturality _ _ f := BraidedCategory.braiding_naturality_left f K

instance commShift_boundedConstructibleBraidingNatTrans₂ (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    NatTrans.CommShift (boundedConstructibleBraidingNatTrans₂ K) ℤ :=
  ⟨fun a ↦ by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      boundedConstructibleBraidingNatTrans₂_app]
    exact (boundedConstructible_braiding_hom_commShiftIso_hom_app a K M).symm⟩

instance commShift_boundedConstructibleBraidingNatTrans₁ (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    NatTrans.CommShift (boundedConstructibleBraidingNatTrans₁ K) ℤ := by
  have : IsIso (boundedConstructibleBraidingNatTrans₂ K) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [boundedConstructibleBraidingNatTrans₂_app]
    infer_instance
  have h : boundedConstructibleBraidingNatTrans₁ K =
      inv (boundedConstructibleBraidingNatTrans₂ K) := by
    rw [← cancel_epi (boundedConstructibleBraidingNatTrans₂ K), IsIso.hom_inv_id]
    exact NatTrans.ext (funext fun M ↦ boundedConstructible_braiding_hom_braiding_hom K M)
  rw [h]
  exact NatTrans.CommShift.of_isIso _ ℤ

end Braiding

end AlgebraicGeometry.ProEtale.CondensedRing
