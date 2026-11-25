/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitInsertion
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! # The regular unit at the identity scalar map

Source: Stacks 07A4 and 0D6D, the tensor clause of the finite-Hom domain calculation.
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem restriction_unit_id
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u})
    (φ : A →+* A) (hφ : φ = RingHom.id A) :
    Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ) =
      (ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology φ hφ).inv.app
        (𝟙_ _) := by
  subst φ
  apply Sheaf.hom_ext_of_ε_comp
  rw [Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose]
  have hη : Functor.LaxMonoidal.ε ((Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
      (ModuleCat.restrictScalars.{u + 1} (RingHom.id A))) = 𝟙 _ := by
    ext U : 2
    apply ModuleCat.hom_ext
    ext
    erw [ModuleCat.restrictScalars_η]
    rfl
  rw [hη, Category.id_comp]
  ext U : 2
  apply ModuleCat.hom_ext
  ext
  rfl

private theorem unit_identity_transport
    {C : Type*} [Category C] (F : C ⥤ C) (α : F ≅ 𝟭 C)
    {A B : C} (i : A ≅ B) (a : F.obj B ⟶ B)
    (h : F.map i.hom ≫ a ≫ i.inv = α.hom.app A) :
    a = α.hom.app B := by
  have hn := α.hom.naturality i.hom
  dsimp only [Functor.id_map] at hn
  apply (cancel_epi (F.map i.hom)).1
  apply (cancel_mono i.inv).1
  calc
    (F.map i.hom ≫ a) ≫ i.inv = α.hom.app A := by
      simpa only [Category.assoc] using h
    _ = (F.map i.hom ≫ α.hom.app B) ≫ i.inv := by
      rw [hn, Category.assoc, i.hom_inv_id]
      exact (Category.comp_id _).symm

private theorem adjoint_identity_unit
    {C : Type*} [Category C] {F R : C ⥤ C} (ad : F ⊣ R)
    (e : R ≅ 𝟭 C) (M : C) :
    (ad.homEquiv _ _).symm (e.inv.app M) =
      (Adjunction.leftAdjointIdIso ad e).hom.app M := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have h := unit_conjugateEquiv (Adjunction.id) ad
    (Adjunction.leftAdjointIdIso ad e).hom M
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  change 𝟙 _ ≫ e.inv.app M = ad.unit.app M ≫ R.map _ at h
  erw [Category.id_comp] at h
  exact h

private theorem insertion_identity
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (R : C ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : _root_.DerivedCategory C ⥤ _root_.DerivedCategory C}
    (a : L ⊣ R.mapDerivedCategory) (e : R ≅ 𝟭 C) (M : C)
    (f : M ⟶ R.obj M) (hf : f = e.inv.app M) :
    SheafExactDegreeZero.adjointInsertion R a f =
      (Adjunction.leftAdjointIdIso a
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C)).hom.app
          ((_root_.DerivedCategory.singleFunctor C 0).obj M) := by
  have h := SheafExactDegreeZero.raw_unit_id R e M f hf
  unfold SheafExactDegreeZero.adjointInsertion
  rw [h]
  exact adjoint_identity_unit _ _ _

end WeilConjectures
