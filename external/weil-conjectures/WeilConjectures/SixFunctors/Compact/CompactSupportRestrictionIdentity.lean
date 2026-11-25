/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportCoefficientPresentation
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Mathlib.Algebra.Homology.Localization

/-! # Identity normalization of the compact-support restriction comparison

Source: Step 5 of the coefficient quotient cocycle proof, and the sectionwise and
K-injective normalizations of the open/proper restriction comparisons.
(blueprint: lem-coef-compact-support-restriction-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  constantSheaf presheafToSheaf Functor.leftAdjoint

private theorem quotient_hom_id {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (J : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app J = 𝟙 (DerivedCategory.Q.obj J) := rfl

private theorem quotient_inv_id {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (J : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app J = 𝟙 (DerivedCategory.Q.obj J) := rfl

private theorem homotopyFactors_inv_id
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J =
      𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj J)) := rfl

private theorem identity_factors {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (J : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj J) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app J := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj J)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  simp only [quotient_hom_id, quotient_inv_id, homotopyFactors_inv_id] at h
  erw [(𝟭 C).mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at h
  exact h

private theorem coefficient_identity_factors (W : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (J : CochainComplex (proEtaleRingModules W (proEtaleConstantRing W A)) ℤ) :
    (sfOpenDerivedCoefficientRestrictionId W A).hom.app (DerivedCategory.Q.obj J) =
      (proEtaleCoefficientRestrictScalars W (RingHom.id A)).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (sfOpenCoefficientRestrictionId W A).hom (.up ℤ)).app
            J) := by
  dsimp only [sfOpenDerivedCoefficientRestrictionId, Iso.trans_hom, NatTrans.comp_app]
  rw [identity_factors, Functor.mapDerivedCategoryNatIso_fac]

private theorem direct_image_identity {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (A : Type u) [CommRing A] [Finite A] (K : proEtaleDerivedCategory Z A) :
    (sfDerivedImageRestriction g (RingHom.id A)).hom.app K ≫
        (sfOpenDerivedCoefficientRestrictionId Y A).hom.app
          ((proEtaleConstantDerivedDirectImage g A).obj K) =
      (proEtaleConstantDerivedDirectImage g A).map
        ((sfOpenDerivedCoefficientRestrictionId Z A).hom.app K) := by
  let F := proEtaleConstantModuleDirectImage g A
  let x := proEtaleCoefficientRestrictScalars Z (RingHom.id A)
  let y := proEtaleCoefficientRestrictScalars Y (RingHom.id A)
  let c := proEtaleCoefficientDirectImageComparison g (RingHom.id A)
  have hi : CategoryTheory.ExactDerivedSquare.unitNormalized F F (𝟭 _) (𝟭 _)
      (𝟭 _) (𝟭 _) (Iso.refl _) (Iso.refl _) (𝟙 F) (𝟙 F.rightDerivedFunctor) := by
    intro J
    change F.rightDerivedFunctorUnitQ J ≫ 𝟙 _ ≫ F.rightDerivedFunctor.map (𝟙 _) =
      𝟙 _ ≫ DerivedCategory.Q.map (𝟙 _) ≫ F.rightDerivedFunctorUnitQ J
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]
    erw [Category.comp_id, Category.id_comp]
  have hc (M : proEtaleRingModules Z (proEtaleConstantRing Z A)) :
      (sfOpenCoefficientRestrictionId Y A).hom.app (F.obj M) ≫ (𝟙 F : F ⟶ F).app M =
        c.hom.app M ≫ F.map ((sfOpenCoefficientRestrictionId Z A).hom.app M) := by
    erw [NatTrans.id_app, Category.comp_id]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext t
    change ((sfOpenCoefficientRestrictionId Y A).hom.app (F.obj M)).val.app V t =
      (F.map ((sfOpenCoefficientRestrictionId Z A).hom.app M)).val.app V
        ((c.hom.app M).val.app V t)
    rw [AlgebraicGeometry.Scheme.coefficientRestrictionId_apply]
    have hn := (proEtaleCoefficientDirectImageComparison_existsUnique g
      (RingHom.id A)).choose_spec.1 M V t
    change (c.hom.app M).val.app V t = t at hn
    rw [hn]
    change t = ((sfOpenCoefficientRestrictionId Z A).hom.app M).val.app _ t
    exact (AlgebraicGeometry.Scheme.coefficientRestrictionId_apply Z A M _ t).symm
  have h := CategoryTheory.ExactDerivedSquare.normalized_naturality
    F F x y (𝟭 _) (𝟭 _) x.mapDerivedCategory (𝟭 _) y.mapDerivedCategory (𝟭 _)
    x.mapDerivedCategoryFactors (Iso.refl _) y.mapDerivedCategoryFactors (Iso.refl _)
    c.hom (𝟙 F) (sfDerivedImageRestriction g (RingHom.id A)).inv (𝟙 F.rightDerivedFunctor)
    (compactSupportScalarDirectNormalization g (RingHom.id A)) hi
    (sfOpenCoefficientRestrictionId Z A).hom (sfOpenCoefficientRestrictionId Y A).hom
    (sfOpenDerivedCoefficientRestrictionId Z A).hom
    (sfOpenDerivedCoefficientRestrictionId Y A).hom
    (fun J ↦ by
      dsimp only [Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
      exact coefficient_identity_factors Z A J)
    (fun J ↦ by
      dsimp only [Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
      exact coefficient_identity_factors Y A J) hc
  have hk := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hk
  erw [Category.comp_id] at hk
  rw [← cancel_epi ((sfDerivedImageRestriction g (RingHom.id A)).inv.app K)]
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hk

private theorem compact_support_identity {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) :
    (compactSupportCoefficientComparison c (RingHom.id A)).hom.app K ≫
        (sfOpenDerivedCoefficientRestrictionId Y A).hom.app
          ((sfAmbientCompactSupportCandidate A c).obj K) =
      (sfAmbientCompactSupportCandidate A c).map
        ((sfOpenDerivedCoefficientRestrictionId X A).hom.app K) := by
  have ho := sfOpenRestriction_derived_id c.i A K
  have hd := direct_image_identity c.g A
    ((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj K)
  let P := proEtaleConstantDerivedDirectImage c.g A
  let o := (sfOpenRestrictionDerived c.i (RingHom.id A)).hom.app K
  change (P.map o ≫ (sfDerivedImageRestriction c.g (RingHom.id A)).hom.app _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t ↦ P.map o ≫ t) hd).trans
      ((P.map_comp _ _).symm.trans (congrArg P.map ho)))

private theorem coefficient_res_id (W : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    compactSupportCoefficientResId W A (RingHom.id A) rfl =
      sfOpenDerivedCoefficientRestrictionId W A := by
  unfold compactSupportCoefficientResId
  exact Iso.refl_trans _

/-- The published compact-support restriction square for the identity coefficient map
is the square of the canonical identity restriction comparisons.

Source: Step 5 of `lem-coef-compact-support-quotient-cocycle`, blueprint
`lem-coef-integral-compact-support.proof.md`, finite-level comparison; Stacks Tags 03DI and 0D6E.
(blueprint: lem-coef-compact-support-restriction-identity).

Proof: restriction along the identity acts as the identity on the underlying sheaves.
The ordinary comparison sfOpenCoefficientRestrictionId is the sectionwise identity
transported through the canonical realization equivalence. The unit-normalized
extension-by-zero square for the identity coefficient homomorphism commutes with
these comparisons: apply its adjunction and use the identity on each generator of
extension by zero. Localize this equality termwise. For direct image, use the specified
K-injective normalization: both routes are the identity coefficient restriction map
on the same K-injective representative, followed by the same universal comparison.
Uniqueness of the right-derived comparison extends the equality to every unbounded
object. Whisker the open equality by derived direct image and the proper equality by
extension by zero. Their composite is sfCompactSupportRestriction by definition and
gives the displayed identity. Transport along hq inserts exactly the two eqToIso
comparisons in the statement. No coefficient invertibility or boundedness is needed
for these identity normalization calculations. -/
theorem compactSupportRestriction_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (A : Type u) [CommRing A] [Finite A]
    (q : A →+* A) (hq : q = RingHom.id A) (K : proEtaleDerivedCategory X A) :
    (compactSupportCoefficientComparison c q).hom.app K ≫
        (compactSupportCoefficientResId Y A q hq).hom.app
          ((sfAmbientCompactSupportCandidate A c).obj K) =
      (sfAmbientCompactSupportCandidate A c).map
        ((compactSupportCoefficientResId X A q hq).hom.app K) := by
  cases hq
  rw [coefficient_res_id, coefficient_res_id]
  exact compact_support_identity c A K

end WeilConjectures
