/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.FiniteProperComparisonIso
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison

/-! # Proper quotient coefficient mate

Source: Bhatt--Scholze Lemmas 6.7.7 and 6.1.13; Stacks Tag 0GL6.
(blueprint: lem-pur-completed-quotient-proper-mate).
The lower normalization calculation is reused from QcqsCompactSupportFiniteMates
without importing that consumer of the integral comparison module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
open PurCompactSupport

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard
  sfCompletedCoefficientMap proEtaleRingDirectImageMap
  coefficient_inverse_image_iso finite_inverse_image_iso purCoefficientIso
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  constantSheaf completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingProjectionUnrestricted

section QuotientMate
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem finiteKInjective (W : Scheme.{u}) (m : ℕ) :
    Abelian.HasKInjectiveResolutions (scalarReductionTarget.{u, u} l E W m) :=
  proEtaleRingModules_hasKInjectiveResolutions W (integralCoefficientCommRingSheaf l E W m)

attribute [local instance] finiteKInjective

private theorem trim_identities {C : Type*} [Category C] {A B D : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D) (h : a ≫ b ≫ 𝟙 D = c) :
    a ≫ b = c ≫ 𝟙 D := by
  simpa only [Category.comp_id] using h

private theorem identity_projection_cube
    {C D H : Type*} [Category C] [Category D] [Category H]
    (R : C ⥤ H) (G : D ⥤ H) (M : C) (N : D) (a : G.obj N ⟶ R.obj M) :
    a ≫ 𝟙 _ ≫ R.map (𝟙 M) = 𝟙 _ ≫ G.map (𝟙 N) ≫ a := by
  rw [R.map_id M, G.map_id N]
  simp only [Category.comp_id, Category.id_comp]

private theorem chain_unit_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) :
    chainDerivedUnit F I = canonical_cochain_unit F I := by
  calc
    chainDerivedUnit F I =
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I) := by
      change 𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _) = _
      erw [F.rightDerivedFunctor.map_id, Category.comp_id, Category.id_comp]
    _ = canonical_cochain_unit F I := (canonical_cochain_unit_eq_unit F I).symm

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem ring_unit_eq
    {U V : Scheme.{u}} (g : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S)
    (I : CochainComplex (proEtaleRingModules U S) ℤ) :
    proEtaleRingDirectImageDerivedUnit g R S c I =
      canonical_cochain_unit (proEtaleRingModuleDirectImage g R S c) I :=
  chain_unit_eq (proEtaleRingModuleDirectImage g R S c) I

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem finiteProperComparison_app_mate
    {R S : Coefficients.{u}} (a : Change R S) {U V : Scheme.{u}} (g : U ⟶ V)
    (K : DerivedCategory (pbcModules U (R.ring U))) :
    (finiteProperComparison a g).app K =
      ((pbcDerivedScalarAdjunction (a.map V)).homEquiv _ _).symm
        ((proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
          ((pbcDerivedScalarAdjunction (a.map U)).unit.app K) ≫
          (proEtaleRingRestrictionDerivedDirectImage g
            (R.ring V) (S.ring V) (R.ring U) (S.ring U)
            (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv.app
              ((pbcDerivedExtend (a.map U)).obj K)) := by
  simp only [finiteProperComparison, mateEquiv_symm_apply, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, Functor.comp_map, Functor.comp_obj, Category.assoc,
    Category.id_comp]
  erw [Category.comp_id]

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
@[irreducible] private def quotientMateIso
    {U V : Scheme.{u}} (g : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aV ≫ cS.hom)
    (K : DerivedCategory (proEtaleRingModules U RU)) : Prop :=
  IsIso (((pbcDerivedScalarAdjunction aV).homEquiv _ _).symm
    ((proEtaleRingDerivedDirectImage g RV RU cR).map
      ((pbcDerivedScalarAdjunction aU).unit.app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage g RV SV RU SU aV aU cR cS comm).inv.app
        ((pbcDerivedExtend aU).obj K)))

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
-- Uniqueness of the normalized derived square identifies the two projection-formula maps.
private theorem normalized_quotient_mate
    (F : scalarReductionTarget.{u, u} l E X n ⥤ scalarReductionTarget.{u, u} l E Y n)
    (G : scalarReductionSource.{u, u} l E X ⥤ scalarReductionSource.{u, u} l E Y)
    [F.Additive] [G.Additive]
    (hF : F = proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1)))
    (hG : G = sfCompletedModuleDirectImage l E f)
    (a : F ⋙ scalarReductionRestriction l E Y n ≅
      scalarReductionRestriction l E X n ⋙ G)
    (ha : Functor.isoWhiskerRight (eqToIso hF).symm
        (scalarReductionRestriction l E Y n) ≪≫ a ≪≫
        Functor.isoWhiskerLeft (scalarReductionRestriction l E X n) (eqToIso hG) =
      sfDirectImageRestrictionComparison l E f n)
    (d : F.rightDerivedFunctor ⋙ (scalarReductionRestriction l E Y n).mapDerivedCategory ≅
      (scalarReductionRestriction l E X n).mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hd : normalized_square F G (scalarReductionRestriction l E X n)
      (scalarReductionRestriction l E Y n) a d)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    IsIso (((pbcDerivedScalarAdjunction
      (completedIntegralCommRingProjectionUnrestricted l E Y n)).homEquiv _ _).symm
        (G.rightDerivedFunctor.map ((pbcDerivedScalarAdjunction
          (completedIntegralCommRingProjectionUnrestricted l E X n)).unit.app K) ≫
            d.inv.app ((pbcDerivedExtend
              (completedIntegralCommRingProjectionUnrestricted l E X n)).obj K))) := by
  subst F
  subst G
  have heq : a = sfDirectImageRestrictionComparison l E f n := by
    simpa only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
      Functor.isoWhiskerLeft_refl, Iso.refl_trans, Iso.trans_refl] using ha
  subst a
  have hdeq : d = (sfDerivedRestrictionComparison l E f n).symm := by
    apply Iso.ext
    apply derived_natTrans_ext_on_kinjectives
    intro I hI
    have := canonical_cochain_unit_isIso
      (proEtaleConstantModuleDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))) I
    apply (cancel_epi ((scalarReductionRestriction l E Y n).mapDerivedCategory.map
      (canonical_cochain_unit (proEtaleConstantModuleDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))) I))).mp
    apply (cancel_mono ((sfCompletedDerivedDirectImage l E f).map
      ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app I))).mp
    have hi := (hd I).trans (sf_restriction_normalization l E f n I).symm
    dsimp only [scalarReductionDerivedRestriction, sfCompletedDerivedDirectImage,
      Iso.symm_hom] at hi ⊢
    simpa only [Category.assoc] using hi
  subst d
  let ax := pbcDerivedScalarAdjunction
    (completedIntegralCommRingProjectionUnrestricted l E X n)
  let ay := pbcDerivedScalarAdjunction
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
  let ax' := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
  let ay' := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose
  obtain ⟨sx, hsx⟩ := IntegralCoefficientPresentation.square_iso ax' ax
    (𝟭 _) (𝟭 _) (Iso.refl _)
  obtain ⟨sy, hsy⟩ := IntegralCoefficientPresentation.square_iso ay' ay
    (𝟭 _) (𝟭 _) (Iso.refl _)
  refine projection_formula_transport _ _ _ _ _ _ _ _ ax ay ax' ay'
    (sfCompletedDerivedDirectImage l E f)
    (proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctor
    (sfCompletedDerivedDirectImage l E f)
    (proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctor
    (𝟭 _) (𝟭 _) (𝟭 _) (𝟭 _) (Iso.refl _) (Iso.refl _) sx sy
    (Iso.refl _) (Iso.refl _) (sfDerivedRestrictionComparison l E f n)
    (sfDerivedRestrictionComparison l E f n) ?_ ?_ ?_ K ?_
  · intro Z
    exact trim_identities _ _ _ (hsx Z)
  · intro Z
    exact trim_identities _ _ _ (hsy Z)
  · intro N
    exact identity_projection_cube (scalarReductionDerivedRestriction l E Y n)
      (sfCompletedDerivedDirectImage l E f) _ _
      ((sfDerivedRestrictionComparison l E f n).hom.app N)
  · exact sf_projection_formula l E f n K

-- Eliminate equality transports before using the identity-on-sections uniqueness clause.
private theorem ordinary_comparison_normalized
    (F : scalarReductionTarget.{u, u} l E X n ⥤ scalarReductionTarget.{u, u} l E Y n)
    (G : scalarReductionSource.{u, u} l E X ⥤ scalarReductionSource.{u, u} l E Y)
    (hF : F = proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1)))
    (hG : G = sfCompletedModuleDirectImage l E f)
    (a : F ⋙ scalarReductionRestriction l E Y n ≅
      scalarReductionRestriction l E X n ⋙ G)
    (ha : ∀ (M : scalarReductionTarget.{u, u} l E X n) (U : Y.ProEtᵒᵖ)
      (x : (F.obj M).val.obj U), HEq ((a.hom.app M).val.app U x) x) :
    Functor.isoWhiskerRight (eqToIso hF).symm
        (scalarReductionRestriction l E Y n) ≪≫ a ≪≫
        Functor.isoWhiskerLeft (scalarReductionRestriction l E X n) (eqToIso hG) =
      sfDirectImageRestrictionComparison l E f n := by
  subst F
  subst G
  simp only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_trans, Iso.trans_refl]
  apply (sfDirectImageRestrictionComparison_existsUnique l E f n).unique
  · intro M U x
    exact eq_of_heq (ha M U x)
  · exact (sfDirectImageRestrictionComparison_existsUnique l E f n).exists.choose_spec

private theorem completed_pull_eq :
    (completed l E).pull f = coefficient_inverse_image_iso l E f := by
  apply Iso.ext
  apply ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).injective
  change (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
      (sfCompletedCoefficientMap l E f)) = _
  rw [Equiv.apply_symm_apply]
  simpa only [proEtaleRingDirectImageMap, Adjunction.homEquiv_unit, completed] using
    (coefficient_direct_image_eq l E f).symm

private theorem finite_pull_eq :
    (finite l E (n + 1) (Nat.le_add_left 1 n)).pull f =
      finite_inverse_image_iso l E f n := by
  apply Iso.ext
  exact (finite_inverse_image_eq l E f n).symm

private theorem projection_square (n : ℕ) (hn : 1 ≤ n)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ((completed l E).pull g).hom ≫ projection l E n hn U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (projection l E n hn V) ≫
        ((finite l E n hn).pull g).hom := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n =>
    let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
    change (adj.homEquiv _ _).symm (sfCompletedCoefficientMap l E g) ≫
        completedIntegralCommRingProjectionUnrestricted l E U n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E V n) ≫
        (adj.homEquiv _ _).symm
          (proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)))
    rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm]
    apply congrArg (adj.homEquiv _ _).symm
    simpa only [sfCompletedCoefficientMap] using
      ((sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n)

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- The actual proper quotient scalar mate is invertible on every derived input.
Source: Bhatt--Scholze Lemmas 6.7.7 and 6.1.13; Stacks Tag 0GL6.
(blueprint: lem-pur-completed-quotient-proper-mate).
Proof: identify the ordinary restriction square by its identity section maps.
Uniqueness on K-injective complexes identifies its derived square with the
normalized finite reduction square. Transport the known quotient projection
formula through the two scalar adjunctions. Finally substitute the completed
and finite inverse-image identifications; proof irrelevance identifies their
commutative-square witnesses. This applies to zero objects and all shifts. -/
theorem completedQuotientProperMate
    (a : Change (completed l E) (finite l E (n + 1) (Nat.le_add_left 1 n)))
    (hmap : ∀ W, a.map W = projection l E (n + 1) (Nat.le_add_left 1 n) W)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    IsIso ((finiteProperComparison a f).app K) := by
  rcases a with ⟨amap, asquare⟩
  have hamap : amap = projection l E (n + 1) (Nat.le_add_left 1 n) := funext hmap
  subst amap
  let RV := completedIntegralCommRingSheafUnrestricted l E Y
  let RU := completedIntegralCommRingSheafUnrestricted l E X
  let SV := integralCoefficientCommRingSheaf l E Y n
  let SU := integralCoefficientCommRingSheaf l E X n
  let aV := completedIntegralCommRingProjectionUnrestricted l E Y n
  let aU := completedIntegralCommRingProjectionUnrestricted l E X n
  let cR := coefficient_inverse_image_iso l E f
  let cS := finite_inverse_image_iso l E f n
  have comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom := by
    rw [finite_inverse_image_eq]
    exact coefficient_inverse_image_projection l E f n
  let F := proEtaleRingModuleDirectImage f SV SU cS
  let G := proEtaleRingModuleDirectImage f RV RU cR
  have : F.Additive := proEtaleRingModuleDirectImage_additive f SV SU cS
  have : G.Additive := proEtaleRingModuleDirectImage_additive f RV RU cR
  let a := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let d := proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU aV aU cR cS comm
  have hF : F = proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1)) := finite_direct_image_eq l E f n
  have hG : G = sfCompletedModuleDirectImage l E f := completed_direct_image_eq l E f
  have ha : Functor.isoWhiskerRight (eqToIso hF).symm
      (scalarReductionRestriction l E Y n) ≪≫ a ≪≫
      Functor.isoWhiskerLeft (scalarReductionRestriction l E X n) (eqToIso hG) =
      sfDirectImageRestrictionComparison l E f n := by
    apply ordinary_comparison_normalized l E f n F G hF hG a
    intro M U x
    exact heq_of_eq ((Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
      f RV SV RU SU aV aU cR cS comm)).1 M U x)
  -- Both derived comparisons are fixed by this same cochain-unit equation.
  have hd : normalized_square F G (scalarReductionRestriction l E X n)
      (scalarReductionRestriction l E Y n) a d := by
    intro I
    have h := (Classical.choose_spec (proEtaleRingRestrictionDerivedDirectImage_existsUnique
      f RV SV RU SU aV aU cR cS comm)).1 I
    simpa only [F, G, a, d, ring_unit_eq, proEtaleRingRestrictionDerivedDirectImage,
      proEtaleRingDerivedDirectImage] using h
  have hiso := normalized_quotient_mate l E f n F G hF hG a ha d hd K
  have hp (W : Scheme.{u}) : projection l E (n + 1) (Nat.le_add_left 1 n) W =
      completedIntegralCommRingProjectionUnrestricted l E W n := by
    change completedIntegralCommRingProjectionUnrestricted l E W n ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [finiteProperComparison_app_mate]
  change IsIso (((pbcDerivedScalarAdjunction (projection l E (n + 1)
    (Nat.le_add_left 1 n) Y)).homEquiv _ _).symm
      ((proEtaleRingDerivedDirectImage f RV RU ((completed l E).pull f)).map
        ((pbcDerivedScalarAdjunction (projection l E (n + 1)
          (Nat.le_add_left 1 n) X)).unit.app K) ≫
        (proEtaleRingRestrictionDerivedDirectImage f RV SV RU SU
          (projection l E (n + 1) (Nat.le_add_left 1 n) Y)
          (projection l E (n + 1) (Nat.le_add_left 1 n) X)
          ((completed l E).pull f) ((finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)
          (projection_square l E (n + 1) (Nat.le_add_left 1 n) f)).inv.app
            ((pbcDerivedExtend (projection l E (n + 1)
              (Nat.le_add_left 1 n) X)).obj K)))
  -- Keep the mate opaque while substituting the four coefficient identifications.
  have hn : quotientMateIso f RV SV RU SU aV aU cR cS comm K := by
    unfold quotientMateIso
    exact hiso
  have transfer (bV : RV ⟶ SV) (bU : RU ⟶ SU)
      (eR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
      (eS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
      (hbV : bV = aV) (hbU : bU = aU) (heR : eR = cR) (heS : eS = cS)
      (hc : eR.hom ≫ bU =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map bV ≫ eS.hom) :
      quotientMateIso f RV SV RU SU bV bU eR eS hc K := by
    subst bV
    subst bU
    subst eR
    subst eS
    exact hn
  have ho := transfer _ _ _ _ (hp Y) (hp X) (completed_pull_eq l E f)
    (finite_pull_eq l E f n) (projection_square l E (n + 1) (Nat.le_add_left 1 n) f)
  unfold quotientMateIso at ho
  exact ho

end QuotientMate
end WeilConjectures
