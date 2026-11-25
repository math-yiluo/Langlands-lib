/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem heq_apply_cast {α α' : Type v} {β β' : Type w}
    (hα : α = α') (hβ : β = β') (f : α → β) (g : α' → β')
    (h : HEq f g) (x : α') :
    f (cast hα.symm x) = cast hβ.symm (g x) := by
  cases hα
  cases hβ
  exact congrFun (eq_of_heq h) x

private theorem restriction_map_section (W : Scheme.{u})
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E W).map f).app (op n)).val.app U
        (integralComparisonRestrictedSection l E W M n U x) =
      integralComparisonRestrictedSection l E W N n U (f.val.app (op (n, U.unop)) x) := by
  exact heq_apply_cast (integralComparisonRestrictedSectionType l E W M n U)
    (integralComparisonRestrictedSectionType l E W N n U) _ _
    ((coefficientSequenceRestriction_exists l E W).exists.choose_spec.2.2 f n U) x

private theorem restriction_site_section (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ)
    {U V : W.ProEt} (f : U ⟶ V) (x : M.val.obj (op (n, V))) :
    (((coefficientSequenceRestriction l E W).obj M).obj (op n)).val.map f.op
        (integralComparisonRestrictedSection l E W M n (op V) x) =
      integralComparisonRestrictedSection l E W M n (op U)
        (M.val.map (Prod.mkHom (𝟙 n) f).op x) := by
  apply heq_apply_cast (integralComparisonRestrictedSectionType l E W M n (op V))
    (integralComparisonRestrictedSectionType l E W M n (op U)) _ _ ?_ x
  rw [← integralComparisonRestrictionCurried_eq l E W]
  rfl

private theorem identity_site_composite (W : Scheme.{u}) (U : W.ProEt) :
    proEtaleIsoCommaArrow (𝟙 W) U ≫
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).hom.app
          ((proEtaleIsoPostcompose (𝟙 W)).obj U) =
      (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl).hom.app U := by
  apply MorphismProperty.Over.Hom.ext
  change (proEtaleIsoCommaArrow (𝟙 W) U).left ≫
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).hom.app
        ((proEtaleIsoPostcompose (𝟙 W)).obj U)).left = 𝟙 U.left
  rw [MorphismProperty.Over.pullbackId_hom_app_left]
  change pullback.lift (𝟙 U.left) U.hom (by simp) ≫
    pullback.fst (U.hom ≫ 𝟙 W) (𝟙 W) = 𝟙 U.left
  exact pullback.lift_fst _ _ _

private theorem identity_restriction_section (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEt)
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose (𝟙 W)).obj U))) :
    M.val.map (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow (𝟙 W) U)).op
        (M.val.map (Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).hom.app
            ((proEtaleIsoPostcompose (𝟙 W)).obj U))).op x) =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl).hom.app U)).op x := by
  let δ := proEtaleIsoCommaArrow (𝟙 W) U
  let ε := (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).hom.app
    ((proEtaleIsoPostcompose (𝟙 W)).obj U)
  let μ := (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl).hom.app U
  have hpair : (Prod.mkHom (𝟙 n) ε).op ≫ (Prod.mkHom (𝟙 n) δ).op =
      (Prod.mkHom (𝟙 n) μ).op := by
    apply Quiver.Hom.unop_inj
    apply Prod.hom_ext
    · apply Subsingleton.elim
    · exact identity_site_composite W U
  exact (M.val.map_comp_apply
    (Prod.mkHom (𝟙 n) ε).op (Prod.mkHom (𝟙 n) δ).op x).symm.trans
      (M.val.congr_map_apply hpair x)

/-- The restricted-system identity agrees with the ordinary degreewise relabelling.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03D6 and 0941 (blueprint: lem-pod-identity-restricted-tower).

Proof: on each restricted section generator, RestrictedGenerators and the unit
formula for integralComparisonSequenceUnit identify the composite tower map with
the degreewise ordinary identity relabelling. This identifies every component and
transition of the strict tower. Naturality of the
ordinary identity comparison identifies its component on each restricted module.
Extensionality in the tower index and cochain degree gives the displayed equality,
including zero complexes. No Roos complex or derived comparison is involved. -/
theorem podIdentityRestrictedTower
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (D : PodCompletionReindex l E (𝟙 W))
    (hD : PodCompletionReindex.RestrictedGenerators l E (𝟙 W) D)
    (a : isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _)
    (ha : ∀ (M : scalarReductionSource l E W) (U : W.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (𝟙 W)).obj U))),
      (a.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W
          (𝟙 W) rfl).hom.app U).op x)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    let σ := NatIso.mapHomologicalComplex (integralComparisonSequenceUnit l E W) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    (D.restricted C).hom ≫ HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map
          (σ.hom.app C)) =
      (isoWhiskerLeft (podRestrictedTower l E C) α ≪≫
        (podRestrictedTower l E C).rightUnitor).hom := by
  dsimp only
  ext n i U z
  let σ := (integralComparisonSequenceUnit l E W).hom.app (C.X i)
  let R := coefficientSequenceRestriction l E W
  change (((R.map σ).app n).val.app U)
      (((((D.restricted C).hom.app n).f i).val.app U) z) =
    ((a.hom.app ((R.obj (C.X i)).obj n)).val.app U) z
  let x := cast (integralComparisonRestrictedSectionType l E W (C.X i) n.unop
    (op ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop))) z
  have hz : integralComparisonRestrictedSection l E W (C.X i) n.unop
      (op ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop)) x = z := by
    simp only [integralComparisonRestrictedSection, x, cast_cast, cast_eq]
  rw [← hz, hD C n.unop i U.unop x]
  rw [restriction_map_section l E W σ n.unop U]
  rw [ha ((R.obj (C.X i)).obj n) U.unop]
  erw [restriction_site_section l E W (C.X i) n.unop
    ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ W (𝟙 W) rfl).hom.app U.unop) x]
  have hu := (integralComparisonSequenceUnit_existsUnique l E W).exists.choose_spec
    (C.X i) n.unop ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop) x
  have hn := PresheafOfModules.naturality_apply σ.val
    (Prod.mkHom (𝟙 n.unop) (proEtaleIsoCommaArrow (𝟙 W) U.unop)).op
      (integralComparisonSequenceGenerator l E (𝟙 W) (C.X i) n.unop
        ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop) x)
  change σ.val.app (op (n.unop,
      (proEtaleBaseChange (𝟙 W)).obj ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop)))
      (integralComparisonSequenceGenerator l E (𝟙 W) (C.X i) n.unop
        ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop) x) = _ at hu
  rw [hn, hu]
  congr 1
  exact identity_restriction_section l E W (C.X i) n.unop U.unop x

end WeilConjectures
