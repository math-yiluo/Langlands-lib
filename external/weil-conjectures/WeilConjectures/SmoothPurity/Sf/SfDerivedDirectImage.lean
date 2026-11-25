/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage

import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Finite and integral derived direct images with canonical quotient comparisons

Source: Weil blueprint, order 1468; Bhatt--Scholze, Sections 6.5 and 6.7;
Stacks Tags 03DA, 0D6E and 06YY (blueprint: prose-03-02).
The integral object is presented as a chosen Roos triangle, in accordance with the
recorded definition of derived limit; the finite comparison is the adjunct of its
specified projection, rather than a chosen isomorphism of its endpoints.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
private theorem constantDirectImage_naturality (A B : CommRingCat.{u + 1}) (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold proEtaleConstantDirectImageMap
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((proEtaleBaseChange f).op.obj U))
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).unit.naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantDirectImage_naturality_ring
    (A B : CommRingCat.{u + 1}) (a : A ⟶ B) :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a) ≫
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B) =
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
      (proEtaleSheafDirectImage f RingCat.{u + 1}).map
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map (a.hom.app U))
    (constantDirectImage_naturality f A B a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed coefficient structure map is uniquely determined by its finite
projections and the canonical constant-section maps.
Source: Stacks Tags 03CO and 03DA (blueprint: prose-03-02).
Proof: direct image is a right adjoint and preserves the inverse limit defining
completed coefficients. The constant-section maps commute with quotient maps, so
compose the projections with them and use the universal property of that limit.
Its projections are jointly monic, which proves uniqueness. -/
theorem sfCompletedCoefficientMap_existsUnique :
    ∃! φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X),
      ∀ n : ℕ,
        φ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
          completedIntegralCommRingProjectionUnrestricted l E Y n ≫
            proEtaleCoefficientDirectImageMap f (Padic.coefficientExtensionRing l E (n + 1)) := by
  let G := proEtaleSheafDirectImage f RingCat.{u + 1}
  let H := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let DY := integralCoefficientSheafSystem l E Y
  let DX := integralCoefficientSheafSystem l E X
  let ρ (n : ℕ) := H.map
    (proEtaleCoefficientDirectImageMap f (Padic.coefficientExtensionRing l E (n + 1)))
  let α : DY ⟶ DX ⋙ G := NatTrans.ofOpSequence ρ (by
    intro n
    dsimp only [DY, DX, integralCoefficientSheafSystem, Functor.comp_map]
    rw [Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_map_homOfLE_succ]
    dsimp only [integralCoefficientSheafTransition, ρ, H, G,
      proEtaleCoefficientDirectImageMap]
    have hh := constantDirectImage_naturality_ring f _ _
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)))
    exact hh)
  let c : Cone (DX ⋙ G) := ⟨limit DY, (limit.cone DY).π ≫ α⟩
  let h := isLimitOfPreserves G (limit.isLimit DX)
  let g : H.obj (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
      H.obj ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X)) := h.lift c
  let φ := H.preimage g
  have hφ (n : ℕ) :
      φ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          (completedIntegralCommRingProjectionUnrestricted l E X n) =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          proEtaleCoefficientDirectImageMap f
            (Padic.coefficientExtensionRing l E (n + 1)) := by
    apply H.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    ext U x
    exact congrArg (fun a ↦ a.hom.app U x) (h.fac c (op n))
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply H.map_injective
  apply h.hom_ext
  intro n
  ext U x
  exact congrArg (fun a ↦ a.hom.app U x) ((hψ n.unop).trans (hφ n.unop).symm)

/-- The canonical completed-ring map, with its finite-coordinate normalization.
Source: Stacks Tag 03DA (blueprint: prose-03-02). -/
noncomputable def sfCompletedCoefficientMap :=
  (sfCompletedCoefficientMap_existsUnique l E f).exists.choose

/-- Ordinary direct image over completed coefficients, with the canonical ring map.
Source: Stacks Tag 03DA (blueprint: prose-03-02). -/
noncomputable def sfCompletedModuleDirectImage :
    scalarReductionSource.{u, u} l E X ⥤ scalarReductionSource.{u, u} l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (K := AlgebraicGeometry.Scheme.ProEt.topology X)
    ⟨Functor.whiskerRight (sfCompletedCoefficientMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Completed-coefficient direct image is additive.
Source: Stacks Tag 03DA (blueprint: prose-03-02).
Proof: the functor precomposes the underlying sheaf and its linear maps with base
change. Addition of maps is sectionwise, and scalar restriction respects it. -/
theorem sfCompletedModuleDirectImage_additive : (sfCompletedModuleDirectImage l E f).Additive := by
  constructor
  intro M N a b
  ext U x
  rfl

attribute [instance] sfCompletedModuleDirectImage_additive

/-- K-injective resolutions for the same completed coefficient module category.
Source: Stacks Section 07A5 (blueprint: prose-03-02). -/
noncomputable instance sfCompletedHasKInjectiveResolutions (T : AlgebraicGeometry.Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (scalarReductionSource.{u, u} l E T) :=
  proEtaleRingModules_hasKInjectiveResolutions T
    (completedIntegralCommRingSheafUnrestricted l E T)

/-- The ordinary unbounded derived image for completed coefficients.
Source: Stacks Section 07A5 (blueprint: prose-03-02). -/
noncomputable abbrev sfCompletedDerivedDirectImage :
    DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E Y) :=
  (sfCompletedModuleDirectImage l E f).rightDerivedFunctor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact finite-coefficient scalar square, normalized by identity on sections.
Source: Stacks Tag 0D6E (blueprint: prose-03-02).
Proof: both functors have sections N(X times_Y V). Compatibility of the completed
ring map with its finite projection makes their scalar actions identical. Identity
on sections therefore gives a linear natural isomorphism, uniquely. -/
theorem sfDirectImageRestrictionComparison_existsUnique (n : ℕ) :
    ∃! e : proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          scalarReductionRestriction.{u, u} l E Y n ≅
        scalarReductionRestriction.{u, u} l E X n ⋙ sfCompletedModuleDirectImage l E f,
      ∀ (M : scalarReductionTarget.{u, u} l E X n) (U : Y.ProEtᵒᵖ)
        (x : M.val.obj ((proEtaleBaseChange f).op.obj U)),
        (e.hom.app M).val.app U x = x := by
  let F := proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1))
  let P := scalarReductionRestriction.{u, u} l E X n
  let Q := scalarReductionRestriction.{u, u} l E Y n
  let G := sfCompletedModuleDirectImage l E f
  have hc := (sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec n
  let h (M : scalarReductionTarget.{u, u} l E X n) :
      (F ⋙ Q).obj M ⟶ (P ⋙ G).obj M :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := ((F ⋙ Q).obj M).val.obj U)
            (Y := ((P ⋙ G).obj M).val.obj U)
            { toFun := id
              map_add' := fun _ _ ↦ rfl
              map_smul' := by
                intro r x
                change (proEtaleCoefficientDirectImageMap f
                    (Padic.coefficientExtensionRing l E (n + 1))).hom.app U
                    ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r) •
                    (show M.val.obj ((proEtaleBaseChange f).op.obj U) from x) =
                  (completedIntegralCommRingProjectionUnrestricted l E X n).hom.app
                    ((proEtaleBaseChange f).op.obj U)
                    ((sfCompletedCoefficientMap l E f).hom.app U r) •
                    (show M.val.obj ((proEtaleBaseChange f).op.obj U) from x)
                exact congrArg (fun a : (integralCoefficientCommRingSheaf l E X n).obj.obj
                    ((proEtaleBaseChange f).op.obj U) ↦
                  a • (show M.val.obj ((proEtaleBaseChange f).op.obj U) from x))
                  (congrArg (fun a ↦ a.hom.app U r) hc).symm }
          naturality := by intros; ext x; rfl } }
  let h' (M : scalarReductionTarget.{u, u} l E X n) :
      (P ⋙ G).obj M ⟶ (F ⋙ Q).obj M :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := ((P ⋙ G).obj M).val.obj U)
            (Y := ((F ⋙ Q).obj M).val.obj U)
            { toFun := id
              map_add' := fun _ _ ↦ rfl
              map_smul' := by
                intro r x
                change (completedIntegralCommRingProjectionUnrestricted l E X n).hom.app
                    ((proEtaleBaseChange f).op.obj U)
                    ((sfCompletedCoefficientMap l E f).hom.app U r) •
                    (show M.val.obj ((proEtaleBaseChange f).op.obj U) from x) =
                  (proEtaleCoefficientDirectImageMap f
                    (Padic.coefficientExtensionRing l E (n + 1))).hom.app U
                    ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r) •
                    (show M.val.obj ((proEtaleBaseChange f).op.obj U) from x)
                exact congrArg (fun a : (integralCoefficientCommRingSheaf l E X n).obj.obj
                    ((proEtaleBaseChange f).op.obj U) ↦
                  a • (show M.val.obj ((proEtaleBaseChange f).op.obj U) from x))
                  (congrArg (fun a ↦ a.hom.app U r) hc) }
          naturality := by intros; ext x; rfl } }
  let e : F ⋙ Q ≅ P ⋙ G := NatIso.ofComponents
    (fun M ↦ { hom := h M, inv := h' M
               hom_inv_id := by ext U x; rfl
               inv_hom_id := by ext U x; rfl })
    (by intros; ext U x; rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext U x
  exact he' M U x

/-- The uniquely normalized underived coefficient comparison.
Source: Stacks Tag 0D6E (blueprint: prose-03-02). -/
noncomputable def sfDirectImageRestrictionComparison (n : ℕ) :=
  (sfDirectImageRestrictionComparison_existsUnique l E f n).exists.choose

-- Keep the coefficient limits and constant-sheaf construction behind their APIs.
-- Their internal choices are irrelevant to the derived comparison.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted constantSheaf
  proEtaleConstantModuleDirectImage

set_option backward.isDefEq.respectTransparency false in
private theorem moduleToModel_isEquivalence (T : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).IsEquivalence := by
  let S := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj R
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).functor.IsContinuous
      (ProEt.topology T) (proEtaleModelTopology T) := proEtaleModelUp_isContinuous T
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology T) (ProEt.topology T) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology T) (ProEt.topology T)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)) (𝟙 R) (𝟙 S)
    (by ext U; dsimp [AsSmall.equiv]; erw [S.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)
  exact inferInstanceAs e.inverse.IsEquivalence

section ModelTransport

private noncomputable def ringModuleDirectImageOfMap
    (RU : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RV : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (cR : RV ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj RU) :
    proEtaleRingModules X RU ⥤ proEtaleRingModules Y RV :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    ⟨Functor.whiskerRight cR.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private theorem ringModuleDirectImageOfMap_additive
    (RU : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RV : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (cR : RV ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj RU) :
    (ringModuleDirectImageOfMap f RU RV cR).Additive := by
  constructor
  intro M N a b
  ext U x
  rfl

attribute [local instance] ringModuleDirectImageOfMap_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem ringModuleDirectImage_quasiIso
    (RU SU : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RV : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (aU : RU ⟶ SU)
    (cR : RV ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj RU)
    (I : CochainComplex (proEtaleRingModules X SU) ℤ) [I.IsKInjective]
    (J : CochainComplex (proEtaleRingModules X RU) ℤ) [J.IsKInjective]
    (j : ((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso (((ringModuleDirectImageOfMap f RU RV cR).mapHomologicalComplex
      (.up ℤ)).map j) := by
  -- Present restriction and direct image on small sites; both transports retain sections.
  let eu := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let ev := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  let T := proEtaleModelTopology X
  let S := proEtaleModelTopology Y
  let F := proEtaleModelBaseChange f
  have : F.IsContinuous S T := proEtaleModelBaseChange_isContinuous f
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs ev.inverse.IsEquivalence
  have : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs eu.functor.IsEquivalence
  have : PreservesFiniteLimits F := by
    dsimp only [F, proEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits _
  let L := Functor.sheafPullbackConstruction.sheafPullback F (Type (u + 1)) S T
  have : PreservesFiniteLimits L := by dsimp only [L]; infer_instance
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    F (Type (u + 1)) S T
  have : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsContinuous
      T (ProEt.topology X) :=
    by
      dsimp only [T]
      infer_instance
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsContinuous
      S (ProEt.topology Y) :=
    by
      dsimp only [S]
      infer_instance
  let TU := (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} T (ProEt.topology X)
  let TV := (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} S (ProEt.topology Y)
  let R := TU.obj SU
  let Z := TU.obj RU
  let W := TV.obj RV
  let φ : W ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} S T).obj Z :=
    TV.map cR
  obtain ⟨p, hp⟩ := continuousRingedToposModuleDirectImage_exists F L adj Z W φ
  let a := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (TU.map aU)
  obtain ⟨r, hr⟩ := restrictionRingedToposModuleDirectImage_exists a
  let P := p.modules
  let A := r.modules
  let EM := proEtaleModuleToModel
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)
  let EA := proEtaleModuleToModel
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  let EB := proEtaleModuleToModel
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  have : EM.IsEquivalence := moduleToModel_isEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)
  have : EA.IsEquivalence := moduleToModel_isEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  have : EB.IsEquivalence := moduleToModel_isEquivalence Y
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  have : EM.Additive := EM.additive_of_preserves_binary_products
  have : EA.Additive := EA.additive_of_preserves_binary_products
  have : EB.Additive := EB.additive_of_preserves_binary_products
  have : PreservesFiniteLimits EA := inferInstance
  have : PreservesFiniteColimits EA := inferInstance
  have : EA.PreservesHomology := inferInstance
  have : PreservesFiniteLimits EB := inferInstance
  have : PreservesFiniteColimits EB := inferInstance
  have : EB.PreservesHomology := inferInstance
  have : EB.ReflectsIsomorphisms := inferInstance
  have : EM.PreservesKInjectiveComplexes := inferInstance
  have : EA.PreservesKInjectiveComplexes := inferInstance
  have : P.Additive := p.additive
  have : A.Additive := r.additive
  let H := proEtaleRingRestrictScalars aU
  let G := ringModuleDirectImageOfMap f RU RV cR
  have : H.Additive := inferInstanceAs (proEtaleRingRestrictScalars aU).Additive
  have : G.Additive := inferInstanceAs (ringModuleDirectImageOfMap f RU RV cR).Additive
  let α : EM ⋙ A ≅ H ⋙ EA := by
    dsimp only [A]
    rw [hr]
    exact NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
          intro W W' a
          ext x
          rfl))) (by
        intro M N h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        rfl)
  let β : EA ⋙ P ≅ G ⋙ EB := by
    dsimp only [P]
    rw [hp]
    exact NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
          intro W W' a
          ext x
          rfl))) (by
        intro M N h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        rfl)
  have hq := quasiIso_map_of_models EM EA EB A P H G α β
    (ringed_resolution T T S R Z W r p) I J j
  exact hq

end ModelTransport

set_option backward.isDefEq.respectTransparency false in
private theorem chainDerivedUnit_objQIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    chainDerivedUnit F I = (F.rightDerivedFunctorObjQIso I).inv := by
  simp only [chainDerivedUnit, Functor.rightDerivedFunctorObjQIso, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, asIso_hom, Iso.app_hom,
    quotient_inv_id, quotient_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem chainDerivedUnit_eq_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    chainDerivedUnit F K =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) := by
  simp only [chainDerivedUnit, quotient_hom_id, quotient_inv_id, Category.id_comp]
  erw [F.rightDerivedFunctor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedFactorsh_objQ
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [quotient_hom_id, quotient_inv_id, homotopyFactors_inv_id]
  erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := B)).map_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedRestrictionSquare_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) [F.Additive] (P : A ⥤ C) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (G : C ⥤ D) [G.Additive] (e : F ⋙ Q ≅ P ⋙ G)
    (hacyclic : ∀ (J : CochainComplex A ℤ) [J.IsKInjective]
      (I : CochainComplex C ℤ) [I.IsKInjective]
      (j : (P.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    ∃! d : P.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
        F.rightDerivedFunctor ⋙ Q.mapDerivedCategory,
      ∀ (J : CochainComplex A ℤ) [J.IsKInjective]
        (I : CochainComplex C ℤ) [I.IsKInjective]
        (j : (P.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso j],
        d.hom.app (DerivedCategory.Q.obj J) ≫
            Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
            Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) =
          G.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app J) ≫
            G.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫
            (G.rightDerivedFunctorObjQIso I).hom := by
  let W := HomotopyCategory.quasiIso (A) (.up ℤ)
  let β := Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G
  have hβ : (P.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor β W := by
    apply (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((P ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
    intro K
    obtain ⟨J, hJ, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective K
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((P.mapHomologicalComplex (.up ℤ)).obj J)
    have : I.IsKInjective := hI
    have : QuasiIso j := hj
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) :=
      hacyclic J I j
    have hi := chainDerivedUnit_isIso_of_resolution G _ I j
    have : IsIso (G.rightDerivedFunctorUnit.app
        ((P.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj J))) := by
      rw [chainDerivedUnit_eq_unit] at hi
      exact hi
    change IsIso (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj J))
    rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
    infer_instance
  let := hβ
  let eComp := Functor.rightDerivedUnique (P ⋙ G).rightDerivedFunctor
    (P.mapDerivedCategory ⋙ G.rightDerivedFunctor) (P ⋙ G).rightDerivedFunctorUnit β W
  let d : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).symm ≪≫
      Functor.rightDerivedFunctorNatIso e ≪≫ eComp
  have hd (K : CochainComplex (A) ℤ) :
      Q.mapDerivedCategory.map (chainDerivedUnit F K) ≫
          d.hom.app (DerivedCategory.Q.obj K) ≫
          G.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app K) =
        Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) ≫
          chainDerivedUnit G ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
    let K' := (HomotopyCategory.quotient _ (.up ℤ)).obj K
    have hcomp : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app
        K' = 𝟙 _ := rfl
    have hcomp' : (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app
        K' = 𝟙 _ := rfl
    have h₁ : Q.mapDerivedCategoryFactorsh.inv.app
          ((F.mapHomotopyCategory (.up ℤ)).obj K') ≫
        Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K') ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F Q).inv.app
          (DerivedCategory.Qh.obj K') = (F ⋙ Q).rightDerivedFunctorUnit.app K' := by
      have h := Functor.rightDerivedNatTrans_app
        (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory) (F ⋙ Q).rightDerivedFunctor
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F Q)
        (F ⋙ Q).rightDerivedFunctorUnit W (𝟙 _) K'
      simpa [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
        Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, hcomp, Category.assoc] using h
    have h₂ : (F ⋙ Q).rightDerivedFunctorUnit.app K' ≫
        (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K') =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K') ≫
        (P ⋙ G).rightDerivedFunctorUnit.app K' := by
      simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
    have h₃ : (P ⋙ G).rightDerivedFunctorUnit.app K' ≫
        eComp.hom.app (DerivedCategory.Qh.obj K') =
      G.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj K') ≫
        G.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.inv.app K') := by
      simp [eComp, β, Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app, hcomp']
    have hh : Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K') ≫
          d.hom.app (DerivedCategory.Qh.obj K') ≫
          G.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.hom.app K') =
        Q.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K') ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K') ≫
          G.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj K') := by
      apply (cancel_epi (Q.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj K'))).mp
      simp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
      simp
    dsimp only [K'] at hh
    rw [derivedFactorsh_objQ] at hh
    have hQ := derivedFactorsh_objQ Q ((F.mapHomologicalComplex (.up ℤ)).obj K)
    change Q.mapDerivedCategoryFactorsh.hom.app
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj K)) = _ at hQ
    rw [hQ] at hh
    have hτ : DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
          ((HomotopyCategory.quotient A (.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := rfl
    rw [hτ] at hh
    simp only [chainDerivedUnit_eq_unit]
    exact hh
  have he : ∀ (J : CochainComplex (A) ℤ) [J.IsKInjective]
      (I : CochainComplex (C) ℤ) [I.IsKInjective]
      (j : (P.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso j],
      d.inv.app (DerivedCategory.Q.obj J) ≫
          Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
          Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J) ≫
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) =
        G.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app J) ≫
          G.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫
          (G.rightDerivedFunctorObjQIso I).hom := by
    intro J hJ I hI j hj
    have hu := hd J
    rw [chainDerivedUnit_objQIso] at hu
    have hn : DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) ≫
        chainDerivedUnit G I =
      chainDerivedUnit G ((P.mapHomologicalComplex (.up ℤ)).obj J) ≫
        G.rightDerivedFunctor.map (DerivedCategory.Q.map j) := by
      have h := G.rightDerivedFunctorUnit.naturality
        ((HomotopyCategory.quotient _ (.up ℤ)).map j)
      simp only [chainDerivedUnit_eq_unit]
      exact h
    apply (cancel_epi (Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).inv ≫
      d.hom.app (DerivedCategory.Q.obj J))).mp
    apply (cancel_mono (G.rightDerivedFunctorObjQIso I).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id, Category.comp_id,
      ← Q.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id, Q.mapDerivedCategory.map_id,
      Category.id_comp]
    rw [← chainDerivedUnit_objQIso, hn, ← reassoc_of% hu]
  refine ⟨d.symm, he, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  change d'.hom.app M = d.inv.app M
  obtain ⟨J, hJ, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let := hJ
  have hj : d'.hom.app (DerivedCategory.Q.obj J) = d.inv.app (DerivedCategory.Q.obj J) := by
    obtain ⟨I, hI, j, _, hji⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((P.mapHomologicalComplex (.up ℤ)).obj J)
    let := hI
    let := hji
    have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) :=
      hacyclic J I j
    have h := (hd' J I j).trans (he J I j).symm
    exact (cancel_mono
      (Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j))).mp h
  apply (cancel_mono ((F.rightDerivedFunctor ⋙ Q.mapDerivedCategory).map i.hom)).mp
  rw [← d'.hom.naturality, ← d.inv.naturality, hj]

set_option backward.isDefEq.respectTransparency false in
/-- Derived coefficient restriction comparison, normalized on K-injective resolutions.
Source: Stacks Tags 0D6E and 0D6J (blueprint: prose-03-02).
Proof: exact restriction descends termwise. Apply canonical ringed-topos composition
to the two factorizations of the same morphism of ringed topoi. The equality of the
structural maps follows from the finite-coordinate normalization above. Resolve a
finite-coefficient K-injective complex after restriction, and compare both total
right-derived units with the identity-on-sections square. Composition gives the
stated equation. It uniquely determines the isomorphism on K-injective representatives,
hence on every derived object and every roof, without assuming restriction preserves
K-injectives. -/
theorem sfDerivedRestrictionComparison_existsUnique (n : ℕ) :
    ∃! e : scalarReductionDerivedRestriction.{u, u} l E X n ⋙
          sfCompletedDerivedDirectImage l E f ≅
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          scalarReductionDerivedRestriction.{u, u} l E Y n,
      ∀ (J : CochainComplex (scalarReductionTarget.{u, u} l E X n) ℤ) [J.IsKInjective]
        (I : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ) [I.IsKInjective]
        (j : ((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex (.up ℤ)).obj
          J ⟶ I) [QuasiIso j],
        e.hom.app (DerivedCategory.Q.obj J) ≫
            (scalarReductionDerivedRestriction.{u, u} l E Y n).map
              ((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).rightDerivedFunctorObjQIso J).hom ≫
            (scalarReductionRestriction.{u, u} l E Y n).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantModuleDirectImage f
                (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
                  (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (sfDirectImageRestrictionComparison l E f n) (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map
              (((sfCompletedModuleDirectImage l E f).mapHomologicalComplex (.up ℤ)).map
                (X := ((scalarReductionRestriction.{u, u} l E X n).mapHomologicalComplex
                  (.up ℤ)).obj J) (Y := I) j) =
          (sfCompletedDerivedDirectImage l E f).map
              ((scalarReductionRestriction.{u, u} l E X n).mapDerivedCategoryFactors.hom.app J) ≫
            (sfCompletedDerivedDirectImage l E f).map (DerivedCategory.Q.map j) ≫
            ((sfCompletedModuleDirectImage l E f).rightDerivedFunctorObjQIso I).hom := by
  have : Abelian.HasKInjectiveResolutions (scalarReductionTarget.{u, u} l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X (integralCoefficientCommRingSheaf l E X n)
  have := sfRestrictionLimits l E X n
  have := sfRestrictionColimits l E X n
  have := sfRestrictionLimits l E Y n
  have := sfRestrictionColimits l E Y n
  have h := derivedRestrictionSquare_existsUnique
    (proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (scalarReductionRestriction.{u, u} l E X n)
    (scalarReductionRestriction.{u, u} l E Y n) (sfCompletedModuleDirectImage l E f)
    (sfDirectImageRestrictionComparison l E f n)
    (fun J _ I _ j _ ↦ by
      have hq := ringModuleDirectImage_quasiIso f
        (completedIntegralCommRingSheafUnrestricted l E X)
        (integralCoefficientCommRingSheaf l E X n)
        (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingProjectionUnrestricted l E X n)
        (sfCompletedCoefficientMap l E f) J I j
      exact hq)
  exact h

/-- The canonical derived comparison selected by its resolution characterization.
Source: Stacks Tag 0D6E (blueprint: prose-03-02). -/
noncomputable def sfDerivedRestrictionComparison (n : ℕ) :=
  (sfDerivedRestrictionComparison_existsUnique l E f n).exists.choose

/-- The finite derived image of the derived reduction of K at exponent n+1.
Source: blueprint order 1468 (blueprint: prose-03-02). -/
noncomputable abbrev sfFiniteDerivedDirectImage
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1))).obj
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)

/-- The restricted finite-image term in the integral tower.
Source: blueprint order 1468 (blueprint: prose-03-02). -/
noncomputable abbrev sfDirectImageTerm
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (scalarReductionDerivedRestriction.{u, u} l E Y n).obj (sfFiniteDerivedDirectImage l E f K n)

/-- The coefficient transition, transported through the canonical restriction square.
Source: blueprint order 1468 (blueprint: prose-03-02). -/
noncomputable def sfDirectImageTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    sfDirectImageTerm l E f K (n + 1) ⟶ sfDirectImageTerm l E f K n :=
  (sfDerivedRestrictionComparison l E f (n + 1)).inv.app
      ((scalarReductionDerivedExtension.{u, u} l E X (n + 1)).obj K) ≫
    (sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionTransition l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)

/-- The integral direct image is a derived limit with its specified Roos projection.
Its objects are exactly the chosen derived limits of the finite-image tower; its
projection supplies the canonical finite-reduction comparison.
Source: blueprint order 1468; Bhatt--Scholze, Section 6.5
(blueprint: prose-03-02). -/
structure SfIntegralDirectImage
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    [HasProduct (sfDirectImageTerm l E f K)] where
  obj : DerivedCategory (scalarReductionSource.{u, u} l E Y)
  projection : obj ⟶ ∏ᶜ (sfDirectImageTerm l E f K)
  boundary : (∏ᶜ (sfDirectImageTerm l E f K)) ⟶ obj⟦(1 : ℤ)⟧
  roos : IsDerivedLimitTriangle (sfDirectImageTransition l E f K) obj projection boundary

/-- The actual finite-reduction comparison: the scalar-extension adjunct of the
n-th projection of the specified Roos triangle.
Source: blueprint order 1468; Stacks Tag 07A6
(blueprint: prose-03-02). -/
noncomputable def sfDirectImageReductionComparison
    {K : DerivedCategory (scalarReductionSource.{u, u} l E X)}
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E Y n).obj L.obj ⟶
      sfFiniteDerivedDirectImage l E f K n :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose.homEquiv
    L.obj (sfFiniteDerivedDirectImage l E f K n)).symm
      (L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n)

end WeilConjectures
