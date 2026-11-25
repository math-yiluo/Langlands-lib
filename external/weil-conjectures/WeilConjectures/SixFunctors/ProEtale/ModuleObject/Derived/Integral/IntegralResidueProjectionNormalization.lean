/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorSquare

/-! # Projection normalization of integral residue comparisons

Source: Bhatt--Scholze, Lemma 6.5.9(3), and Remark 6.8.15.
-/

set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars

@[expose] public section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'}
  {T : C ⥤ C'} {U : D ⥤ D'} {S : C' ⥤ C} {V : D' ⥤ D}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem doubleMate
    (a : F ⊣ G) (a' : F' ⊣ G') (b : T ⊣ S) (b' : U ⊣ V)
    (p : F ⋙ T ≅ U ⋙ F') (q : V ⋙ F ⟶ F' ⋙ S)
    (hq : ∀ N : D', T.map (q.app N) ≫ b.counit.app (F'.obj N) =
      p.hom.app (V.obj N) ≫ F'.map (b'.counit.app N))
    (J : C') :
    F.map ((((b'.comp a').rightAdjointUniq ((a.comp b).ofNatIsoLeft p)).hom.app J)) ≫
      a.counit.app (S.obj J) =
    q.app (G'.obj J) ≫ S.map (a'.counit.app J) := by
  let r := ((b'.comp a').rightAdjointUniq ((a.comp b).ofNatIsoLeft p)).hom
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [b.counit.naturality]
  rw [reassoc_of% (hq (G'.obj J))]
  have hr := (b'.comp a').rightAdjointUniq_hom_app_counit
    ((a.comp b).ofNatIsoLeft p) J
  dsimp only [Adjunction.ofNatIsoLeft_counit, Functor.whiskerLeft_app,
    NatTrans.comp_app, Adjunction.comp_counit_app, Functor.comp_map,
    Functor.comp_obj] at hr
  have hr' := congrArg (fun z ↦ p.hom.app ((G' ⋙ V).obj J) ≫ z) hr
  erw [← p.hom.naturality_assoc] at hr'
  simpa [Category.assoc] using hr'

end CategoryTheory

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'}
  {T : C ⥤ C'} {U : D ⥤ D'} {S : C' ⥤ C} {V : D' ⥤ D}

private theorem normalization
    (a : F ⊣ G) (a' : F' ⊣ G') [F.Monoidal]
    (p : U ⋙ F' ≅ F ⋙ T)
    (r : G' ⋙ V ⟶ S ⋙ G) (q : V ⋙ F ⟶ F' ⋙ S)
    (hr : ∀ J : C', F.map (r.app J) ≫ a.counit.app (S.obj J) =
      q.app (G'.obj J) ≫ S.map (a'.counit.app J))
    (BY : D) (tY : U ⋙ V ≅ tensorRight BY)
    (tX : T ⋙ S ≅ tensorRight (F.obj BY))
    (ht : ∀ M : D, F.map (tY.hom.app M) ≫ Functor.OplaxMonoidal.δ F M BY =
      q.app (U.obj M) ≫ S.map (p.hom.app M) ≫ tX.hom.app (F.obj M))
    (K : C) :
    V.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ p.hom)).app K) ≫
        r.app (T.obj K) ≫ G.map (tX.hom.app K) =
      tY.hom.app (G.obj K) ≫
        ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app K).app BY := by
  let push := (mateEquiv a a' (TwoSquare.mk _ _ _ _ p.hom))
  have hc := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ p.hom) K
  change F'.map (push.app K) ≫ a'.counit.app (T.obj K) =
    p.hom.app (G.obj K) ≫ T.map (a.counit.app K) at hc
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := a.counit.naturality (tX.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, ← Category.assoc (F.map (r.app _))]
  erw [hr]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (V.map (push.app K)))]
  erw [q.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← S.map_comp_assoc, hc, S.map_comp, Category.assoc]
  erw [tX.hom.naturality]
  dsimp only [tensorRight]
  erw [← reassoc_of% (ht (G.obj K))]
  congr 1
  exact (a.map_rightAdjointProjectionMap_app_app_comp_counit
    (Functor.OplaxMonoidal.δNatTrans F) K BY).symm

private theorem normalization_family
    (a : F ⊣ G) (a' : F' ⊣ G') (b : T ⊣ S) (b' : U ⊣ V)
    (p : F ⋙ T ≅ U ⋙ F') (q : V ⋙ F ⟶ F' ⋙ S)
    (hq : ∀ N : D', T.map (q.app N) ≫ b.counit.app (F'.obj N) =
      p.hom.app (V.obj N) ≫ F'.map (b'.counit.app N)) (BY : D)
    (h : ∃ m : F.Monoidal, letI := m
      ∃ (tY : U ⋙ V ≅ tensorRight BY) (tX : T ⋙ S ≅ tensorRight (F.obj BY)),
        ∀ M : D, F.map (tY.hom.app M) ≫ Functor.OplaxMonoidal.δ F M BY =
          q.app (U.obj M) ≫ S.map (p.inv.app M) ≫ tX.hom.app (F.obj M)) :
    ∃ m : F.Monoidal, letI := m
      ∀ K : C,
        ∃ (s : V.obj (U.obj (G.obj K)) ≅ G.obj K ⊗ BY)
          (e : S.obj (T.obj K) ≅ K ⊗ F.obj BY),
          V.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ p.inv)).app K) ≫
              (((b'.comp a').rightAdjointUniq
                ((a.comp b).ofNatIsoLeft p)).hom.app (T.obj K)) ≫ G.map e.hom =
            s.hom ≫
              ((a.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app K).app
                BY := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  let := m
  obtain ⟨tY, tX, ht⟩ := hm
  intro K
  refine ⟨tY.app _, tX.app K, ?_⟩
  exact normalization a a' p.symm _ q
    (doubleMate a a' b b' p q hq) BY tY tX ht K

end CategoryTheory

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueProjectionNormalization
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local instance 2000] residueExchangeIntegralDerivedMonoidal

/-- Coherent pull comparisons identify the restricted push mate with the projection map.

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15, and associativity of derived tensor.
(blueprint: new-integral-residue-projection-normalization)

Proof. The inverse image on sheaves preserves the coequalizers of balanced tensor pairs.
Its strong monoidal comparison therefore induces the relative tensor comparison on
module objects, and the coefficient-pullback isomorphism identifies their base rings.
The unit and associativity diagrams follow after precomposing with the epimorphisms
from the balanced tensor presentations. Pullback preserves flat modules and colimits;
apply the functorial flat resolutions to obtain resolutions with K-flat pullback.
The derived tensor comparison of these resolutions is invertible, and its unit and
associativity diagrams follow by uniqueness of derived comparisons. This gives m.

Resolve the input of scalar extension by K-flat modules. Associativity of relative tensor
and the coefficient-pullback isomorphism give the pull comparison. The associativity
pentagon and the coefficient-map composition equations give its composition law with
leftDerivedUpperStarComp, so the comparisons form c. The canonical balanced tensor
counit is a left-derived presentation. Uniqueness of left derivation and symmetry
identify restricted reduction with right tensor by the residue regular module.
This gives s. Derived scalar
extension is left adjoint to exact scalar restriction. Thus the two composite functors
in c.pull are left adjoints, and conjugating c.pull gives an isomorphism of their right
adjoints, Rf_* followed by restriction and restriction followed by Rf_*. Evaluate it at
reduction of K. Combine it with the tensor identification on X and the coefficient
pullback isomorphism f^* A_Y ≅ A_X to obtain e on X. The target identification is the
composite of c.restrictPushIso at reduction of K with Rf_* applied to e. To identify the
morphism, transpose under the integral pull-push adjunction. The counit identity for
c.push, tensor associativity, and the coefficient-pullback isomorphism reduce both
sides to the oplax tensor comparison followed by the counit tensored with the identity.
This is the defining transpose of rightAdjointProjectionMap. No dualizability or
invertibility of the projection map is used. Empty schemes and zero complexes are
included: all comparisons remain the canonical ones. -/
theorem integralResidue_projection_normalization
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ c : IntegralResiduePullComparisons.{u} ℓ E,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        ∃ m : (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal,
          letI := m
          ∀ K : residueExchangeDerived (integralCoeff ℓ E) X,
            ∃ (s :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E Y).obj
                      ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K)) ≅
                  (residueExchangeLowerStar (integralCoeff ℓ E) f).obj K ⊗
                    residueExchangeCoefficient ℓ E Y)
              (e :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E X).obj K) ≅
                  K ⊗ (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
                    (residueExchangeCoefficient ℓ E Y)),
              (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.map
                  ((c.push f).app K) ≫
                (c.restrictPushIso f).hom.app ((residueExchangeReduction ℓ E X).obj K) ≫
                (residueExchangeLowerStar (integralCoeff ℓ E) f).map e.hom =
                s.hom ≫
                  (((residueExchangeAdjunction (integralCoeff ℓ E) f).rightAdjointProjectionMap
                    (Functor.OplaxMonoidal.δNatTrans
                      (residueExchangeUpperStar (integralCoeff ℓ E) f))).app K).app
                    (residueExchangeCoefficient ℓ E Y) := by
  have _hTensor := hTensor
  let c := residueExchangePullComparisons.{u} ℓ E
  refine ⟨c, ?_⟩
  intro X Y f
  unfold IntegralResiduePullComparisons.push IntegralResiduePullComparisons.restrictPushIso
  exact CategoryTheory.normalization_family (residueExchangeAdjunction (integralCoeff ℓ E) f)
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
      (residueExchangeReductionAdjunction ℓ E X)
      (residueExchangeReductionAdjunction ℓ E Y) (c.pull f)
      (residueExchangeRestrictPullIso ℓ E f).hom
      (residueExchangePullComparisons_counit ℓ E f)
      (residueExchangeCoefficient ℓ E Y)
      (integralResidue_tensorSquare ℓ E f)

end AlgebraicGeometry.ProEtale.CondensedRing
