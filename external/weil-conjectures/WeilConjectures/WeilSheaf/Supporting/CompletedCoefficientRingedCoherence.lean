/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Composition and slice localization of completed coefficient ring maps

Source: Stacks Project, Tag 04J0; Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-tw-completed-coefficient-ringed-coherence).

The small pro-etale site keeps object universe t+1 and morphism universe t.
Coefficient values live in max u (t+1); the two input universes are independent.
Index n denotes the positive exponent n+1. All coefficient maps are fixed by
projections, and all geometric comparisons by their adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The recorded Kan-extension/sheafification inverse image at the coefficient size.
Source: Stacks 00VC, 09A5 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingPull {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  letI : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange f)
    CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)

/-- Its specified Kan-extension/sheafification adjunction.
Source: Stacks 00VC, 09A5 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingAdj {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  letI : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (proEtaleBaseChange f)
    CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)

/-- Constant-section structural map, using the recorded constant-section adjunct.
Source: Stacks 0H7J (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingConstantMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) :
    (completedRingPull.{t, u} f).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ⟶
      (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A :=
  ((completedRingAdj.{t, u} f).homEquiv _ _).symm
    (coefficientProEtaleDirectRingMap.{t, u} f A)

private instance completedWeakSheafify (W : Scheme.{t}) :
    (sheafToPresheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).IsRightAdjoint :=
  (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint

private theorem completedDirect_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) (H : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app H ≫
        (coefficientProEtaleDirectRingMap f A).hom.app H =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange f).op.obj H) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj A)
      (((proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).obj
          ((constantSheaf (ProEt.topology X) _).obj A))).apply_symm_apply
            (Functor.whiskerLeft (proEtaleBaseChange f).op
              (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun a ↦ a.app H) h

private theorem completedConstant_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (completedRingPull.{t, u} f).map
        ((constantSheaf (ProEt.topology Y) _).map a) ≫ completedRingConstantMap f B =
      completedRingConstantMap f A ≫ (constantSheaf (ProEt.topology X) _).map a := by
  apply ((completedRingAdj.{t, u} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [completedRingConstantMap, Equiv.apply_symm_apply]
  apply ((sheafificationAdjunction (ProEt.topology Y) _).homEquiv _ _).injective
  apply NatTrans.ext
  funext H
  change _ ≫ _ ≫ _ = _ ≫ _ ≫ _
  rw [← Category.assoc, ← Category.assoc]
  have h := congrArg (fun a ↦ a.app H)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at h
  erw [← h, Category.assoc, completedDirect_unit, completedDirect_unit]
  exact congrArg (fun a ↦ a.app ((proEtaleBaseChange f).op.obj H))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

attribute [-instance] completedWeakSheafify

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The projection equations determine exactly one structural ring map.
Source: Stacks 03CO, 04J0; Bhatt--Scholze 6.6.11
(blueprint: lem-tw-completed-coefficient-ringed-coherence).
Proof: the constant-section adjuncts commute with reductions, since their two
extensions agree on every constant. Compose the pulled-back projections with
these maps to obtain a cone in the target site. The sectionwise limit universal
property supplies the map and proves its uniqueness. No infinite-limit
preservation by inverse image is used. -/
theorem completedRingMap_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! c : (completedRingPull.{t, u} f).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
          completedIntegralCommRingSheafUnrestricted l E X,
      ∀ n : ℕ, c ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
        (completedRingPull.{t, u} f).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
            completedRingConstantMap f
              (CommRingCat.of (ULift.{t + 1}
                (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let F := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let d (n : ℕ) := (completedRingPull.{t, u} f).map
    (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
      completedRingConstantMap f
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let c : Cone (integralCoefficientSheafSystem l E X) :=
    { pt := F.obj ((completedRingPull.{t, u} f).obj
        (completedIntegralCommRingSheafUnrestricted l E Y))
      π := NatTrans.ofOpSequence (fun n ↦ F.map (d n)) (by
        intro n
        simp only [Functor.const_obj_map, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        change F.map (d n) = F.map (d (n + 1)) ≫ _
        change _ = F.map (d (n + 1)) ≫ F.map
          ((constantSheaf (ProEt.topology X) _).map _)
        rw [← F.map_comp]
        congr 1
        dsimp only [d]
        rw [Category.assoc, ← completedConstant_naturality, ← Category.assoc,
          ← Functor.map_comp]
        congr 2
        apply (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map_injective
        change limit.π (integralCoefficientSheafSystem l E Y) (op n) =
          limit.π _ (op (n + 1)) ≫ integralCoefficientSheafTransition l E Y n
        simpa only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (limit.w (integralCoefficientSheafSystem l E Y)
            (homOfLE (Nat.le_succ n)).op).symm) }
  let m : (completedRingPull.{t, u} f).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X := F.preimage (limit.lift _ c)
  have hm (n : ℕ) : m ≫ completedIntegralCommRingProjectionUnrestricted l E X n = d n := by
    apply F.map_injective
    change F.map m ≫ limit.π _ (op n) = _
    simp only [m, Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨m, hm, ?_⟩
  intro m' hm'
  apply F.map_injective
  apply limit.hom_ext
  intro n
  change F.map m' ≫ limit.π _ n = F.map m ≫ limit.π _ n
  change F.map m' ≫ F.map (completedIntegralCommRingProjectionUnrestricted l E X n.unop) =
    F.map m ≫ F.map (completedIntegralCommRingProjectionUnrestricted l E X n.unop)
  rw [← F.map_comp, ← F.map_comp, hm', hm]

/-- The unique projection-defined completed coefficient map, with no extra choices.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (completedRingPull.{t, u} f).obj (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
      completedIntegralCommRingSheafUnrestricted l E X :=
  (completedRingMap_existsUnique l E f).exists.choose

/-- The geometric inverse-image compositor, the mate of fibre-product associativity.
Source: Stacks 09A5 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingComp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    completedRingPull.{t, u} (f ≫ g) ≅
      completedRingPull.{t, u} g ⋙ completedRingPull.{t, u} f :=
  ((conjugateIsoEquiv (completedRingAdj.{t, u} (f ≫ g))
    ((completedRingAdj.{t, u} g).comp (completedRingAdj.{t, u} f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
          CommRingCat.{max u (t + 1)}
          (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

private theorem completedMap_projection {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    completedRingMap l E f ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
      (completedRingPull.{t, u} f).map
        (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
          completedRingConstantMap f
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  (completedRingMap_existsUnique l E f).exists.choose_spec n

private theorem completedMap_ext {X : Scheme.{t}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}}
    {a b : S ⟶ completedIntegralCommRingSheafUnrestricted l E X}
    (h : ∀ n, a ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
      b ≫ completedIntegralCommRingProjectionUnrestricted l E X n) : a = b := by
  let F := sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)
  apply F.map_injective
  apply limit.hom_ext
  intro n
  exact congrArg F.map (h n.unop)

private def completedDirectComp {T W Z : Scheme.{t}} (h : T ⟶ W) (k : W ⟶ Z) :=
  Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).symm
      CommRingCat.{max u (t + 1)} (ProEt.topology Z) (ProEt.topology W) (ProEt.topology T)

private theorem completedDirect_comp {T W Z : Scheme.{t}} (h : T ⟶ W) (k : W ⟶ Z)
    (A : CommRingCat.{max u (t + 1)}) :
    coefficientProEtaleDirectRingMap k A ≫
      ((proEtaleBaseChange k).sheafPushforwardContinuous _ _ _).map
        (coefficientProEtaleDirectRingMap h A) ≫
          (completedDirectComp.{t, u} h k).hom.app
            ((constantSheaf (ProEt.topology T) _).obj A) =
      coefficientProEtaleDirectRingMap (h ≫ k) A := by
  apply ((sheafificationAdjunction (ProEt.topology Z) _).homEquiv _ _).injective
  apply NatTrans.ext
  funext H
  change _ ≫ _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc, ← Category.assoc, completedDirect_unit]
  change ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange k).op.obj H) ≫
      (coefficientProEtaleDirectRingMap h A).hom.app
        ((proEtaleBaseChange k).op.obj H)) ≫
      ((constantSheaf (ProEt.topology T) _).obj A).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app
          H.unop).op = _
  erw [completedDirect_unit, completedDirect_unit]
  have hn := (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj A)).naturality
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app
      H.unop).op
  change 𝟙 _ ≫ _ = _ at hn
  exact hn.symm.trans (Category.id_comp _)

/-- Slice restriction under the recorded equivalence Over U ≌ ProEt U.left.
It is exactly sectionwise restriction, in the coefficient universe.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingRestriction {W : Scheme.{t}} (U : W.ProEt) :
    Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
  letI : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology W) :=
    ProEt.isContinuous_overMap U.prop
  (MorphismProperty.Over.map ⊤ U.prop).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (ProEt.topology U.left) (ProEt.topology W)

/-- The base-changed object's morphism to the original object.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingSliceArrow {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    ((proEtaleBaseChange g).obj U).left ⟶ U.left :=
  pullback.fst U.hom g

/-- The actual geometric identification H ×_U (U ×_W T) ≅ H ×_W T over T.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingSlicePointIso {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt)
    (H : U.left.ProEt) :
    (MorphismProperty.Over.map ⊤ ((proEtaleBaseChange g).obj U).prop).obj
        ((proEtaleBaseChange (completedRingSliceArrow g U)).obj H) ≅
      (proEtaleBaseChange g).obj ((MorphismProperty.Over.map ⊤ U.prop).obj H) :=
  MorphismProperty.Over.isoMk (pullbackRightPullbackFstIso U.hom g H.hom) (by
    change (pullbackRightPullbackFstIso U.hom g H.hom).hom ≫
      pullback.snd (H.hom ≫ U.hom) g =
        pullback.snd H.hom (pullback.fst U.hom g) ≫ pullback.snd U.hom g
    exact pullbackRightPullbackFstIso_hom_snd U.hom g H.hom)

section SliceProof

set_option backward.defeqAttrib.useBackward true

private theorem completed_inverseMate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (β : R ⋙ G ⟶ H ⋙ R') (X : A) :
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β))).app X =
      L'.map (G.map (a.unit.app X)) ≫ L'.map (β.app (L.obj X)) ≫
        b.counit.app (H.obj (L.obj X)) := by
  simp [mateEquiv]

private theorem completed_inverseMate_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (β : R ⋙ G ⟶ H ⋙ R') {X : A} {Y : B} (f : L.obj X ⟶ Y) :
    b.homEquiv _ _
      ((((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β))).app X ≫ H.map f) =
      G.map (a.homEquiv _ _ f) ≫ β.app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ β) X
  dsimp only [Functor.id_obj] at hu
  rw [← hu, Category.assoc]
  change G.map (a.unit.app X) ≫ β.app (L.obj X) ≫ R'.map (H.map f) = _
  have hn := β.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← G.map_comp_assoc]
  rfl

private theorem completed_iteratedInverseMate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (α : TwoSquare U₂ R₂ R₁ U₁) [IsIso α] :
    IsIso (((mateEquiv a b).symm ((mateEquiv d c).symm α))) := by
  rw [iterated_mateEquiv_conjugateEquiv_symm]
  infer_instance

private abbrev completedRestrictFunctor {W : Scheme.{t}} (U : W.ProEt) :=
  MorphismProperty.Over.map ⊤ U.prop

private instance completedRestrictContinuous {W : Scheme.{t}} (U : W.ProEt) :
    (completedRestrictFunctor U).IsContinuous (ProEt.topology U.left) (ProEt.topology W) :=
  ProEt.isContinuous_overMap U.prop

private instance completedRestrictCocontinuous {W : Scheme.{t}} (U : W.ProEt) :
    (completedRestrictFunctor U).IsCocontinuous (ProEt.topology U.left) (ProEt.topology W) :=
  ProEt.isCocontinuous_overMap U.prop

private abbrev completedRestrict {W : Scheme.{t}} (U : W.ProEt) :=
  (completedRestrictFunctor U).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (ProEt.topology U.left) (ProEt.topology W)

private theorem completedRestriction_eq {W : Scheme.{t}} (U : W.ProEt) :
    completedRingRestriction.{t, u} U = completedRestrict.{t, u} U := rfl

section ConstantRestriction

variable {C D A : Type*} [Category C] [Category D] [Category A]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

private def completedConstantRestrictionIso (a : A) :
    (G.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj a) ≅
      (constantSheaf J A).obj a :=
  ((G.pushforwardContinuousSheafificationCompatibility A J K).app
    ((Functor.const Dᵒᵖ).obj a)).symm

private theorem completedConstantRestrictionIso_unit (a : A) (H : C) :
    (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op (G.obj H)) ≫
      (completedConstantRestrictionIso G J K a).hom.hom.app (op H) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj a)).app (op H) := by
  have h := congrArg (fun α ↦ α.app (op H))
    (G.toSheafify_pullbackSheafificationCompatibility A J K
      ((Functor.const Dᵒᵖ).obj a))
  change (toSheafify J ((Functor.const Cᵒᵖ).obj a)).app (op H) ≫
      (completedConstantRestrictionIso G J K a).inv.hom.app (op H) =
    (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op (G.obj H)) at h
  rw [← h, Category.assoc]
  have hi := congrArg (fun α ↦ α.hom.app (op H))
    (completedConstantRestrictionIso G J K a).inv_hom_id
  change (completedConstantRestrictionIso G J K a).inv.hom.app (op H) ≫
    (completedConstantRestrictionIso G J K a).hom.hom.app (op H) = 𝟙 _ at hi
  change _ ≫ ((completedConstantRestrictionIso G J K a).inv.hom.app (op H) ≫
    (completedConstantRestrictionIso G J K a).hom.hom.app (op H)) = _
  rw [hi, Category.comp_id]

private theorem completedConstantRestrictionIso_naturality {a b : A} (f : a ⟶ b) :
    (G.sheafPushforwardContinuous A J K).map ((constantSheaf K A).map f) ≫
      (completedConstantRestrictionIso G J K b).hom =
    (completedConstantRestrictionIso G J K a).hom ≫ (constantSheaf J A).map f := by
  exact (G.pushforwardContinuousSheafificationCompatibility A J K).inv.naturality
    ((Functor.const Dᵒᵖ).map f)

end ConstantRestriction

private def completedRestrictConstant {W : Scheme.{t}} (U : W.ProEt)
    (A : CommRingCat.{max u (t + 1)}) :
    (completedRestrict.{t, u} U).obj ((constantSheaf (ProEt.topology W) _).obj A) ≅
      (constantSheaf (ProEt.topology U.left) _).obj A := by
  let : HasWeakSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} U.left).isRightAdjoint
  let : HasLimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink _
  exact completedConstantRestrictionIso (A := CommRingCat.{max u (t + 1)})
    (completedRestrictFunctor U)
    (ProEt.topology U.left) (ProEt.topology W) A

private theorem completedRestrictConstant_unit {W : Scheme.{t}} (U : W.ProEt)
    (A : CommRingCat.{max u (t + 1)}) (H : U.left.ProEt) :
    (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
        (op ((completedRestrictFunctor U).obj H)) ≫
      (completedRestrictConstant.{t, u} U A).hom.hom.app (op H) =
    (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj A)).app
      (op H) := by
  let : HasWeakSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} U.left).isRightAdjoint
  let : HasLimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink _
  exact completedConstantRestrictionIso_unit (A := CommRingCat.{max u (t + 1)})
    (completedRestrictFunctor U)
    (ProEt.topology U.left) (ProEt.topology W) A H

private theorem completedRestrictConstant_naturality {W : Scheme.{t}} (U : W.ProEt)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (completedRestrict.{t, u} U).map ((constantSheaf (ProEt.topology W) _).map a) ≫
      (completedRestrictConstant.{t, u} U B).hom =
    (completedRestrictConstant.{t, u} U A).hom ≫
      (constantSheaf (ProEt.topology U.left) _).map a := by
  let : HasWeakSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} U.left).isRightAdjoint
  let : HasLimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink _
  exact completedConstantRestrictionIso_naturality (A := CommRingCat.{max u (t + 1)})
    (completedRestrictFunctor U)
    (ProEt.topology U.left) (ProEt.topology W) a

attribute [irreducible] completedRestrictConstant

private abbrev completedRestrictRings {W : Scheme.{t}} (U : W.ProEt) :=
  (completedRestrictFunctor U).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology U.left) (ProEt.topology W)

private instance completedRestrictRings_limits {W : Scheme.{t}} (U : W.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ (completedRestrictRings.{t, u} U) := by
  apply preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (ProEt.topology U.left) RingCat.{max u (t + 1)})

private def completedRestrictDiagram {W : Scheme.{t}} (U : W.ProEt) :
    integralCoefficientSheafSystem l E W ⋙ completedRestrictRings.{t, u} U ≅
      integralCoefficientSheafSystem l E U.left := by
  let F := sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let a : integralCoefficientSheafSystem l E W ⋙ completedRestrictRings.{t, u} U ⟶
      integralCoefficientSheafSystem l E U.left :=
    NatTrans.ofOpSequence
      (F := integralCoefficientSheafSystem l E W ⋙ completedRestrictRings.{t, u} U)
      (G := integralCoefficientSheafSystem l E U.left) (fun n ↦ F.map
      (completedRestrictConstant.{t, u} U (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom) (by
      intro n
      simp only [Functor.comp_map, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      have h := congrArg F.map (completedRestrictConstant_naturality.{t, u} U
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))
      simp only [Functor.map_comp] at h
      exact h)
  have : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    change IsIso (F.map (completedRestrictConstant.{t, u} U (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))).hom)
    infer_instance
  exact asIso a

private def completedRestrictCompletion {W : Scheme.{t}} (U : W.ProEt) :
    (completedRestrict.{t, u} U).obj
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
      completedIntegralCommRingSheafUnrestricted l E U.left := by
  let F := sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  exact F.preimageIso
    (preservesLimitIso (completedRestrictRings.{t, u} U)
      (integralCoefficientSheafSystem l E W) ≪≫
        HasLimit.isoOfNatIso (completedRestrictDiagram.{t, u} l E U))

private theorem completedRestrictCompletion_projection {W : Scheme.{t}} (U : W.ProEt)
    (n : ℕ) :
    (completedRestrictCompletion.{t, u} l E U).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E U.left n =
      (completedRestrict.{t, u} U).map
        (completedIntegralCommRingProjectionUnrestricted l E W n) ≫
          (completedRestrictConstant.{t, u} U (CommRingCat.of
            (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom := by
  let F := sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  apply F.map_injective
  change F.map (completedRestrictCompletion.{t, u} l E U).hom ≫ limit.π _ (op n) = _
  dsimp only [completedRestrictCompletion, Functor.preimageIso, Iso.trans_hom]
  rw [Functor.map_preimage, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    preservesLimitIso_hom_π_assoc]
  rfl

attribute [irreducible] completedRestrictCompletion

private instance completedObjectBaseContinuous {W : Scheme.{t}} (U : W.ProEt) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology W) (ProEt.topology U.left) :=
  ProEt.isContinuous_overPullback U.hom

private abbrev completedObjectPush {W : Scheme.{t}} (U : W.ProEt) :=
  letI : (proEtaleBaseChange U.hom).IsContinuous
      (ProEt.topology W) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  (proEtaleBaseChange U.hom).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (ProEt.topology W) (ProEt.topology U.left)

private def completedRestrictionAdj {W : Scheme.{t}} (U : W.ProEt) :
    completedRestrict.{t, u} U ⊣
      completedObjectPush.{t, u} U :=
  Adjunction.sheafPushforwardContinuous (E := CommRingCat.{max u (t + 1)})
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial)
    (ProEt.topology U.left) (ProEt.topology W)

private def completedSliceRightIso {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    proEtaleBaseChange U.hom ⋙ proEtaleBaseChange (completedRingSliceArrow g U) ≅
      proEtaleBaseChange g ⋙ proEtaleBaseChange ((proEtaleBaseChange g).obj U).hom :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (completedRingSliceArrow g U) U.hom).symm ≪≫
  MorphismProperty.Over.pullbackCongr (pullback.condition (f := U.hom) (g := g)) ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    ((proEtaleBaseChange g).obj U).hom g

private def completedSliceGamma {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    completedObjectPush.{t, u} ((proEtaleBaseChange g).obj U) ⋙
      (proEtaleBaseChange g).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (ProEt.topology W) (ProEt.topology T) ≅
    (proEtaleBaseChange (completedRingSliceArrow g U)).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (ProEt.topology U.left)
          (ProEt.topology ((proEtaleBaseChange g).obj U).left) ⋙
      completedObjectPush.{t, u} U :=
  letI : (proEtaleBaseChange U.hom).IsContinuous
      (ProEt.topology W) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  letI : (proEtaleBaseChange ((proEtaleBaseChange g).obj U).hom).IsContinuous
      (ProEt.topology T) (ProEt.topology ((proEtaleBaseChange g).obj U).left) :=
    ProEt.isContinuous_overPullback ((proEtaleBaseChange g).obj U).hom
  letI : (proEtaleBaseChange (completedRingSliceArrow g U)).IsContinuous
      (ProEt.topology U.left) (ProEt.topology ((proEtaleBaseChange g).obj U).left) :=
    ProEt.isContinuous_overPullback (completedRingSliceArrow g U)
  letI := Functor.isContinuous_comp (proEtaleBaseChange g)
    (proEtaleBaseChange ((proEtaleBaseChange g).obj U).hom)
    (ProEt.topology W) (ProEt.topology T)
    (ProEt.topology ((proEtaleBaseChange g).obj U).left)
  letI := Functor.isContinuous_comp (proEtaleBaseChange U.hom)
    (proEtaleBaseChange (completedRingSliceArrow g U))
    (ProEt.topology W) (ProEt.topology U.left)
    (ProEt.topology ((proEtaleBaseChange g).obj U).left)
  Functor.sheafPushforwardContinuousComp _ _ CommRingCat.{max u (t + 1)}
    (ProEt.topology W) (ProEt.topology T)
      (ProEt.topology ((proEtaleBaseChange g).obj U).left) ≪≫
  Functor.sheafPushforwardContinuousIso (completedSliceRightIso g U).symm
    CommRingCat.{max u (t + 1)} (ProEt.topology W)
      (ProEt.topology ((proEtaleBaseChange g).obj U).left) ≪≫
  (Functor.sheafPushforwardContinuousComp _ _ CommRingCat.{max u (t + 1)}
    (ProEt.topology W) (ProEt.topology U.left)
      (ProEt.topology ((proEtaleBaseChange g).obj U).left)).symm

private def completedSliceBeta {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :=
  ((mateEquiv (completedRestrictionAdj.{t, u} ((proEtaleBaseChange g).obj U))
    (completedRestrictionAdj.{t, u} U)).symm
      (TwoSquare.mk _ _ _ _ (completedSliceGamma.{t, u} g U).hom))

private def completedSliceLambda {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :=
  ((mateEquiv (completedRingAdj.{t, u} g)
    (completedRingAdj.{t, u} (completedRingSliceArrow g U))).symm
      (TwoSquare.mk _ _ _ _ (completedSliceBeta.{t, u} g U)))

private theorem completedProEt_comp_left {W : Scheme.{t}} {A B C : W.ProEt}
    (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).left = f.left ≫ g.left := rfl

private theorem completedSliceBeta_app {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt)
    (F : Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}) (H : U.left.ProEt) :
    ((completedSliceBeta.{t, u} g U).app F).hom.app (op H) =
      F.obj.map (completedRingSlicePointIso g U H).hom.op := by
  dsimp only [completedSliceBeta]
  rw [completed_inverseMate_app]
  change F.obj.map _ ≫ (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id]
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [unop_comp, completedProEt_comp_left]
  apply pullback.hom_ext <;>
    simp [completedSliceRightIso, completedRingSlicePointIso,
      completedRestrictFunctor, MorphismProperty.Over.mapPullbackAdj,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
      proEtaleBaseChange, completedRingSliceArrow, completedProEt_comp_left]

private instance completedSliceBeta_isIso {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) : IsIso (completedSliceBeta.{t, u} g U) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _),
    NatTrans.isIso_iff_isIso_app]
  intro H
  change IsIso (((completedSliceBeta.{t, u} g U).app F).hom.app H)
  rw [completedSliceBeta_app g U F H.unop]
  infer_instance

attribute [irreducible] completedRestrictionAdj completedSliceGamma

private instance completedSliceLambda_isIso {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) : IsIso (completedSliceLambda.{t, u} g U) := by
  exact completed_iteratedInverseMate_isIso (completedRingAdj.{t, u} g)
    (completedRingAdj.{t, u} (completedRingSliceArrow g U))
    (completedRestrictionAdj.{t, u} U)
    (completedRestrictionAdj.{t, u} ((proEtaleBaseChange g).obj U))
    (TwoSquare.mk _ _ _ _ (completedSliceGamma.{t, u} g U).hom)

private theorem completedSliceLambda_app {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt)
    (F : Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}) :
    (completedSliceLambda.{t, u} g U).app F =
      (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
        ((completedRestrict.{t, u} U).map ((completedRingAdj.{t, u} g).unit.app F)) ≫
      (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
        ((completedSliceBeta.{t, u} g U).app ((completedRingPull.{t, u} g).obj F)) ≫
      (completedRingAdj.{t, u} (completedRingSliceArrow g U)).counit.app
        ((completedRestrict.{t, u} ((proEtaleBaseChange g).obj U)).obj
          ((completedRingPull.{t, u} g).obj F)) := by
  exact completed_inverseMate_app _ _ _ F

private theorem completedSliceLambda_adjunct {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) {R : Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}}
    {S : Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}}
    (a : (completedRingPull.{t, u} g).obj R ⟶ S) :
    (completedRingAdj.{t, u} (completedRingSliceArrow g U)).homEquiv _ _
      ((completedSliceLambda.{t, u} g U).app R ≫
        (completedRestrict.{t, u} ((proEtaleBaseChange g).obj U)).map a) =
      (completedRestrict.{t, u} U).map ((completedRingAdj.{t, u} g).homEquiv _ _ a) ≫
        (completedSliceBeta.{t, u} g U).app S := by
  exact completed_inverseMate_adjunct _ _ _ a

attribute [irreducible] completedSliceBeta completedSliceLambda

section ConstantCompatibility

attribute [local implicit_reducible] MorphismProperty

private theorem completedSliceConstant {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt)
    (A : CommRingCat.{max u (t + 1)}) :
    (completedSliceLambda.{t, u} g U).app ((constantSheaf (ProEt.topology W) _).obj A) ≫
        (completedRestrict.{t, u} ((proEtaleBaseChange g).obj U)).map
          (completedRingConstantMap g A) ≫
        (completedRestrictConstant.{t, u} ((proEtaleBaseChange g).obj U) A).hom =
      (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
        (completedRestrictConstant.{t, u} U A).hom ≫
          completedRingConstantMap (completedRingSliceArrow g U) A := by
  apply ((completedRingAdj.{t, u} (completedRingSliceArrow g U)).homEquiv _ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    completedSliceLambda_adjunct, Adjunction.homEquiv_naturality_left]
  simp only [completedRingConstantMap, Equiv.apply_symm_apply]
  apply (cancel_epi (completedRestrictConstant.{t, u} U A).inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology U.left) _ _
    (by exact ObjectProperty.FullSubcategory.property _)
  apply NatTrans.ext
  funext H
  obtain ⟨H⟩ := H
  change
    (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj A)).app (op H) ≫
      (completedRestrictConstant.{t, u} U A).inv.hom.app (op H) ≫
      (coefficientProEtaleDirectRingMap g A).hom.app
        (op ((completedRestrictFunctor U).obj H)) ≫
      ((completedSliceBeta.{t, u} g U).app
        ((constantSheaf (ProEt.topology T) _).obj A)).hom.app (op H) ≫
      (completedRestrictConstant.{t, u} ((proEtaleBaseChange g).obj U) A).hom.hom.app
        ((proEtaleBaseChange (completedRingSliceArrow g U)).op.obj (op H)) =
    (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj A)).app (op H) ≫
      (coefficientProEtaleDirectRingMap (completedRingSliceArrow g U) A).hom.app (op H)
  have hu := completedRestrictConstant_unit.{t, u} U A H
  have hui :
      (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj A)).app (op H) ≫
        (completedRestrictConstant.{t, u} U A).inv.hom.app (op H) =
      (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app
        (op ((completedRestrictFunctor U).obj H)) := by
    rw [← hu, Category.assoc]
    have hi := congrArg (fun a ↦ a.hom.app (op H)) (completedRestrictConstant.{t, u} U A).hom_inv_id
    change (completedRestrictConstant.{t, u} U A).hom.hom.app (op H) ≫
      (completedRestrictConstant.{t, u} U A).inv.hom.app (op H) = 𝟙 _ at hi
    rw [hi]
    exact Category.comp_id _
  rw [← Category.assoc, hui, ← Category.assoc, completedDirect_unit,
    completedSliceBeta_app]
  have hn := (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj A)).naturality
    (completedRingSlicePointIso g U H).hom.op
  change 𝟙 _ ≫ _ = _ at hn
  simp only [Category.id_comp] at hn
  erw [← Category.assoc, ← hn, completedRestrictConstant_unit.{t, u},
    completedDirect_unit]
  rfl

end ConstantCompatibility

private theorem completedProjectionGlue
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ B) (M : C ⥤ D) (P : A ⥤ C) (Q : B ⥤ D)
    (α : P ⋙ M ⟶ L ⋙ Q) {X X' : A} {Y Y' : B} {Z Z' : C} {V V' : D}
    (p : X ⟶ X') (q : Y ⟶ Y') (c : L.obj X ⟶ Y) (d : L.obj X' ⟶ Y')
    (eU : P.obj X ⟶ Z) (eV : Q.obj Y ⟶ V) (pU : Z ⟶ Z') (pV : V ⟶ V')
    (aU : P.obj X' ⟶ Z') (aV : Q.obj Y' ⟶ V') (cV : M.obj Z' ⟶ V')
    (hU : eU ≫ pU = P.map p ≫ aU) (hV : eV ≫ pV = Q.map q ≫ aV)
    (hc : c ≫ q = L.map p ≫ d)
    (hd : α.app X' ≫ Q.map d ≫ aV = M.map aU ≫ cV) :
    (α.app X ≫ Q.map c ≫ eV) ≫ pV = M.map (eU ≫ pU) ≫ cV := by
  have hn := α.naturality p
  dsimp only [Functor.comp_map] at hn
  calc
    (α.app X ≫ Q.map c ≫ eV) ≫ pV =
        α.app X ≫ Q.map (c ≫ q) ≫ aV := by
      simp only [Category.assoc, hV, Functor.map_comp]
    _ = α.app X ≫ Q.map (L.map p) ≫ Q.map d ≫ aV := by
      rw [hc, Functor.map_comp, Category.assoc]
    _ = M.map (P.map p) ≫ α.app X' ≫ Q.map d ≫ aV := by
      rw [← Category.assoc, ← Category.assoc, ← hn]
      simp only [Category.assoc]
    _ = M.map (P.map p) ≫ M.map aU ≫ cV := by rw [hd]
    _ = M.map (eU ≫ pU) ≫ cV := by rw [hU, Functor.map_comp, Category.assoc]

attribute [local implicit_reducible] MorphismProperty Scheme.ProEt
  Scheme.instCategoryProEt

private theorem completedSliceProjection {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) (n : ℕ) :
      ((completedSliceLambda.{t, u} g U).app (completedIntegralCommRingSheafUnrestricted l E W) ≫
        (completedRestrict.{t, u} ((proEtaleBaseChange g).obj U)).map (completedRingMap l E g) ≫
          (completedRestrictCompletion.{t, u} l E ((proEtaleBaseChange g).obj U)).hom) ≫
          completedIntegralCommRingProjectionUnrestricted l E
            ((proEtaleBaseChange g).obj U).left n =
      (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
        ((completedRestrictCompletion.{t, u} l E U).hom ≫
          completedIntegralCommRingProjectionUnrestricted l E U.left n) ≫
          completedRingConstantMap (completedRingSliceArrow g U) (CommRingCat.of
            (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
    exact completedProjectionGlue
      (completedRingPull.{t, u} g) (completedRingPull.{t, u} (completedRingSliceArrow g U))
      (completedRestrict.{t, u} U) (completedRestrict.{t, u} ((proEtaleBaseChange g).obj U))
      (completedSliceLambda.{t, u} g U)
      (X := completedIntegralCommRingSheafUnrestricted l E W)
      (X' := integralCoefficientCommRingSheaf l E W n)
      (Y := completedIntegralCommRingSheafUnrestricted l E T)
      (Y' := integralCoefficientCommRingSheaf l E T n)
      (Z := completedIntegralCommRingSheafUnrestricted l E U.left)
      (Z' := integralCoefficientCommRingSheaf l E U.left n)
      (V := completedIntegralCommRingSheafUnrestricted l E ((proEtaleBaseChange g).obj U).left)
      (V' := integralCoefficientCommRingSheaf l E ((proEtaleBaseChange g).obj U).left n)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (completedRingMap l E g)
      (completedRingConstantMap g (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
      (completedRestrictCompletion.{t, u} l E U).hom
      (completedRestrictCompletion.{t, u} l E ((proEtaleBaseChange g).obj U)).hom
      (completedIntegralCommRingProjectionUnrestricted l E U.left n)
      (completedIntegralCommRingProjectionUnrestricted l E ((proEtaleBaseChange g).obj U).left n)
      (completedRestrictConstant.{t, u} U (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
      (completedRestrictConstant.{t, u} ((proEtaleBaseChange g).obj U) (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
      (completedRingConstantMap (completedRingSliceArrow g U) (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
      (completedRestrictCompletion_projection.{t, u} l E U n)
      (completedRestrictCompletion_projection.{t, u} l E ((proEtaleBaseChange g).obj U) n)
      (completedMap_projection l E g n)
      (completedSliceConstant.{t, u} g U (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

private theorem completedSliceMap_eq {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) :
    (completedSliceLambda.{t, u} g U).app
        (completedIntegralCommRingSheafUnrestricted l E W) ≫
      (completedRestrict.{t, u} ((proEtaleBaseChange g).obj U)).map
        (completedRingMap l E g) ≫
      (completedRestrictCompletion.{t, u} l E ((proEtaleBaseChange g).obj U)).hom =
    (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
        (completedRestrictCompletion.{t, u} l E U).hom ≫
      completedRingMap l E (completedRingSliceArrow g U) := by
  apply completedMap_ext l E
  intro n
  rw [completedSliceProjection.{t, u} l E g U n, Category.assoc,
    completedMap_projection l E (completedRingSliceArrow g U) n, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

end SliceProof

/-- Slice identifications preserve constants and every completed projection; the
localized structural map is precisely the completed map of the base change.
Source: Stacks 04J0; Bhatt--Scholze 6.6.11, 6.8.15
(blueprint: lem-tw-completed-coefficient-ringed-coherence).
Proof:
1. Apply weakly-etale localization to U and its base change. Its equivalences are
sliceFrom and sliceTo, and its constant-ring comparison is identity on constants.
Naturality in quotient reduction gives compatible finite-level identifications.
2. Slice restriction is sectionwise, so it preserves this inverse limit. The
finite comparisons induce the completed identifications and commute with pi_n.
3. Localize the ringed-site morphism (Stacks 04J0). The direct-image comparison
on H is restriction along H ×_U (U ×_W T) ≅ H ×_W T. Its inverse-image mate is the
unit/comparison/counit composite displayed below and is invertible.
4. Under the constant comparisons, its finite structural adjunct sends a constant
a to the same constant on the same fibre product. It is therefore the defining
adjunct for c_v. Naturality of the mate at pi_n gives the finite projection
identity; joint limit uniqueness gives the completed identity. No flatness or
invertibility assumption on any structural coefficient map enters. -/
theorem completedRingMap_slice {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    ∃ (eU : (completedRingRestriction.{t, u} U).obj
          (completedIntegralCommRingSheafUnrestricted l E W) ≅
            completedIntegralCommRingSheafUnrestricted l E U.left)
      (eV : (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).obj
          (completedIntegralCommRingSheafUnrestricted l E T) ≅
            completedIntegralCommRingSheafUnrestricted l E ((proEtaleBaseChange g).obj U).left)
      (aU : ∀ n : ℕ, (completedRingRestriction.{t, u} U).obj
          (integralCoefficientCommRingSheaf l E W n) ≅
            integralCoefficientCommRingSheaf l E U.left n)
      (aV : ∀ n : ℕ,
        (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).obj
          (integralCoefficientCommRingSheaf l E T n) ≅
            integralCoefficientCommRingSheaf l E ((proEtaleBaseChange g).obj U).left n)
      (beta : (proEtaleBaseChange g).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (ProEt.topology W) (ProEt.topology T) ⋙
            completedRingRestriction.{t, u} U ≅
        completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U) ⋙
          (proEtaleBaseChange (completedRingSliceArrow g U)).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} (ProEt.topology U.left)
              (ProEt.topology ((proEtaleBaseChange g).obj U).left))
      (lambda : completedRingRestriction.{t, u} U ⋙
          completedRingPull.{t, u} (completedRingSliceArrow g U) ≅
        completedRingPull.{t, u} g ⋙
          completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)),
      (∀ (F : Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}) (H : U.left.ProEt),
        (beta.hom.app F).hom.app (op H) =
          F.obj.map (completedRingSlicePointIso g U H).hom.op) ∧
      (∀ F : Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)},
        lambda.hom.app F =
          (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
            ((completedRingRestriction.{t, u} U).map ((completedRingAdj.{t, u} g).unit.app F)) ≫
          (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
            (beta.hom.app ((completedRingPull.{t, u} g).obj F)) ≫
          (completedRingAdj.{t, u} (completedRingSliceArrow g U)).counit.app
            ((completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).obj
              ((completedRingPull.{t, u} g).obj F))) ∧
      (∀ n : ℕ, eU.hom ≫ completedIntegralCommRingProjectionUnrestricted l E U.left n =
        (completedRingRestriction.{t, u} U).map
          (completedIntegralCommRingProjectionUnrestricted l E W n) ≫ (aU n).hom) ∧
      (∀ n : ℕ, eV.hom ≫ completedIntegralCommRingProjectionUnrestricted l E
          ((proEtaleBaseChange g).obj U).left n =
        (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).map
          (completedIntegralCommRingProjectionUnrestricted l E T n) ≫ (aV n).hom) ∧
      (∀ (n : ℕ) (H : U.left.ProEt),
        (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((MorphismProperty.Over.map ⊤ U.prop).obj H)) ≫
            (aU n).hom.hom.app (op H) =
        (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))))).app (op H)) ∧
      (∀ (n : ℕ) (H : ((proEtaleBaseChange g).obj U).left.ProEt),
        (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((MorphismProperty.Over.map ⊤ ((proEtaleBaseChange g).obj U).prop).obj H)) ≫
            (aV n).hom.hom.app (op H) =
        (toSheafify (ProEt.topology ((proEtaleBaseChange g).obj U).left)
          ((Functor.const ((proEtaleBaseChange g).obj U).left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1)))))).app (op H)) ∧
      (lambda.hom.app (completedIntegralCommRingSheafUnrestricted l E W) ≫
        (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).map
          (completedRingMap l E g) ≫ eV.hom =
        (completedRingPull.{t, u} (completedRingSliceArrow g U)).map eU.hom ≫
          completedRingMap l E (completedRingSliceArrow g U)) ∧
      ∀ n : ℕ,
        (lambda.hom.app (completedIntegralCommRingSheafUnrestricted l E W) ≫
          (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).map
            (completedRingMap l E g) ≫ eV.hom) ≫
              completedIntegralCommRingProjectionUnrestricted l E
                ((proEtaleBaseChange g).obj U).left n =
        (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
          (eU.hom ≫ completedIntegralCommRingProjectionUnrestricted l E U.left n) ≫
            completedRingConstantMap (completedRingSliceArrow g U)
              (CommRingCat.of (ULift.{t + 1}
                (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let V := (proEtaleBaseChange g).obj U
  let v := completedRingSliceArrow g U
  let eU := completedRestrictCompletion.{t, u} l E U
  let eV := completedRestrictCompletion.{t, u} l E V
  let aU (n : ℕ) := completedRestrictConstant.{t, u} U (CommRingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let aV (n : ℕ) := completedRestrictConstant.{t, u} V (CommRingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let beta := asIso (completedSliceBeta.{t, u} g U)
  let lambda := asIso (completedSliceLambda.{t, u} g U)
  have hp (n : ℕ) :
      (lambda.hom.app (completedIntegralCommRingSheafUnrestricted l E W) ≫
        (completedRestrict.{t, u} V).map (completedRingMap l E g) ≫ eV.hom) ≫
          completedIntegralCommRingProjectionUnrestricted l E V.left n =
      (completedRingPull.{t, u} v).map
        (eU.hom ≫ completedIntegralCommRingProjectionUnrestricted l E U.left n) ≫
          completedRingConstantMap v (CommRingCat.of
            (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
    exact completedSliceProjection.{t, u} l E g U n
  refine ⟨eU, eV, aU, aV, beta, lambda, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp⟩
  · exact completedSliceBeta_app g U
  · exact completedSliceLambda_app g U
  · exact completedRestrictCompletion_projection.{t, u} l E U
  · exact completedRestrictCompletion_projection.{t, u} l E V
  · intro n H
    exact completedRestrictConstant_unit.{t, u} U _ H
  · intro n H
    exact completedRestrictConstant_unit.{t, u} V _ H
  · exact completedSliceMap_eq.{t, u} l E g U

end WeilConjectures
