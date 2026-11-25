/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageAssociativity

/-!
# Proper exchange along a commuting triangle

Source: blueprint proposition-composition-base-change-rf-shriek--4, proof (3), proper mate pasting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace CategoryTheory
section FamilyCoherence

variable {I : Type*} [Category I] {C : I → Type*} [∀ i, Category (C i)]
    (D : ∀ {X Y : I}, (X ⟶ Y) → C Y ⥤ C X)
    (χ : ∀ {X Y Z : I} (f : X ⟶ Y) (g : Y ⟶ Z), D (f ≫ g) ≅ D g ⋙ D f)

variable (hc : ∀ {S T U V : I} (a : S ⟶ T) (b : T ⟶ U) (c : U ⟶ V)
    (M : C V), (χ (a ≫ b) c).hom.app M ≫ (χ a b).hom.app ((D c).obj M) =
      (eqToIso (congrArg D (Category.assoc a b c))).hom.app M ≫
        (χ a (b ≫ c)).hom.app M ≫ (D a).map ((χ b c).hom.app M))

include hc

end FamilyCoherence

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Direct-image composition followed by the specified equality of scheme maps.
Source: blueprint proposition-composition-base-change-rf-shriek--4, proof (3).
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportPushforwardTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ C) (q : A ⟶ C)
    (e : a ≫ p = q) :
    R((a)_*⟦Λ⟧) ⋙ R((p)_*⟦Λ⟧) ≅ R((q)_*⟦Λ⟧) :=
  (refinementDerivedLowerStarComp Λ a p).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ e)

/-- Pull back a morphism of triangles to the two literal fibre products.
Source: blueprint proposition-composition-base-change-rf-shriek--4, proof (3).
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportTrianglePullback
    {A B Y Y' : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y) : pullback q v ⟶ pullback p v :=
  pullback.map q v p v a (𝟙 Y') (𝟙 Y) (by simpa using e.symm) (by simp)

/-- The Cartesian square of a pulled-back morphism of triangles.
Source: base change of a refinement, as in Compactification.Refinement.ofIsPullback.
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportTrianglePullbackSquare
    {A B Y Y' : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y) :
    ChosenCartesianSquare (pullback.fst q v) (compactSupportTrianglePullback a p q e v)
      a (pullback.fst p v) := by
  have hfst : compactSupportTrianglePullback a p q e v ≫ pullback.fst p v =
      pullback.fst q v ≫ a := by simp [compactSupportTrianglePullback]
  have hp : IsPullback (compactSupportTrianglePullback a p q e v) (pullback.fst q v)
      (pullback.fst p v) a := by
    refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback p v).flip
    have hsnd : compactSupportTrianglePullback a p q e v ≫ pullback.snd p v =
        pullback.snd q v := by simp [compactSupportTrianglePullback]
    rw [hsnd, e]
    exact (IsPullback.of_hasPullback q v).flip
  exact
    { toCommSq := hp.flip.toCommSq
      isoPullback := hp.flip.isoPullback
      hom_fst := hp.flip.isoPullback_hom_fst
      hom_snd := hp.flip.isoPullback_hom_snd }

attribute [local irreducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStar lowerStar upperStarComp
  upperStarLowerStarAdjunction derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarIsoMapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private abbrev exactUpper {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar Λ f).mapDerivedCategory

private def exactComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exactUpper Λ (f ≫ g) ≅ exactUpper Λ g ⋙ exactUpper Λ f :=
  Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f g)

private def exactSquare {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    exactUpper Λ g ⋙ exactUpper Λ f' ≅ exactUpper Λ f ⋙ exactUpper Λ g' :=
  (exactComp Λ f' g).symm ≪≫
    eqToIso (congrArg (exactUpper Λ) h.symm) ≪≫ exactComp Λ g' f

omit [IsCommMonObj Λ] in
private theorem derive_transport {A B : Scheme.{u}} {f g : A ⟶ B} (e : f = g) :
    Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ e) =
      eqToIso (congrArg (fun f ↦ (lowerStar Λ f).rightDerivedFunctor) e) := by
  cases e
  apply Iso.ext
  simp [lowerStarCongr, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans]
private theorem pull_comp_exact {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedUpperStarComp Λ f g =
      leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g) ≪≫
      exactComp Λ f g ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
        (upperStar Λ f).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (upperStar Λ g).leftDerivedFunctor
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    exactComp, Iso.trans_assoc]
private theorem pull_eq_exact {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    eqToIso (congrArg (fun f ↦ (upperStar Λ f).leftDerivedFunctor) h) ≪≫
        leftDerivedUpperStarIsoMapDerivedCategory Λ g =
      leftDerivedUpperStarIsoMapDerivedCategory Λ f ≪≫
        eqToIso (congrArg (exactUpper Λ) h) := by
  cases h
  simp
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
private theorem square_exact {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
        (upperStar Λ f').mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (upperStar Λ g).leftDerivedFunctor
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f').symm ≪≫
      condensedAmbientPullbackComparison Λ sq ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
        (upperStar Λ g').leftDerivedFunctor ≪≫
      Functor.isoWhiskerLeft (upperStar Λ f).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory Λ g') =
      exactSquare Λ g' f' f g sq.toCommSq.w := by
  simp only [condensedAmbientPullbackComparison, pull_comp_exact, Iso.trans_symm,
    Iso.symm_symm_eq, ← Functor.isoWhiskerLeft_symm, ← Functor.isoWhiskerRight_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [Functor.isoWhiskerLeft_symm,
    Functor.isoWhiskerLeft_trans_isoWhiskerRight_assoc]
  simp only [← Functor.isoWhiskerLeft_symm, Iso.symm_self_id, Iso.trans_refl]
  rw [← Iso.trans_assoc (eqToIso (congrArg
    (fun f ↦ (upperStar Λ f).leftDerivedFunctor) sq.toCommSq.w.symm))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (g' ≫ f))]
  rw [pull_eq_exact Λ sq.toCommSq.w.symm]
  simp only [exactSquare, Iso.trans_assoc,
    Iso.symm_self_id_assoc]
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
private theorem triangle_assoc {A B C D : Scheme.{u}}
    (s : A ⟶ B) (a : B ⟶ C) (p : C ⟶ D) (q : B ⟶ D)
    (r : A ⟶ C) (z : A ⟶ D) (e : a ≫ p = q)
    (es : s ≫ q = z) (er : r ≫ p = z) (esr : s ≫ a = r)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))) :
    (compactSupportPushforwardTriangle Λ a p q e).hom.app
        ((lowerStar Λ s).rightDerivedFunctor.obj N) ≫
      (compactSupportPushforwardTriangle Λ s q z es).hom.app N =
    (lowerStar Λ p).rightDerivedFunctor.map
        ((compactSupportPushforwardTriangle Λ s a r esr).hom.app N) ≫
      (compactSupportPushforwardTriangle Λ r p z er).hom.app N := by
  subst q
  subst r
  subst z
  simp only [compactSupportPushforwardTriangle, Iso.trans_hom, Iso.symm_hom,
    derive_transport, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  have hc := congr_app (derivedDirectImageAssociativity Λ s a p) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hc
  let T := Functor.rightDerivedFunctorNatIso
    (lowerStarCongr Λ (Category.assoc s a p))
  have hi :
      (directImageComposition Λ (s ≫ a) p).app N ≪≫
        (lowerStar Λ p).rightDerivedFunctor.mapIso ((directImageComposition Λ s a).app N) =
      T.app N ≪≫ (directImageComposition Λ s (a ≫ p)).app N ≪≫
        (directImageComposition Λ a p).app ((lowerStar Λ s).rightDerivedFunctor.obj N) := by
    apply Iso.ext
    exact hc
  have hh := congrArg (fun i ↦ i.inv ≫ T.hom.app N) hi
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc,
    Category.comp_id, T, derive_transport, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    directImageComposition] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

end AlgebraicGeometry.ProEtale.CondensedRing
