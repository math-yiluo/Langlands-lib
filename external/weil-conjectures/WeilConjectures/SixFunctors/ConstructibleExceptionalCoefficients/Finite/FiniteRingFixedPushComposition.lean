/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOrdinaryPushCoordinates
import all WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDirectCompositorCoordinates

/-! # Finite ring-sheaf proper-compositor coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.finite
  AlgebraicGeometry.Scheme.ProEt CategoryTheory.MorphismProperty
set_option backward.defeqAttrib.useBackward true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem refl_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (M : C) : (Iso.refl F).app M = Iso.refl (F.obj M) := rfl

private theorem rightDerived_refl
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    Functor.rightDerivedFunctorNatIso (Iso.refl F) = Iso.refl F.rightDerivedFunctor := by
  apply Iso.ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

private theorem rightDerived_eqToIso_refl
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (h : F = F) :
    Functor.rightDerivedFunctorNatIso (eqToIso h) = Iso.refl F.rightDerivedFunctor := by
  have he : h = rfl := Subsingleton.elim _ _
  rw [he]
  exact rightDerived_refl F

private theorem derived_compositor_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
    [F.PreservesKInjectiveComplexes] [F'.PreservesKInjectiveComplexes]
    (hf : F = F') (hg : G = G') (hh : H = H')
    (d : F ⋙ G ≅ H) (d' : F' ⋙ G' ≅ H')
    (hd : d = Functor.isoWhiskerRight (eqToIso hf) G ≪≫
      Functor.isoWhiskerLeft F' (eqToIso hg) ≪≫ d' ≪≫ (eqToIso hh).symm)
    (M : DerivedCategory C) :
    (Functor.rightDerivedFunctorCompIso' F G d).symm.app M ≪≫
      G.rightDerivedFunctor.mapIso ((Functor.rightDerivedFunctorNatIso (eqToIso hf)).app M) ≪≫
      (Functor.rightDerivedFunctorNatIso (eqToIso hg)).app (F'.rightDerivedFunctor.obj M) =
    (Functor.rightDerivedFunctorNatIso (eqToIso hh)).app M ≪≫
      (Functor.rightDerivedFunctorCompIso' F' G' d').symm.app M := by
  subst F' G' H'
  have hd' : d = d' := by
    apply Iso.ext
    simpa using congrArg Iso.hom hd
  subst d'
  simp only [rightDerived_eqToIso_refl]
  change (Functor.rightDerivedFunctorCompIso' F G d).symm.app M ≪≫
      G.rightDerivedFunctor.mapIso (Iso.refl _) ≪≫ Iso.refl _ =
    Iso.refl _ ≪≫ (Functor.rightDerivedFunctorCompIso' F G d).symm.app M
  simp only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]
  exact Iso.trans_refl _

private theorem inverse_square {C : Type*} [Category C] {S T U V : C}
    (f : S ≅ U) (g : U ≅ V) (d : S ≅ T) (e : T ≅ V)
    (h : f ≪≫ g = d ≪≫ e) : d.symm ≪≫ f = e ≪≫ g.symm := by
  have hh := congrArg (fun a ↦ d.symm ≪≫ a ≪≫ g.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
    Iso.self_symm_id, Iso.symm_self_id, Iso.refl_trans, Iso.trans_refl] using hh

private theorem paste_coordinates {C D : Type*} [Category C] [Category D]
    (G G' : C ⥤ D) (v : G ≅ G') {M N P : C} {S T U V : D}
    (z : S ≅ G.obj M) (z' : T ≅ G'.obj N) (u : M ≅ N)
    (a : S ≅ T) (dh : N ≅ P) (dk : G'.obj P ≅ U) (dt : T ≅ V)
    (b : V ≅ U)
    (h₁ : z ≪≫ G.mapIso u ≪≫ v.app N = a ≪≫ z')
    (h₂ : z' ≪≫ G'.mapIso dh ≪≫ dk = dt ≪≫ b) :
    z ≪≫ G.mapIso (u ≪≫ dh) ≪≫ (v.app P ≪≫ dk) = (a ≪≫ dt) ≪≫ b := by
  apply Iso.ext
  have hn := v.hom.naturality dh.hom
  have hh₁ := congrArg Iso.hom h₁
  have hh₂ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hh₁ hh₂
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hh₁, hh₂]

namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)
private theorem ring_compositor_eq {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring W)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring V)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring U)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h)) :
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let F := proEtaleRingModuleDirectImage h (R.ring V) (R.ring U) (R.pull h)
    let G := proEtaleRingModuleDirectImage k (R.ring W) (R.ring V) (R.pull k)
    let a := proEtaleRingModuleAdjunction h (R.ring V) (R.ring U) (R.pull h)
    let := a.preservesKInjectiveComplexes
    PurCompactSupport.geometricPushComposition R h k hc =
      Functor.rightDerivedFunctorCompIso' F G
        (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose := by
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let a := proEtaleRingModuleAdjunction h (R.ring V) (R.ring U) (R.pull h)
  let b := proEtaleRingModuleAdjunction k (R.ring W) (R.ring V) (R.pull k)
  let c := proEtaleRingModuleAdjunction (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k))
  let d := (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose
  let e := (conjugateIsoEquiv (b.comp a) c).symm d
  let := a.preservesKInjectiveComplexes
  apply Iso.ext
  symm
  exact Adjunction.compIso_hom_eq_conjugate a b c d e
    ((congrArg Iso.hom ((conjugateIsoEquiv (b.comp a) c).apply_symm_apply d)).symm)

private theorem constant_compositor_eq {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let F := proEtaleConstantModuleDirectImage h A
    let G := proEtaleConstantModuleDirectImage k A
    let a := sfIntrinsicConstantModuleAdjunction h A
    let := a.preservesKInjectiveComplexes
    Functor.rightDerivedFunctorCompIso' F G (finiteIntrinsicOrdinaryCompositor l E n h k) =
      conjugateIsoEquiv
        (((sfIntrinsicConstantModuleAdjunction k A).mapDerivedCategoryRightDerivedAdjunction).comp
          (sfIntrinsicConstantModuleAdjunction h A).mapDerivedCategoryRightDerivedAdjunction)
        (sfIntrinsicConstantModuleAdjunction (h ≫ k) A).mapDerivedCategoryRightDerivedAdjunction
        (sfIntrinsicDerivedPullbackComp A h k) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let a := sfIntrinsicConstantModuleAdjunction h A
  let b := sfIntrinsicConstantModuleAdjunction k A
  let c := sfIntrinsicConstantModuleAdjunction (h ≫ k) A
  let := a.preservesKInjectiveComplexes
  apply Iso.ext
  exact Adjunction.compIso_hom_eq_conjugate a b c
    (finiteIntrinsicOrdinaryCompositor l E n h k) (sfIntrinsicPullbackComp A h k) rfl

private theorem constant_coordinates {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W)
    (K : DerivedCategory (Sheaf (ProEt.topology U)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let F := proEtaleConstantModuleDirectImage h A
    let G := proEtaleConstantModuleDirectImage k A
    let a := sfIntrinsicConstantModuleAdjunction h A
    let := a.preservesKInjectiveComplexes
    (Functor.rightDerivedFunctorCompIso' F G (finiteIntrinsicOrdinaryCompositor l E n h k)).symm.app
        ((sfIntrinsicDerivedEquivalence U A).functor.obj K) ≪≫
      (proEtaleConstantDerivedDirectImage k A).mapIso
        ((sfIntrinsicDerivedDirectImageComparison h A).app K) ≪≫
      (sfIntrinsicDerivedDirectImageComparison k A).app
        ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{w + 1} (ULift.{w + 1} A))
          h).rightDerivedFunctor.obj K) =
    (sfIntrinsicDerivedDirectImageComparison (h ≫ k) A).app K ≪≫
      (sfIntrinsicDerivedEquivalence W A).functor.mapIso
        ((AlgebraicGeometry.ProEtale.finiteDirectImageComposition
          (ULift.{w + 1} A) h k).app K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let q := conjugateIsoEquiv
    ((AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction B k).comp
      (AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction B h))
    (AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction B (h ≫ k))
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp B h k)
  let d := conjugateIsoEquiv
    (((sfIntrinsicConstantModuleAdjunction k A).mapDerivedCategoryRightDerivedAdjunction).comp
      (sfIntrinsicConstantModuleAdjunction h A).mapDerivedCategoryRightDerivedAdjunction)
    (sfIntrinsicConstantModuleAdjunction (h ≫ k) A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicDerivedPullbackComp A h k)
  have hq : (AlgebraicGeometry.ProEtale.finiteDirectImageComposition
      (ULift.{w + 1} A) h k).symm = q :=
    Iso.ext (AlgebraicGeometry.ProEtale.finiteDirectImageComposition_conjugate
      (ULift.{w + 1} A) h k)
  have hc : ((proEtaleConstantDerivedDirectImage k A).mapIso
        ((sfIntrinsicDerivedDirectImageComparison h A).app K) ≪≫
      (sfIntrinsicDerivedDirectImageComparison k A).app
        ((AlgebraicGeometry.ProEtale.lowerStar B h).rightDerivedFunctor.obj K)) ≪≫
      (sfIntrinsicDerivedEquivalence W A).functor.mapIso (q.app K) =
    d.app ((sfIntrinsicDerivedEquivalence U A).functor.obj K) ≪≫
      (sfIntrinsicDerivedDirectImageComparison (h ≫ k) A).app K := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      sfIntrinsicDirectCompositorCoordinates A h k K
  dsimp only
  rw [constant_compositor_eq l E n h k]
  have hh := inverse_square _ _ _ _ hc
  rw [← hq] at hh
  exact hh

/-- Realization preserves the inverse proper compositor in finite ring-sheaf coordinates.
This concerns three direct-image functors only; there are no open immersions,
compactifications, etale antecedents, or compact-support objects in the assertion.
Source: compactification-coherence proof, second paragraph; Stacks 03D6 and 0D6E
(blueprint: lem-sf-finite-ring-fixed-push-composition).

Proof: first eliminate the equality h ≫ k = g by substitution. Before deriving,
modulePushComposition_existsUnique fixes the ring-sheaf direct-image compositor
on every section by pullbackComp. finiteDirectImage_eq identifies its structural
map with the constant-section structural map. The ordinary realization comparison
sfIntrinsicDirectImageComparison preserves these scalar-unit sections. Therefore
the pasted ordinary realization comparisons intertwine the two direct-image
compositors: both sides send a section to its restriction along pullbackComp.
Faithfulness of underlying module sheaves proves equality of the natural maps.
Resolve a fixed-scalar input by a K-injective complex. The exact inverse-image
adjunction makes each first direct image preserve K-injectives, as do the realization
equivalences. The normalization in sfIntrinsicDerivedDirectImageComparison_existsUnique
identifies the derived maps with the ordinary maps on that resolution. The conjugate
of geometricPullComposition is the derived module compositor: its ordinary mate
is modulePushComposition_existsUnique, and the derived adjunction factorization
preserves the mate equation. The inverse of finiteDirectImageComposition is the
same derived compositor in fixed-scalar coordinates. Derive the ordinary equality,
then invert it and cancel the comparison for h ≫ k. This is the displayed equation
on K-injective inputs. Naturality and existence of a K-injective resolution extend
it to every input. Equality transport was removed by substitution, hence is restored
by the two displayed eqToIso factors. The argument also covers identity maps,
empty schemes and zero coefficients. -/
theorem finiteFixedPushIso_composition
    {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W) (g : U ⟶ W)
    (w : h ≫ k = g)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring W)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring V)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring U)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h))
    (K : DerivedCategory (Sheaf (ProEt.topology U)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    ((PurCompactSupport.geometricPushComposition R h k hc ≪≫
      eqToIso (congrArg (fun t ↦ PurCompactSupport.push R t) w)).symm.app
        ((sfIntrinsicDerivedEquivalence U A).functor.obj K)) ≪≫
      (PurCompactSupport.push R k).mapIso ((finiteFixedPushIso l E n h).app K) ≪≫
      (finiteFixedPushIso l E n k).app
        ((AlgebraicGeometry.ProEtale.lowerStar B h).rightDerivedFunctor.obj K) =
    (finiteFixedPushIso l E n g).app K ≪≫
      (sfIntrinsicDerivedEquivalence W A).functor.mapIso
        ((eqToIso (congrArg (fun t ↦
          (AlgebraicGeometry.ProEtale.lowerStar B t).rightDerivedFunctor) w.symm)).app K ≪≫
          (AlgebraicGeometry.ProEtale.finiteDirectImageComposition
            (ULift.{w + 1} A) h k).app K) := by
  subst g
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, refl_app, Iso.refl_trans]
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let F := proEtaleRingModuleDirectImage h (R.ring V) (R.ring U) (R.pull h)
  let G := proEtaleRingModuleDirectImage k (R.ring W) (R.ring V) (R.pull k)
  let H := proEtaleRingModuleDirectImage (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k))
  let F' := proEtaleConstantModuleDirectImage h A
  let G' := proEtaleConstantModuleDirectImage k A
  let H' := proEtaleConstantModuleDirectImage (h ≫ k) A
  let : F.Additive := proEtaleRingModuleDirectImage_additive h _ _ _
  let : G.Additive := proEtaleRingModuleDirectImage_additive k _ _ _
  let : H.Additive := proEtaleRingModuleDirectImage_additive (h ≫ k) _ _ _
  let : F'.Additive := (proEtaleConstantModuleDirectImage_additive_leftExact h A).1
  let : G'.Additive := (proEtaleConstantModuleDirectImage_additive_leftExact k A).1
  let : H'.Additive := (proEtaleConstantModuleDirectImage_additive_leftExact (h ≫ k) A).1
  let := (proEtaleRingModuleAdjunction h (R.ring V) (R.ring U)
    (R.pull h)).preservesKInjectiveComplexes
  let := (sfIntrinsicConstantModuleAdjunction h A).preservesKInjectiveComplexes
  let u := Functor.rightDerivedFunctorNatIso
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n h))
  let v := Functor.rightDerivedFunctorNatIso
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n k))
  let t := Functor.rightDerivedFunctorNatIso
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n (h ≫ k)))
  let e := (sfIntrinsicDerivedEquivalence U A).functor
  let q := (sfIntrinsicDerivedEquivalence W A).functor
  let d := (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose
  let d' := finiteIntrinsicOrdinaryCompositor l E n h k
  have hr := derived_compositor_transport F F' G G' H H'
    (PurCompactSupport.finiteDirectImage_eq l E n h)
    (PurCompactSupport.finiteDirectImage_eq l E n k)
    (PurCompactSupport.finiteDirectImage_eq l E n (h ≫ k))
    d d' (finiteOrdinaryPushComposition l E n h k hc) (e.obj K)
  rw [← ring_compositor_eq l E n h k hc] at hr
  exact paste_coordinates G.rightDerivedFunctor G'.rightDerivedFunctor v
    ((PurCompactSupport.geometricPushComposition R h k hc).symm.app (e.obj K))
    ((Functor.rightDerivedFunctorCompIso' F' G' d').symm.app (e.obj K))
    (u.app (e.obj K)) (t.app (e.obj K))
    ((sfIntrinsicDerivedDirectImageComparison h A).app K)
    ((sfIntrinsicDerivedDirectImageComparison k A).app
      ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{w + 1} (ULift.{w + 1} A))
        h).rightDerivedFunctor.obj K))
    ((sfIntrinsicDerivedDirectImageComparison (h ≫ k) A).app K)
    (q.mapIso ((AlgebraicGeometry.ProEtale.finiteDirectImageComposition
      (ULift.{w + 1} A) h k).app K)) hr (constant_coordinates l E n h k K)

end WeilConjectures.ConstructibleExceptionalCoefficients
