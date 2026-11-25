/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoBoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-! # Compact-support base change for isomorphic condensed coefficients

Source: latest blueprint, lem-fd-base-change.proof.md, compact-support paragraph
(blueprint: lem-fd-condensed-compact-support-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem nonempty_compactSupport_comapIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ' ⟶ Λ) [IsMonHom a]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]
    {T Z : Scheme.{u}} {p : T ⟶ Z} (d : Compactification p) :
    Nonempty (rightDerivedLowerShriekOfCompactification Λ d ⋙
        (Mod.comap (coefficientMap a Z)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a T)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ' d) := by
  let J := openImmersionLowerShriek Λ d.i
  let J' := openImmersionLowerShriek Λ' d.i
  let P' := lowerStar Λ' d.g
  let j : J.mapDerivedCategory ⋙ (Mod.comap (coefficientMap a d.Z)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a T)).mapDerivedCategory ⋙ J'.mapDerivedCategory :=
    Functor.mapDerivedCategorySquareIso (comapOpenImmersionLowerShriekIso a d.i)
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft J.mapDerivedCategory (derivedComapLowerStarIso a d.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight j P'.rightDerivedFunctor ≪≫ Functor.associator _ _ _⟩

private theorem transport_compactSupport_baseChange
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (c : Compactification f) (c' : Compactification f')
    (h : ∀ K, boundedConstructible (condensedRingObj Λ' X) K →
      Nonempty ((upperStar Λ' g).leftDerivedFunctor.obj
          ((rightDerivedLowerShriekOfCompactification Λ' c).obj K) ≅
        (rightDerivedLowerShriekOfCompactification Λ' c').obj
          ((upperStar Λ' g').leftDerivedFunctor.obj K)))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hK : boundedConstructible (condensedRingObj Λ X) K) :
    Nonempty ((upperStar Λ g).leftDerivedFunctor.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ≅
      (rightDerivedLowerShriekOfCompactification Λ c').obj
        ((upperStar Λ g').leftDerivedFunctor.obj K)) := by
  -- Fix the coefficient objects before elaborating the derived comparisons.
  let a : Λ' ⟶ Λ := e.inv.hom
  have : IsMonHom a := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso a := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  let (T : Scheme.{u}) : IsIso (coefficientMap a T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map a))
  let (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (coefficientMap a T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (coefficientMap a T)).symm
  let U (T : Scheme.{u}) :
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ' T)) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (coefficientMap a T)).mapDerivedCategory
  have he (T : Scheme.{u}) : (U T).IsEquivalence := by
    have : (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (coefficientMap a T)).IsEquivalence :=
      (inferInstance : (Mod.comapEquivalenceOfIsIso
        (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (coefficientMap a T)).functor.IsEquivalence)
    exact Functor.isEquivalence_mapDerivedCategory _
  have hK' : boundedConstructible (condensedRingObj Λ' X) ((U X).obj K) :=
    (boundedConstructible_comap_iso_iff (coefficientMap a X) K).2 hK
  obtain ⟨ec⟩ := nonempty_compactSupport_comapIso a c
  obtain ⟨ec'⟩ := nonempty_compactSupport_comapIso a c'
  obtain ⟨bc⟩ := h ((U X).obj K) hK'
  have : (U Y').IsEquivalence := he Y'
  refine ⟨(U Y').preimageIso (?_)⟩
  exact (derivedComapLeftDerivedUpperStarIso a g).symm.app _ ≪≫
    (upperStar Λ' g).leftDerivedFunctor.mapIso (ec.app K) ≪≫
    bc ≪≫
    (rightDerivedLowerShriekOfCompactification Λ' c').mapIso
      ((derivedComapLeftDerivedUpperStarIso a g').app K) ≪≫
    (ec'.app ((upperStar Λ g').leftDerivedFunctor.obj K)).symm

/-- Compact-support base change on bounded constructible complexes is independent
of the chosen compactifications and of an isomorphic presentation of E or Qlbar.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
lem-fd-base-change.proof.md, compact-support pushforward paragraph
(blueprint: lem-fd-condensed-compact-support-base-change).

Proof: For the canonical coefficient rings the compact-support base-change map
is an isomorphism on the bounded constructible category. Evaluate it on the given
complex and apply the full inclusion into the ambient category. Independence of
compactification replaces the base-changed compactification by the specified one.
For an isomorphic coefficient ring, restrict scalars along the inverse ring
isomorphism. This is an exact equivalence preserving bounded constructibility.
It commutes with derived pullback, extension by zero, and derived pushforward,
hence with both compactification functors. Apply the canonical-coefficient
isomorphism after restriction and lift it back through the fully faithful
equivalence. All constructions are valid for the empty scheme. -/
theorem nonempty_iso_compactSupport_baseChange_of_coefficientIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)))
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (c : Compactification f.left) (c' : Compactification f'.left)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    Nonempty ((upperStar Λ g.left).leftDerivedFunctor.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ≅
      (rightDerivedLowerShriekOfCompactification Λ c').obj
        ((upperStar Λ g'.left).leftDerivedFunctor.obj K)) := by
  rcases hΛ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine transport_compactSupport_baseChange e f.left g.left f'.left g'.left c c'
      (fun L hL ↦ ?_) K hK
    let L' : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E)
        X.left) := ⟨L, hL⟩
    have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E c sq
    let bc := asIso
      (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
        ℓ E c sq)
    let ci := boundedConstructibleLowerShriekOfCompactificationIso ℓ E
      (c.ofIsPullback sq.overLeft) c'
    exact ⟨(boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E)
      Y'.left)).ι.mapIso (bc.app L' ≪≫ ci.app
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g').obj L'))⟩
  · refine transport_compactSupport_baseChange e f.left g.left f'.left g'.left c c'
      (fun L hL ↦ ?_) K hK
    let L' : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        X.left) := ⟨L, hL⟩
    have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicAlgCl
      ℓ c sq
    let bc := asIso (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq)
    let ci := boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
      (c.ofIsPullback sq.overLeft) c'
    exact ⟨(boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      Y'.left)).ι.mapIso (bc.app L' ≪≫ ci.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj L'))⟩

end AlgebraicGeometry.ProEtale.CondensedRing
