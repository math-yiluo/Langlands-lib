/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.CategoryTheory.Adjunction.MatesCounit
import WeilConjectures.SixFunctors.ProjectiveLinePresentations
import WeilConjectures.SixFunctors.ProjectiveLineTraceAdjunction
import WeilConjectures.SixFunctors.ProjectiveLineTraceCounitBaseChange

/-!
# The projective-line case of exceptional base change

Source: blueprint `lemma-affine-space-etale-localization`, proof (1), and
`proposition-exceptional-inverse-image-smooth-morphism--6`, proof, projective-line model.
-/

@[expose] public section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

attribute [local irreducible] ordinaryFiniteTensor
  ordinaryFiniteTwistedPullback finiteP1TwistedPullbackComparison
  rightDerivedLowerShriekBaseChangeMap rightDerivedUpperShriekAdjunction
  rightDerivedUpperShriekBaseChangeMap mateEquiv
  rightDerivedUpperShriek rightDerivedLowerShriek
  ordinaryFinitePullback ordinaryFinitePushforward

private theorem exceptionalBaseChange_eq_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f'] :
    have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    rightDerivedUpperShriekBaseChangeMap A sq =
      mateEquiv (rightDerivedUpperShriekAdjunction _ f)
        (rightDerivedUpperShriekAdjunction _ f')
        (inv (rightDerivedLowerShriekBaseChangeMap A sq)) := by
  unfold rightDerivedUpperShriekBaseChangeMap
  rfl

private theorem exceptionalBaseChange_isIso_of_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (F' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X')
    (adj : R(f)_![ModuleCat.{u + 1} A] ⊣ F)
    (adj' : R(f')_![ModuleCat.{u + 1} A] ⊣ F')
    (c : ∀ K, (L((g')^*[ModuleCat.{u + 1} A])).obj (F.obj K) ≅
      F'.obj ((L((g)^*[ModuleCat.{u + 1} A])).obj K))
    (hc : ∀ K, (rightDerivedLowerShriekBaseChangeMap A sq).app (F.obj K) ≫
      (R(f')_![ModuleCat.{u + 1} A]).map (c K).hom ≫
        adj'.counit.app ((L((g)^*[ModuleCat.{u + 1} A])).obj K) =
      (L((g)^*[ModuleCat.{u + 1} A])).map (adj.counit.app K)) :
    IsIso (rightDerivedUpperShriekBaseChangeMap A sq) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  rw [exceptionalBaseChange_eq_mate]
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro K
  exact isIso_mateEquiv_app_of_counit (rightDerivedUpperShriekAdjunction _ _)
    (rightDerivedUpperShriekAdjunction _ _) adj adj'
    (inv (rightDerivedLowerShriekBaseChangeMap A sq)) K (c K).hom
    (by
      apply (cancel_epi ((rightDerivedLowerShriekBaseChangeMap A sq).app _)).1
      simpa -implicitDefEqProofs only
        [Category.assoc, NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc] using hc K)

/-- The canonical exceptional base-change map for a projective-line projection over an
arbitrary base is invertible, for finite coefficients of invertible exponent.

Source: blueprint `lemma-affine-space-etale-localization`, proof (1), and
`proposition-exceptional-inverse-image-smooth-morphism--6`, projective-line computation.
(auxiliary; not a blueprint node)

Proof: use the projective-line adjunction whose right adjoint is pullback followed by
the Tate twist and shift (1)[2]. Its counit is the projection-formula map followed by
the trace, where the trace is projection onto the Kummer-class summand of the
projective-line decomposition. The unit and the Kummer class commute with arbitrary
pullback: the first by functoriality of inverse image, the second by naturality of the
Kummer connecting map. Hence the decomposition square commutes with proper exchange.
Invert the decomposition square and project to its Kummer summand to obtain the trace
square. The projection formula and proper exchange satisfy the tensor exchange square;
combining it with the trace square gives the actual counit base-change equation.
The same calculation after identifying a given cartesian square with the standard
base-change square applies to any of its presentations. Transposition through the two
adjunctions identifies the canonical exceptional mate with the pullback/twist/shift
isomorphism. Thus every component of the mate is invertible. This construction uses
the ordinary finite-coefficient projective bundle formula over arbitrary schemes;
it imposes no Noetherian or finite-type-over-a-field hypothesis on either base.
-/
theorem projectiveLineExceptionalBaseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] ⦃S' P' : Scheme.{u}⦄
    {g : S' ⟶ S} {q' : P' ⟶ S'}
    {g' : P' ⟶ ℙ(Option (ULift.{u} (Fin 1)); S)}
    (sq : IsPullback g' q' (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) g)
    [HasCompactification q'] [QuasiCompact q'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  obtain ⟨N, hN, hΛ, hS⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  obtain ⟨t, d, hbc, hdiag⟩ := exists_arbitraryBaseFiniteP1Integrals N hN Λ hΛ
  have : IsProper q' := MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨e, he⟩ := exists_projectiveLinePresentation S
  obtain ⟨e', he', hemap⟩ := exists_projectiveLinePullbackPresentation sq e he
  let hS' := finiteP1_unitOnPullback N g hS
  obtain ⟨adj, hadj⟩ := exists_presentedFiniteP1TraceAdjunction Λ N hN hΛ t d hbc
    (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) e he hS (hdiag S hS)
  obtain ⟨adj', hadj'⟩ := exists_presentedFiniteP1TraceAdjunction Λ N hN hΛ t d hbc
    q' e' he' hS' (hdiag S' hS')
  have hc (K : DerivedCategoryModule Λ S) :
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app
          ((ordinaryFiniteTwistedPullback Λ
            (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
            ((ordinaryFiniteLine Λ N hΛ _)⟦(2 : ℤ)⟧)).obj K) ≫
        (R(q')_![ModuleCat.{u + 1} Λ]).map
          (finiteP1TwistedPullbackComparison Λ N hΛ t sq hS K).hom ≫
        adj'.counit.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((g)^*[ModuleCat.{u + 1} Λ])).map (adj.counit.app K) := by
    rw [hadj, hadj']
    exact presentedFiniteP1Counit_baseChange Λ N hN hΛ t d hbc sq e he e' he' hemap hS hS' K
  exact exceptionalBaseChange_isIso_of_counit Λ sq _ _ adj adj'
    (fun K ↦ finiteP1TwistedPullbackComparison Λ N hΛ t sq hS K) hc

end AlgebraicGeometry.Etale
