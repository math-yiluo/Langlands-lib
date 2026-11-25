/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineFiniteLimits
public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficientsInjective
public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficientsRelativeLimit
public import WeilConjectures.CategoryTheory.Sites.CechComplexTransport
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-!
# Čech complexes of pulled-back injective étale sheaves with general coefficients

Let `A` be a Grothendieck abelian category and `I` an injective sheaf on the small étale site of
an affine scheme `W` with values in `A`. We show that the Čech complexes
(`CategoryTheory.Presheaf.overCechComplex`) of the comparison pullback `ν^* I`, for morphisms of
affine pro-étale `W`-schemes, are exact in positive degrees.

Presenting a morphism of affine pro-étale `W`-schemes as a cofiltered limit of morphisms of affine
étale `W`-schemes, the Čech complex of `ν^* I` is the filtered colimit of the Čech complexes of
`I` for these morphisms. These are exact: after applying `Hom(a, -)` for all objects `a` of `A`,
they become Čech complexes of the abelian presheaves `Hom(a, I(-))`, which are exact since `I` is
injective.

## Main statements

- `AlgebraicGeometry.ProEtale.exactAt_overCechComplex_comparisonUpperStar`: the Čech complexes of
  `ν^* I` for morphisms of affine pro-étale schemes are exact in positive degrees.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {W : Scheme.{u}}

/-- The restriction to the affine pro-étale site of the comparison pullback of an étale sheaf
with values in `A` sends cofiltered limits of affine étale schemes to filtered colimits. -/
instance preservesRelativeFilteredColimits_comparisonUpperStar_obj
    (I : Sheaf W.smallEtaleTopology A) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt W)
      ((AffineProEt.toProEt W).op ⋙ ((comparisonUpperStar A W).obj I).obj) where
  nonempty_isColimit {_} _ _ K c hc := by
    let c' : Cone ((K ⋙ AffineEtale.Spec W) ⋙ toProEt W) := (AffineProEt.toProEt W).mapCone c
    have hc' : IsLimit ((ProEt.forget W ⋙ CategoryTheory.Over.forget W).mapCone c') :=
      AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc
    have (j : _) : IsAffine ((K ⋙ AffineEtale.Spec W).obj j).left :=
      inferInstanceAs (IsAffine (Spec _))
    exact isColimit_comparisonUpperStar_mapCocone_of_isAffine A I _ c' hc'

/-- On affine étale `W`-schemes, the comparison pullback `ν^* I` of an étale sheaf `I` with
values in `A` has the sections of `I`: the unit `I ⟶ ν_* ν^* I` is an isomorphism. -/
noncomputable def affineEtaleSectionsComparisonUpperStarObjIso
    (I : Sheaf W.smallEtaleTopology A) :
    (AffineEtale.Spec W).op ⋙ I.obj ≅ (AffineEtale.toAffineProEt W).op ⋙
      (AffineProEt.toProEt W).op ⋙ ((comparisonUpperStar A W).obj I).obj :=
  have := isIso_comparisonAdjunction_unit A W
  asIso ((AffineEtale.Spec W).op.whiskerLeft ((comparisonAdjunction A W).unit.app I).hom)

variable {A} [IsAffine W]

/-- The Čech complex of the comparison pullback of an injective étale sheaf with values in `A`,
restricted to the affine étale site, for a single morphism of affine étale schemes is exact in
positive degrees. -/
lemma exactAt_overCechComplex_stage_comparisonUpperStar
    (I : Sheaf W.smallEtaleTopology A) [Injective I] {X Y : W.AffineEtale} (α : X ⟶ Y)
    (q : ℕ) :
    ((Presheaf.overCechComplex (CategoryTheory.Over.mk α)).obj
      ((AffineEtale.toAffineProEt W).op ⋙ (AffineProEt.toProEt W).op ⋙
        ((comparisonUpperStar A W).obj I).obj)).ExactAt (q + 1) := by
  refine Presheaf.exactAt_overCechComplex_of_forall_exactAt_cechComplex _ _ _ fun a ↦ ?_
  refine HomologicalComplex.ExactAt.of_iso ?_ ((Presheaf.cechComplex _).mapIso
    (Functor.isoWhiskerRight (affineEtaleSectionsComparisonUpperStarObjIso A I)
      (preadditiveCoyoneda.obj (op a))))
  refine (Presheaf.exactAt_cechComplex_comp_iff (AffineEtale.Spec W) _
    (I.obj ⋙ preadditiveCoyoneda.obj (op a)) q).2 ?_
  exact Sheaf.exactAt_cechComplex_comp_preadditiveCoyoneda_of_injective _ I a q

/-- **Čech acyclicity of pulled-back injectives, with coefficients in `A`.** The Čech complex of
the comparison pullback `ν^* I` of an injective étale sheaf `I` with values in `A`, for a
morphism `f` of affine pro-étale `W`-schemes, is exact in positive degrees. Presenting `f` as a
cofiltered limit of morphisms of affine étale `W`-schemes, this Čech complex is the filtered
colimit of the Čech complexes of `I` for these morphisms, which are exact since `I` is
injective. (blueprint: `lemma-acyclicity-pulled-back-injectives`) -/
theorem exactAt_overCechComplex_comparisonUpperStar
    (I : Sheaf W.smallEtaleTopology A) [Injective I] {V V' : W.AffineProEt} (f : V' ⟶ V)
    (q : ℕ) :
    ((Presheaf.overCechComplex (CategoryTheory.Over.mk f)).obj
      ((AffineProEt.toProEt W).op ⋙ ((comparisonUpperStar A W).obj I).obj)).ExactAt
        (q + 1) := by
  obtain ⟨J, _, _, pV', pV, h, rfl⟩ := AffineProEt.exists_relativeLimitPresentation_hom W f
  have : HasFilteredColimitsOfSize.{u, u} A := hasFilteredColimitsOfSize_shrink.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} A := AB5OfSize_shrink.{u, u, u + 1, u + 1} A
  exact Presheaf.exactAt_overCechComplex_of_relativeLimitPresentation h _
    (fun j q ↦ exactAt_overCechComplex_stage_comparisonUpperStar I _ q) q

end AlgebraicGeometry.ProEtale
