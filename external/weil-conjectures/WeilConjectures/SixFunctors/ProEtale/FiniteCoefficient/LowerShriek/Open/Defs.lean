/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!

# Lower shriek along a localization of small pro-étale sites

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

Let `f : V ⟶ U` be a weakly étale morphism. Composition with `f` induces the localization
functor `MorphismProperty.Over.map ⊤ h : V.ProEt ⥤ U.ProEt` between the small pro-étale
sites, and this file defines the lower shriek functor `j_{f!}` on `A`-valued pro-étale
sheaves along this localization functor, together with its right adjoint, the restriction
functor `j_f^*`.

When `f` is moreover an open immersion (in particular a monomorphism), `j_{f!}` is the
*extension by zero* functor. It is then exact and fully faithful; fully faithfulness is
`AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful`,
proved from the adjoint triple `ProEtale.localizationAdjunctionTriple` below.

## Main definitions

- `AlgebraicGeometry.ProEtale.localizationLowerShriek`: the lower shriek `j_{f!}`.
- `AlgebraicGeometry.ProEtale.localizationRestriction`: the restriction `j_f^*`.
- `AlgebraicGeometry.ProEtale.localizationLowerShriekAdjunction`: the adjunction
  `j_{f!} ⊣ j_f^*`.
- `AlgebraicGeometry.ProEtale.localizationRestrictionLowerStarAdjunction`: the adjunction
  `j_f^* ⊣ f_*`, completing the triple `j_{f!} ⊣ j_f^* ⊣ f_*`.
- `AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`: for `f` weakly étale the
  pullback `f^*` of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` is
  computed by restriction, both being left adjoint to `f_*`.
- `AlgebraicGeometry.ProEtale.localizationLowerShriekUpperStarAdjunction`: the adjunction
  `j_{f!} ⊣ f^*`.
- `AlgebraicGeometry.ProEtale.localizationAdjunctionTriple`: the triple
  `j_{f!} ⊣ j_f^* ⊣ f_*` as a `CategoryTheory.Adjunction.Triple`. Via
  `CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit` this is what makes `j_{f!}`
  fully faithful as soon as `f_*` is.
- `AlgebraicGeometry.ProEtale.localizationLowerShriekPresheaf` and
  `AlgebraicGeometry.ProEtale.localizationLowerShriekPresheafAdjunction`: the presheaf-level
  Kan extension `j_{f,!}^{pre}` and its adjunction with restriction.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriek`: the lower shriek `j_!` along an
  open immersion `j`, with scoped notation `(j)_!open[A]`, whose `open` keeps it apart from
  `AlgebraicGeometry.ProEtale.lowerShriek` along a morphism admitting a compactification.
- `AlgebraicGeometry.ProEtale.openImmersionRestriction`: the restriction `j^*` along an open
  immersion `j`, given objectwise by `(j^* G)(T → U) = G(T → U → X)`.
- `AlgebraicGeometry.ProEtale.upperStarIsoOpenImmersionRestriction`: the pullback `j^*` of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` is computed by
  restriction.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`: the adjunction
  `j_! ⊣ j^*` between the lower shriek and the pullback `ProEtale.upperStar`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek` and
  `AlgebraicGeometry.ProEtale.preservesFiniteColimits_openImmersionLowerShriek`: the lower
  shriek `j_!` is exact when `j` is an open immersion. The left exactness of the
  presheaf-level lower shriek is
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overMap` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

## Implementation notes

- `j_{f!}` is defined as the left Kan extension along `(MorphismProperty.Over.map ⊤ h).op`
  on presheaves followed by sheafification; this holds definitionally, see
  `localizationLowerShriek_eq`. For a monomorphism `f` — in particular for an open
  immersion — no Kan extension existence hypothesis is needed: the indexing comma
  categories are either empty or admit a terminal object, so both the existence and the
  left exactness of the presheaf-level left Kan extension are provided by the instances of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
- `j_f^*` restricts along the localization functor, so it requires `WeaklyEtale f`, but it
  needs neither Kan extensions nor sheafification. The pullback `ProEtale.upperStar` of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` is defined for an
  arbitrary morphism at the cost of both; the two agree for a weakly étale `f`, by
  `upperStarIsoLocalizationRestriction`.
- The continuity and cocontinuity of the localization functor are
  `AlgebraicGeometry.Scheme.ProEt.isContinuous_overMap` and
  `AlgebraicGeometry.Scheme.ProEt.isCocontinuous_overMap` of
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`.
-/

@[expose] public section

universe w u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)

section LowerShriek

variable [Mono f]

/-- The lower shriek `j_{f!}` along a weakly étale `f : V ⟶ U`: left Kan extension on
presheaves followed by sheafification, left adjoint to
`ProEtale.localizationRestriction`. -/
noncomputable def ProEtale.localizationLowerShriek :
    Sheaf (Scheme.ProEt.topology V) A ⥤ Sheaf (Scheme.ProEt.topology U) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h) A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

end LowerShriek

section Restriction

/-- The restriction functor `j_f^*` along a weakly étale `f : V ⟶ U`, given objectwise by
`(j_f^* G)(T → V) = G(T → V → U)`. The continuity of the localization functor is
`AlgebraicGeometry.Scheme.ProEt.isContinuous_overMap`. -/
def ProEtale.localizationRestriction :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology V) A :=
  (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j_f^* G` over `T → V` are the sections of `G` over `T → V → U`. -/
lemma ProEtale.localizationRestriction_obj_val_obj (G : Sheaf (Scheme.ProEt.topology U) A)
    (b : V.ProEt) :
    ((ProEtale.localizationRestriction A f h).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `j_f^*` acts on morphisms by whiskering along `(MorphismProperty.Over.map ⊤ h).op`. -/
lemma ProEtale.localizationRestriction_map_hom_app
    {G G' : Sheaf (Scheme.ProEt.topology U) A} (φ : G ⟶ G') (b : V.ProEt) :
    (((ProEtale.localizationRestriction A f h).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

section Adjunction

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ j_f^*`. -/
noncomputable def ProEtale.localizationLowerShriekAdjunction :
    ProEtale.localizationLowerShriek A f h ⊣ ProEtale.localizationRestriction A f h :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

instance : (ProEtale.localizationLowerShriek A f h).IsLeftAdjoint :=
  (ProEtale.localizationLowerShriekAdjunction A f h).isLeftAdjoint

instance : (ProEtale.localizationRestriction A f h).IsRightAdjoint :=
  (ProEtale.localizationLowerShriekAdjunction A f h).isRightAdjoint

/-- The lower shriek agrees with mathlib's abstract left adjoint
`(MorphismProperty.Over.map ⊤ h).sheafPullback` of the restriction functor. -/
noncomputable def ProEtale.localizationLowerShriekIsoSheafPullback :
    (MorphismProperty.Over.map ⊤ h).sheafPullback A
        (Scheme.ProEt.topology V) (Scheme.ProEt.topology U) ≅
      ProEtale.localizationLowerShriek A f h :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (MorphismProperty.Over.map ⊤ h) A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

end Adjunction

/-! ### Comparison with the pullback `f^*` -/

section UpperStar

open ProEtale

/-- Restriction along the localization functor is left adjoint to the pushforward `f_*`:
this is the right half of the triple `j_{f!} ⊣ j_f^* ⊣ f_*`. It is induced by the
adjunction `MorphismProperty.Over.mapPullbackAdj` between the two site functors, and in
particular requires neither Kan extensions nor sheafification. -/
noncomputable def ProEtale.localizationRestrictionLowerStarAdjunction :
    ProEtale.localizationRestriction A f h ⊣ (f)_*[A] :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f h
    _root_.trivial).sheafPushforwardContinuous
      (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

/-- For a weakly étale `f`, the pullback `f^*` is computed by restriction along the
localization functor: both are left adjoint to `f_*`. In particular `f^*` needs no
sheafification in this case, and its sections are given by
`ProEtale.localizationRestriction_obj_val_obj`. -/
noncomputable def ProEtale.upperStarIsoLocalizationRestriction :
    (f)^*[A] ≅ ProEtale.localizationRestriction A f h :=
  (ProEtale.upperStarLowerStarAdjunction A f).leftAdjointUniq
    (ProEtale.localizationRestrictionLowerStarAdjunction A f h)

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ f^*` between the lower shriek and the pullback, obtained from
`localizationLowerShriekAdjunction` by transporting along
`upperStarIsoLocalizationRestriction`. -/
noncomputable def ProEtale.localizationLowerShriekUpperStarAdjunction :
    ProEtale.localizationLowerShriek A f h ⊣ (f)^*[A] :=
  (ProEtale.localizationLowerShriekAdjunction A f h).ofNatIsoRight
    (ProEtale.upperStarIsoLocalizationRestriction A f h).symm

/-- The adjoint triple `j_{f!} ⊣ j_f^* ⊣ f_*` on pro-étale sheaves, bundling
`localizationLowerShriekAdjunction` and `localizationRestrictionLowerStarAdjunction`. -/
noncomputable def ProEtale.localizationAdjunctionTriple :
    Adjunction.Triple (ProEtale.localizationLowerShriek A f h)
      (ProEtale.localizationRestriction A f h) (f)_*[A] where
  adj₁ := ProEtale.localizationLowerShriekAdjunction A f h
  adj₂ := ProEtale.localizationRestrictionLowerStarAdjunction A f h

end UpperStar

end Restriction

/-! ### The presheaf-level lower shriek -/

section Presheaf

variable [Mono f]

/-- The presheaf-level lower shriek `j_{f,!}^{pre}`: left Kan extension along
`(MorphismProperty.Over.map ⊤ h).op`. -/
noncomputable def ProEtale.localizationLowerShriekPresheaf :
    (V.ProEtᵒᵖ ⥤ A) ⥤ (U.ProEtᵒᵖ ⥤ A) :=
  (MorphismProperty.Over.map ⊤ h).op.lan

/-- The presheaf-level adjunction between `j_{f,!}^{pre}` and restriction. -/
noncomputable def ProEtale.localizationLowerShriekPresheafAdjunction :
    ProEtale.localizationLowerShriekPresheaf A f h ⊣
      (Functor.whiskeringLeft V.ProEtᵒᵖ U.ProEtᵒᵖ A).obj (MorphismProperty.Over.map ⊤ h).op :=
  (MorphismProperty.Over.map ⊤ h).op.lanAdjunction A

/-- The lower shriek is definitionally the left Kan extension on presheaves followed by
sheafification. -/
lemma ProEtale.localizationLowerShriek_eq :
    ProEtale.localizationLowerShriek A f h =
      sheafToPresheaf (Scheme.ProEt.topology V) A ⋙
        ProEtale.localizationLowerShriekPresheaf A f h ⋙
          presheafToSheaf (Scheme.ProEt.topology U) A :=
  rfl

end Presheaf

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open ProEtale

/-- The restriction `j^*` along an open immersion `j : U ⟶ X` on sheaves for the small
pro-étale sites, given objectwise by `(j^* G)(T → U) = G(T → U → X)`. In contrast to
`ProEtale.upperStar` it requires neither Kan extensions nor sheafification. -/
def ProEtale.openImmersionRestriction :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology U) A :=
  ProEtale.localizationRestriction A j inferInstance

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j^* G` over `T → U` are the sections of `G` over `T → U → X`. -/
lemma ProEtale.openImmersionRestriction_obj_val_obj (G : Sheaf (Scheme.ProEt.topology X) A)
    (b : U.ProEt) :
    ((ProEtale.openImmersionRestriction A j).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤
        (inferInstance : @WeaklyEtale _ _ j)).obj b)) :=
  rfl

/-- Restriction along an open immersion is left adjoint to the pushforward `j_*`: this is
the right half of the triple `j_! ⊣ j^* ⊣ j_*`. -/
noncomputable def ProEtale.openImmersionRestrictionLowerStarAdjunction :
    ProEtale.openImmersionRestriction A j ⊣ (j)_*[A] :=
  ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance

/-- The counit of the adjunction `j^* ⊣ j_*` along an open immersion `j` is an
isomorphism: the restriction of a pushforward along an open immersion is the original
sheaf. This holds since `j` is a monomorphism, so the unit of the site-level adjunction
`MorphismProperty.Over.mapPullbackAdj` is an isomorphism. -/
instance ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit :
    IsIso (ProEtale.openImmersionRestrictionLowerStarAdjunction A j).counit :=
  Adjunction.isIso_sheafPushforwardContinuous_counit A
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial)
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The restriction `j^*` along an open immersion on pro-étale sheaves is additive. -/
instance ProEtale.openImmersionRestriction_additive :
    (ProEtale.openImmersionRestriction A j).Additive where

namespace ProEtale

/-- Blueprint `def-weil-extension-by-zero`: Extension by zero. It is the sheafification of the
left Kan extension of the presheaf along the localization functor, whose value at `V ⟶ X` is
`M(V ⟶ U)` if `V ⟶ X` factors through `U` and zero otherwise
(`AlgebraicGeometry.ProEtale.mem_essImage_or_isEmpty_costructuredArrow_op_overMap`).

The lower shriek `j_!` along an open immersion `j : U ⟶ X` on sheaves for the small
pro-étale sites. -/
noncomputable def openImmersionLowerShriek :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A :=
  ProEtale.localizationLowerShriek A j inferInstance

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open[" A "]" =>
  openImmersionLowerShriek A j

end ProEtale

/-- The adjunction `j_! ⊣ j^*` between the extension by zero and the restriction along an
open immersion. -/
noncomputable def ProEtale.openImmersionLowerShriekAdjunction :
    (j)_!open[A] ⊣ ProEtale.openImmersionRestriction A j :=
  ProEtale.localizationLowerShriekAdjunction A j inferInstance

instance : (j)_!open[A].IsLeftAdjoint :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).isLeftAdjoint

instance : (ProEtale.openImmersionRestriction A j).IsRightAdjoint :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).isRightAdjoint

/-- The extension by zero `j_!` along an open immersion on pro-étale sheaves with values in
a preadditive category is additive, being left adjoint to the additive restriction `j^*`. -/
instance ProEtale.openImmersionLowerShriek_additive : (j)_!open[A].Additive :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).left_adjoint_additive

/-- The extension by zero `j_!` along an open immersion on pro-étale sheaves with values in
an abelian category is exact. This is the left exactness half.

`j_!` is the presheaf-level left Kan extension followed by sheafification, and both factors
are left exact: the first by
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overMap`, the second by
the left exactness of sheafification, which is the content of `HasSheafify` beyond the
`HasWeakSheafify` needed to define `j_!`; both are provided for the Grothendieck abelian
coefficient category `A`, the second by the instance of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. -/
instance ProEtale.preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open[A] := by
  have heq : (j)_!open[A] =
      sheafToPresheaf (Scheme.ProEt.topology U) A ⋙
        ProEtale.localizationLowerShriekPresheaf A j inferInstance ⋙
          presheafToSheaf (Scheme.ProEt.topology X) A :=
    rfl
  have hlan : PreservesFiniteLimits
      (ProEtale.localizationLowerShriekPresheaf A j inferInstance) :=
    ProEtale.preservesFiniteLimits_op_lan_overMap A inferInstance
  rw [heq]
  exact comp_preservesFiniteLimits _ _

/-- Together with `ProEtale.preservesFiniteLimits_openImmersionLowerShriek` this
makes `j_!` exact. -/
example : PreservesFiniteColimits (j)_!open[A] :=
  inferInstance

/-- For an open immersion `j`, the pullback `j^*` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` is computed by
restriction along
the localization functor: both are left adjoint to `j_*`. In particular its sections are
given by `ProEtale.openImmersionRestriction_obj_val_obj`. -/
noncomputable def ProEtale.upperStarIsoOpenImmersionRestriction :
    (j)^*[A] ≅ ProEtale.openImmersionRestriction A j :=
  ProEtale.upperStarIsoLocalizationRestriction A j inferInstance

/-- The adjunction `j_! ⊣ j^*` between the lower shriek along an open immersion and the
pullback `ProEtale.upperStar`. -/
noncomputable def ProEtale.openImmersionLowerShriekUpperStarAdjunction :
    (j)_!open[A] ⊣ (j)^*[A] :=
  ProEtale.localizationLowerShriekUpperStarAdjunction A j inferInstance

/-- The adjoint triple `j_! ⊣ j^* ⊣ j_*` on small pro-étale sites along an open
immersion. -/
noncomputable def ProEtale.openImmersionAdjunctionTriple :
    Adjunction.Triple (j)_!open[A] (ProEtale.openImmersionRestriction A j) (j)_*[A] :=
  ProEtale.localizationAdjunctionTriple A j inferInstance

end OpenImmersion

end AlgebraicGeometry
