/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!

# Lower shriek along a localization of small étale sites

Let `f : V ⟶ U` be an étale morphism. Composition with `f` induces the localization functor
`MorphismProperty.Over.map ⊤ h : V.Etale ⥤ U.Etale` between the small étale sites, and this
file defines the lower shriek functor `j_{f!}` on `A`-valued étale sheaves along this
localization functor, together with its right adjoint, the restriction functor `j_f^*`.

When `f` is moreover an open immersion (in particular a monomorphism), `j_{f!}` is the
*extension by zero* functor. It is then exact and fully faithful; fully faithfulness is
`AlgebraicGeometry.Etale.fullyFaithfulOpenImmersionLowerShriek` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`, proved from
the adjoint triple `Etale.localizationAdjunctionTriple` below.

## Main definitions

- `AlgebraicGeometry.Etale.localizationLowerShriek`: the lower shriek `j_{f!}`.
- `AlgebraicGeometry.Etale.localizationRestriction`: the restriction `j_f^*`.
- `AlgebraicGeometry.Etale.localizationLowerShriekAdjunction`: the adjunction
  `j_{f!} ⊣ j_f^*`.
- `AlgebraicGeometry.Etale.localizationRestrictionLowerStarAdjunction`: the adjunction
  `j_f^* ⊣ f_*`, completing the triple `j_{f!} ⊣ j_f^* ⊣ f_*`.
- `AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction`: for `f` étale the pullback
  `f^*` of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is computed by
  restriction, both being left adjoint to `f_*`.
- `AlgebraicGeometry.Etale.localizationLowerShriekUpperStarAdjunction`: the adjunction
  `j_{f!} ⊣ f^*`.
- `AlgebraicGeometry.Etale.localizationAdjunctionTriple`: the triple `j_{f!} ⊣ j_f^* ⊣ f_*`
  as a `CategoryTheory.Adjunction.Triple`. Via
  `CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit` this is what makes `j_{f!}`
  fully faithful as soon as `f_*` is.
- `AlgebraicGeometry.Etale.localizationLowerShriekPresheaf` and
  `AlgebraicGeometry.Etale.localizationLowerShriekPresheafAdjunction`: the presheaf-level
  Kan extension `j_{f,!}^{pre}` and its adjunction with restriction.
- `AlgebraicGeometry.Etale.openImmersionLowerShriek`: the lower shriek `j_!` along an open
  immersion `j`, with scoped notation `(j)_!open[A]`, whose `open` keeps it apart from
  `AlgebraicGeometry.Etale.lowerShriek` along a morphism admitting a compactification.
- `AlgebraicGeometry.Etale.openImmersionRestriction`: the restriction `j^*` along an open
  immersion `j`, given objectwise by `(j^* G)(T → U) = G(T → U → X)`.
- `AlgebraicGeometry.Etale.upperStarIsoOpenImmersionRestriction`: the pullback `j^*` of
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is computed by restriction.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`: the adjunction
  `j_! ⊣ j^*` between the lower shriek and the pullback `Etale.upperStar`.

## Main results

- `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek` and
  `AlgebraicGeometry.Etale.preservesFiniteColimits_openImmersionLowerShriek`: the lower
  shriek `j_!` is exact when `j` is an open immersion. The left exactness of the
  presheaf-level lower shriek is
  `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overMap` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

## Implementation notes

- `j_{f!}` is defined as the left Kan extension along `(MorphismProperty.Over.map ⊤ h).op`
  on presheaves followed by sheafification; this holds definitionally, see
  `localizationLowerShriek_eq`. For a monomorphism `f` — in particular for an open
  immersion — no Kan extension existence hypothesis is needed: the indexing comma
  categories are either empty or admit a terminal object, so both the existence and the
  left exactness of the presheaf-level left Kan extension are provided by the instances of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
- `j_f^*` restricts along the localization functor, so it requires `Etale f`, but it needs
  neither Kan extensions nor sheafification. The pullback `Etale.upperStar` of
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is defined for an arbitrary
  morphism at the cost of both; the two agree for an étale `f`, by
  `upperStarIsoLocalizationRestriction`.
- The continuity and cocontinuity of the localization functor are the `P = Q = @Etale` case
  of `AlgebraicGeometry.Scheme.isContinuous_overMap` and
  `AlgebraicGeometry.Scheme.isCocontinuous_overMap`.
-/

@[expose] public section

universe w u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : Etale f)

section LowerShriek

variable [Mono f]

/-- The lower shriek `j_{f!}` along an étale `f : V ⟶ U`: left Kan extension on presheaves
followed by sheafification, left adjoint to `Etale.localizationRestriction`. -/
noncomputable def Etale.localizationLowerShriek :
    Sheaf V.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h) A
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

end LowerShriek

section Restriction

/-- The restriction functor `j_f^*` along an étale `f : V ⟶ U`, given objectwise by
`(j_f^* G)(T → V) = G(T → V → U)`. The continuity of the localization functor is the
`P = Q = @Etale` case of `AlgebraicGeometry.Scheme.isContinuous_overMap`. -/
def Etale.localizationRestriction :
    Sheaf U.smallEtaleTopology A ⥤ Sheaf V.smallEtaleTopology A :=
  (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j_f^* G` over `T → V` are the sections of `G` over `T → V → U`. -/
lemma Etale.localizationRestriction_obj_val_obj (G : Sheaf U.smallEtaleTopology A)
    (b : V.Etale) :
    ((Etale.localizationRestriction A f h).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `j_f^*` acts on morphisms by whiskering along `(MorphismProperty.Over.map ⊤ h).op`. -/
lemma Etale.localizationRestriction_map_hom_app {G G' : Sheaf U.smallEtaleTopology A}
    (φ : G ⟶ G') (b : V.Etale) :
    (((Etale.localizationRestriction A f h).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

section Adjunction

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ j_f^*`. -/
noncomputable def Etale.localizationLowerShriekAdjunction :
    Etale.localizationLowerShriek A f h ⊣ Etale.localizationRestriction A f h :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

instance : (Etale.localizationLowerShriek A f h).IsLeftAdjoint :=
  (Etale.localizationLowerShriekAdjunction A f h).isLeftAdjoint

instance : (Etale.localizationRestriction A f h).IsRightAdjoint :=
  (Etale.localizationLowerShriekAdjunction A f h).isRightAdjoint

/-- The lower shriek agrees with mathlib's abstract left adjoint
`(MorphismProperty.Over.map ⊤ h).sheafPullback` of the restriction functor. -/
noncomputable def Etale.localizationLowerShriekIsoSheafPullback :
    (MorphismProperty.Over.map ⊤ h).sheafPullback A
        (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale) ≅
      Etale.localizationLowerShriek A f h :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (MorphismProperty.Over.map ⊤ h) A
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

end Adjunction

/-! ### Comparison with the pullback `f^*` -/

section UpperStar

open Etale

/-- Restriction along the localization functor is left adjoint to the pushforward `f_*`:
this is the right half of the triple `j_{f!} ⊣ j_f^* ⊣ f_*`. It is induced by the
adjunction `MorphismProperty.Over.mapPullbackAdj` between the two site functors, and in
particular requires neither Kan extensions nor sheafification. -/
noncomputable def Etale.localizationRestrictionLowerStarAdjunction :
    Etale.localizationRestriction A f h ⊣ (f)_*[A] :=
  (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f h _root_.trivial).sheafPushforwardContinuous
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

/-- For an étale `f`, the pullback `f^*` is computed by restriction along the localization
functor: both are left adjoint to `f_*`. In particular `f^*` needs no sheafification in this
case, and its sections are given by `Etale.localizationRestriction_obj_val_obj`.
(blueprint: `lem-weil-pbc-etale-inverse-image-restriction`) -/
noncomputable def Etale.upperStarIsoLocalizationRestriction :
    (f)^*[A] ≅ Etale.localizationRestriction A f h :=
  (Etale.upperStarLowerStarAdjunction A f).leftAdjointUniq
    (Etale.localizationRestrictionLowerStarAdjunction A f h)

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ f^*` between the lower shriek and the pullback, obtained from
`localizationLowerShriekAdjunction` by transporting along
`upperStarIsoLocalizationRestriction`. -/
noncomputable def Etale.localizationLowerShriekUpperStarAdjunction :
    Etale.localizationLowerShriek A f h ⊣ (f)^*[A] :=
  (Etale.localizationLowerShriekAdjunction A f h).ofNatIsoRight
    (Etale.upperStarIsoLocalizationRestriction A f h).symm

/-- The adjoint triple `j_{f!} ⊣ j_f^* ⊣ f_*` on étale sheaves, bundling
`localizationLowerShriekAdjunction` and `localizationRestrictionLowerStarAdjunction`. -/
noncomputable def Etale.localizationAdjunctionTriple :
    Adjunction.Triple (Etale.localizationLowerShriek A f h)
      (Etale.localizationRestriction A f h) (f)_*[A] where
  adj₁ := Etale.localizationLowerShriekAdjunction A f h
  adj₂ := Etale.localizationRestrictionLowerStarAdjunction A f h

end UpperStar

end Restriction

/-! ### The presheaf-level lower shriek -/

section Presheaf

variable [Mono f]

/-- The presheaf-level lower shriek `j_{f,!}^{pre}`: left Kan extension along
`(MorphismProperty.Over.map ⊤ h).op`. -/
noncomputable def Etale.localizationLowerShriekPresheaf :
    (V.Etaleᵒᵖ ⥤ A) ⥤ (U.Etaleᵒᵖ ⥤ A) :=
  (MorphismProperty.Over.map ⊤ h).op.lan

/-- The presheaf-level adjunction between `j_{f,!}^{pre}` and restriction. -/
noncomputable def Etale.localizationLowerShriekPresheafAdjunction :
    Etale.localizationLowerShriekPresheaf A f h ⊣
      (Functor.whiskeringLeft V.Etaleᵒᵖ U.Etaleᵒᵖ A).obj (MorphismProperty.Over.map ⊤ h).op :=
  (MorphismProperty.Over.map ⊤ h).op.lanAdjunction A

/-- The lower shriek is definitionally the left Kan extension on presheaves followed by
sheafification. -/
lemma Etale.localizationLowerShriek_eq :
    Etale.localizationLowerShriek A f h =
      sheafToPresheaf V.smallEtaleTopology A ⋙
        Etale.localizationLowerShriekPresheaf A f h ⋙
          presheafToSheaf U.smallEtaleTopology A :=
  rfl

end Presheaf

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open Etale

/-- The restriction `j^*` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites, given objectwise by `(j^* G)(T → U) = G(T → U → X)`. In contrast to
`Etale.upperStar` it requires neither Kan extensions nor sheafification. -/
def Etale.openImmersionRestriction :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  Etale.localizationRestriction A j inferInstance

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j^* G` over `T → U` are the sections of `G` over `T → U → X`. -/
lemma Etale.openImmersionRestriction_obj_val_obj (G : Sheaf X.smallEtaleTopology A)
    (b : U.Etale) :
    ((Etale.openImmersionRestriction A j).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).obj b)) :=
  rfl

/-- Restriction along an open immersion is left adjoint to the pushforward `j_*`: this is
the right half of the triple `j_! ⊣ j^* ⊣ j_*`. -/
noncomputable def Etale.openImmersionRestrictionLowerStarAdjunction :
    Etale.openImmersionRestriction A j ⊣ (j)_*[A] :=
  Etale.localizationRestrictionLowerStarAdjunction A j inferInstance

/-- The counit of the adjunction `j^* ⊣ j_*` along an open immersion `j` is an
isomorphism: the restriction of a pushforward along an open immersion is the original
sheaf. This holds since `j` is a monomorphism, so the unit of the site-level adjunction
`MorphismProperty.Over.mapPullbackAdj` is an isomorphism. -/
instance Etale.isIso_openImmersionRestrictionLowerStarAdjunction_counit :
    IsIso (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit :=
  Adjunction.isIso_sheafPushforwardContinuous_counit A
    (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial)
    (U.smallGrothendieckTopology (Q := @Etale) @Etale)
    (X.smallGrothendieckTopology (Q := @Etale) @Etale)

/-- The restriction `j^*` along an open immersion on étale sheaves is additive. -/
instance Etale.openImmersionRestriction_additive :
    (Etale.openImmersionRestriction A j).Additive where

/-- The restriction `j^*` along an open immersion on étale sheaves with values in a `Λ`-linear
category is `Λ`-linear. -/
instance Etale.openImmersionRestriction_linear (Λ : Type*) [Semiring Λ] [Linear Λ A] :
    (Etale.openImmersionRestriction A j).Linear Λ where

namespace Etale

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--7`: Extension by zero for
open immersions

The lower shriek `j_!` along an open immersion `j : U ⟶ X` on sheaves for the small
étale sites: the left adjoint of the restriction `j^*`
(`AlgebraicGeometry.Etale.localizationLowerShriek`). Its geometric stalks are those of `F` at
points of `U` (`AlgebraicGeometry.Etale.openImmersionLowerShriekCompUliftSheafFiberIso`) and
zero elsewhere (`AlgebraicGeometry.Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj`). -/
noncomputable def openImmersionLowerShriek :
    Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  Etale.localizationLowerShriek A j inferInstance

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open[" A "]" =>
  openImmersionLowerShriek A j

end Etale

/-- The adjunction `j_! ⊣ j^*` between the extension by zero and the restriction along an
open immersion. -/
noncomputable def Etale.openImmersionLowerShriekAdjunction :
    (j)_!open[A] ⊣ Etale.openImmersionRestriction A j :=
  Etale.localizationLowerShriekAdjunction A j inferInstance

instance : (j)_!open[A].IsLeftAdjoint :=
  (Etale.openImmersionLowerShriekAdjunction A j).isLeftAdjoint

instance : (Etale.openImmersionRestriction A j).IsRightAdjoint :=
  (Etale.openImmersionLowerShriekAdjunction A j).isRightAdjoint

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in a
preadditive category is additive, being left adjoint to the additive restriction `j^*`. -/
instance Etale.openImmersionLowerShriek_additive : (j)_!open[A].Additive :=
  (Etale.openImmersionLowerShriekAdjunction A j).left_adjoint_additive

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in a
`Λ`-linear category is `Λ`-linear, being left adjoint to the `Λ`-linear restriction `j^*`. -/
instance Etale.openImmersionLowerShriek_linear (Λ : Type*) [Semiring Λ] [Linear Λ A] :
    (j)_!open[A].Linear Λ :=
  (Etale.openImmersionLowerShriekAdjunction A j).left_adjoint_linear

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in an
abelian category is exact. This is the left exactness half.

`j_!` is the presheaf-level left Kan extension followed by sheafification, and both factors
are left exact: the first by
`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overMap`, the second by
the left exactness of sheafification, which is the content of `HasSheafify` beyond the
`HasWeakSheafify` needed to define `j_!`; both are provided for the Grothendieck abelian
coefficient category `A`, the second by the instance of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. -/
instance Etale.preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open[A] := by
  have heq : (j)_!open[A] =
      sheafToPresheaf U.smallEtaleTopology A ⋙
        Etale.localizationLowerShriekPresheaf A j inferInstance ⋙
          presheafToSheaf X.smallEtaleTopology A :=
    rfl
  have hlan : PreservesFiniteLimits (Etale.localizationLowerShriekPresheaf A j inferInstance) :=
    Etale.preservesFiniteLimits_op_lan_overMap A inferInstance
  rw [heq]
  exact comp_preservesFiniteLimits _ _

/-- Together with `Etale.preservesFiniteLimits_openImmersionLowerShriek` this
makes `j_!` exact. -/
example : PreservesFiniteColimits (j)_!open[A] :=
  inferInstance

/-- For an open immersion `j`, the pullback `j^*` of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is computed by restriction along the
localization functor: both are left adjoint to `j_*`. In particular its sections are given
by `Etale.openImmersionRestriction_obj_val_obj`. -/
noncomputable def Etale.upperStarIsoOpenImmersionRestriction :
    (j)^*[A] ≅ Etale.openImmersionRestriction A j :=
  Etale.upperStarIsoLocalizationRestriction A j inferInstance

/-- The adjunction `j_! ⊣ j^*` between the lower shriek along an open immersion and the
pullback `Etale.upperStar`. (blueprint: `lem-weil-pbc-extension-by-zero-adjunction`) -/
noncomputable def Etale.openImmersionLowerShriekUpperStarAdjunction :
    (j)_!open[A] ⊣ (j)^*[A] :=
  Etale.localizationLowerShriekUpperStarAdjunction A j inferInstance

/-- The adjoint triple `j_! ⊣ j^* ⊣ j_*` on small étale sites along an open immersion. -/
noncomputable def Etale.openImmersionAdjunctionTriple :
    Adjunction.Triple (j)_!open[A] (Etale.openImmersionRestriction A j) (j)_*[A] :=
  Etale.localizationAdjunctionTriple A j inferInstance

end OpenImmersion

end AlgebraicGeometry
