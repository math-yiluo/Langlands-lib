/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The pushforward `g_*` and the pullback `g^*` on small pro-étale sites

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, for mathlib's pro-étale site
`AlgebraicGeometry.Scheme.ProEt.topology`: the topology on the category `X.ProEt` of
weakly étale schemes over `X` whose covers are the pro-étale covers of
[Bhatt–Scholze, Definition 4.1.1], that is, the fpqc covers by weakly étale morphisms.

For an *arbitrary* morphism of schemes `g : Z ⟶ Y`, base change induces the functor
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ g : Y.ProEt ⥤ Z.ProEt` between the small
pro-étale sites, and composition with it defines the pushforward `g_*` on `A`-valued
pro-étale sheaves. Its left adjoint `g^*` is the left Kan extension on presheaves followed
by sheafification.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStar`: the pushforward `g_*`, given by composition with
  the base change functor, with scoped notation `(g)_*[A]`.
- `AlgebraicGeometry.ProEtale.upperStar`: the pullback `g^*`, given by left Kan extension
  on presheaves followed by sheafification, with scoped notation `(g)^*[A]`.
- `AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.ProEtale.lowerStarId` and `AlgebraicGeometry.ProEtale.upperStarId`: the
  identity isomorphisms `(𝟙 X)_* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`, the latter obtained from the former
  by uniqueness of left adjoints.
- `AlgebraicGeometry.ProEtale.lowerStarComp` and
  `AlgebraicGeometry.ProEtale.upperStarComp`: the composition isomorphisms
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter
  obtained from the former by uniqueness of left adjoints.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`: base change along an
  arbitrary morphism is continuous for the pro-étale topologies. It preserves covers since
  pro-étale covers are stable under base change, and it preserves compatible families since
  it is representably flat, being a finite-limit-preserving functor on the finitely
  complete pro-étale slice. It is proved in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`, and it is what makes
  `ProEtale.lowerStar` carry no hypotheses at all.
- `AlgebraicGeometry.ProEtale.isLeftAdjoint_op_overPullback` and
  `AlgebraicGeometry.ProEtale.hasPointwiseLeftKanExtension_op_overPullback`: for `g` weakly
  étale, the opposite of base change is a left adjoint — base change is right adjoint to
  the localization functor `MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›` — and all pointwise
  left Kan extensions along it exist. For a general `g` the pointwise left Kan extensions
  instead exist by essential `u + 1`-smallness of the indexing comma categories,
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, with no smallness of
  the small pro-étale site itself.
- `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_lowerStar` and
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerStar`: the pushforward `g_*`
  preserves every limit that exists in the coefficient category. This needs no hypothesis
  beyond the continuity of the base change functor, in particular it does not use the
  adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback` and
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar`: the pullback `g^*` is left
  exact, hence exact, being also a left adjoint. In contrast to `g_*` this is not
  automatic: it needs sheafification to be left exact and the left Kan extension along the
  opposite of base change to be so as well. For a weakly étale `g` the latter is proved
  here, the Kan extension being precomposition with a right adjoint; for a general `g` it is
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`.

## Implementation notes

- The coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
  universe `u + 1`, one above the universe `u` of the base schemes, following the
  convention of the `SixFunctors` folder.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, which
  requires `WeaklyEtale g`. This is essential for compactifications, whose structure morphism is
  proper and in general is not weakly étale.
- Sheafification on the small pro-étale sites and the left Kan extensions along the
  opposite of base change both hold for every Grothendieck abelian `A`, so
  `ProEtale.upperStar` and the adjunction `g^* ⊣ g_*` carry no hypotheses either.
  Sheafification is
  `CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, provided through
  `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` there, and it does
  use essential smallness of the site. The Kan extensions are proved and use no smallness
  of the site at all, only of the indexing comma categories, see
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

section KanExtension

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]

/-- For a weakly étale morphism `g`, base change is right adjoint to the localization
functor `MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›`, hence its opposite is a left
adjoint. -/
instance ProEtale.isLeftAdjoint_op_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.IsLeftAdjoint :=
  ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g ‹WeaklyEtale g›
    _root_.trivial).op).isLeftAdjoint

/-- For a weakly étale morphism `g`, the opposite of base change is a left adjoint by
`ProEtale.isLeftAdjoint_op_overPullback`, so the indexing comma categories of the pointwise
left Kan extensions along it have terminal objects. In particular all pointwise left Kan
extensions along it exist. -/
instance ProEtale.hasPointwiseLeftKanExtension_op_overPullback (F : Y.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.HasPointwiseLeftKanExtension F := by
  intro V
  have : HasTerminal
      (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op V) :=
    (mkTerminalOfRightAdjoint _
      (Adjunction.ofIsLeftAdjoint
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op) V).hasTerminal
  infer_instance

/-- For a weakly étale morphism `g`, the left Kan extension along the opposite of base
change is precomposition with the opposite of the localization functor
`MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›`, hence preserves all limits that exist in the
coefficient category. This is what makes the pullback `g^*` left exact without any
smallness or concreteness assumption on `A`; compare
`CategoryTheory.lan_preservesFiniteLimits_of_flat`. -/
instance ProEtale.preservesFiniteLimits_op_lan_overPullback :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan :
      (Y.ProEtᵒᵖ ⥤ A) ⥤ Z.ProEtᵒᵖ ⥤ A) :=
  inferInstance

end KanExtension

section Star

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

namespace ProEtale

/-- The pushforward `g_*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
pro-étale sites, given objectwise by `(g_* G)(V → Y) = G(V ×_Y Z → Z)`. The continuity of
the base change functor is `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`. -/
noncomputable def lowerStar :
    Sheaf (Scheme.ProEt.topology Z) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

@[inherit_doc ProEtale.lowerStar]
scoped notation "(" g ")_*[" A "]" =>
  lowerStar A g

end ProEtale

open ProEtale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `g_* G` over `V → Y` are the sections of `G` over `V ×_Y Z → Z`. -/
lemma ProEtale.lowerStar_obj_val_obj (G : Sheaf (Scheme.ProEt.topology Z) A) (b : Y.ProEt) :
    ((g)_*[A].obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along
`(MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op`. -/
lemma ProEtale.lowerStar_map_hom_app {G G' : Sheaf (Scheme.ProEt.topology Z) A} (φ : G ⟶ G')
    (b : Y.ProEt) :
    (((g)_*[A].map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj b)) :=
  rfl

/-- The pushforward `g_*` on pro-étale sheaves with values in a preadditive category is
additive: it acts on morphisms by whiskering, which is compatible with the objectwise
addition. -/
instance ProEtale.lowerStar_additive : (g)_*[A].Additive where

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance ProEtale.preservesLimitsOfShape_lowerStar (E : Type*) [Category E]
    [HasLimitsOfShape E A] : PreservesLimitsOfShape E (g)_*[A] :=
  inferInstanceAs (PreservesLimitsOfShape E
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)))

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`. -/
instance ProEtale.preservesFiniteLimits_lowerStar : PreservesFiniteLimits (g)_*[A] :=
  inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)))

section Adjunction

namespace ProEtale

/-- The pullback `g^*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
pro-étale sites: left Kan extension on presheaves followed by sheafification, left adjoint
to `ProEtale.lowerStar`. The Kan extensions are provided by
`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, and the sheafification by
`CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, which is proved
through `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall`. For `g`
weakly étale the Kan extension hypothesis is automatic by
`ProEtale.hasPointwiseLeftKanExtension_op_overPullback`, and `g^*` is computed by
restriction, see `ProEtale.upperStarIsoOpenImmersionRestriction`. -/
noncomputable def upperStar :
    Sheaf (Scheme.ProEt.topology Y) A ⥤ Sheaf (Scheme.ProEt.topology Z) A :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

@[inherit_doc ProEtale.upperStar]
scoped notation "(" g ")^*[" A "]" =>
  upperStar A g

end ProEtale

/-- The adjunction `g^* ⊣ g_*` on sheaves for the small pro-étale sites. -/
noncomputable def ProEtale.upperStarLowerStarAdjunction : (g)^*[A] ⊣ (g)_*[A] :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

instance : (g)_*[A].IsRightAdjoint :=
  (ProEtale.upperStarLowerStarAdjunction A g).isRightAdjoint

instance : (g)^*[A].IsLeftAdjoint :=
  (ProEtale.upperStarLowerStarAdjunction A g).isLeftAdjoint

/-- The pullback `g^*` on pro-étale sheaves is left exact, hence exact, being also a left
adjoint: `g^*` is the composite of the inclusion of sheaves into presheaves, which preserves
finite limits, the left Kan extension along the opposite of base change, and sheafification,
which is left exact by `HasSheafify`. The left exactness of the Kan extension is
`ProEtale.preservesFiniteLimits_op_lan_overPullback` for a weakly étale `g`, and in general
`ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`, the Kan
extension being a filtered colimit and filtered colimits in the Grothendieck abelian `A`
being exact. -/
instance ProEtale.preservesFiniteLimits_upperStar
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan :
      (Y.ProEtᵒᵖ ⥤ A) ⥤ Z.ProEtᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (g)^*[A] := by
  unfold ProEtale.upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

/-- The pullback `g^*` on pro-étale sheaves is right exact, being a left adjoint. -/
example : PreservesFiniteColimits (g)^*[A] := inferInstance

/-- The pullback `g^*` on pro-étale sheaves is additive, being a left adjoint. -/
instance ProEtale.additive_upperStar : (g)^*[A].Additive :=
  (ProEtale.upperStarLowerStarAdjunction A g).left_adjoint_additive

/-- The pullback `g^*` on pro-étale sheaves preserves homology, being exact: it preserves
finite limits by `ProEtale.preservesFiniteLimits_upperStar` and all colimits of size `0`,
being a left adjoint. -/
instance ProEtale.preservesHomology_upperStar : (g)^*[A].PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (g)^*[A] :=
    (ProEtale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits
  -- the two fields of `PreservesHomology` are `autoParam`s, found by instance synthesis
  -- from `ProEtale.preservesFiniteLimits_upperStar` and from `this`
  exact {}

end Adjunction

end Star

section Id

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

open ProEtale

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of the pushforward on pro-étale sheaves: base
change along `𝟙 X` is the identity functor by `MorphismProperty.Over.pullbackId`. This is
the pro-étale counterpart of `AlgebraicGeometry.Etale.lowerStarId`. -/
noncomputable def ProEtale.lowerStarId : (𝟙 X)_*[A] ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) A
    (Scheme.ProEt.topology X)

/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback on pro-étale sheaves, obtained
from `ProEtale.lowerStarId` by uniqueness of left adjoints: both sides are left adjoint to
`(𝟙 X)_*`. This is the pro-étale counterpart of `AlgebraicGeometry.Etale.upperStarId`. -/
noncomputable def ProEtale.upperStarId : (𝟙 X)^*[A] ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X))).symm
    (lowerStarId A X).symm

/-- Under the conjugation bijection between the adjunctions `𝟭 ⊣ 𝟭` and `(𝟙 X)^* ⊣ (𝟙 X)_*`,
the identity isomorphism of the pullback corresponds to the inverse of the identity
isomorphism of the pushforward:

```
  (𝟙 X)^* ⊣ (𝟙 X)_*        upperStarId : (𝟙 X)^* ≅ 𝟭
      ↕ conjugate                  ↦
      𝟭 ⊣ 𝟭               lowerStarId.symm : 𝟭 ≅ (𝟙 X)_*
```

This is the pro-étale counterpart of `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarId`. -/
lemma ProEtale.conjugateIsoEquiv_upperStarId :
    conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X))
        (upperStarId A X) = (lowerStarId A X).symm :=
  Equiv.apply_symm_apply _ _

end Id

section Comp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

open ProEtale

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
pro-étale sheaves: both sides send a sheaf `G` to the sheaf `(V → R) ↦ G(V ×_R T → T)`, up
to the pullback pasting isomorphism `(V ×_R S) ×_S T ≅ V ×_R T` of
`MorphismProperty.Over.pullbackComp`. -/
noncomputable def ProEtale.lowerStarComp : (h₁)_*[A] ⋙ (h₂)_*[A] ≅ (h₁ ≫ h₂)_*[A] :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).symm) A
    (Scheme.ProEt.topology R) (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on pro-étale
sheaves, obtained from `ProEtale.lowerStarComp` by uniqueness of left adjoints: both sides
are left adjoint to `(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def ProEtale.upperStarComp : (h₁ ≫ h₂)^*[A] ≅ (h₂)^*[A] ⋙ (h₁)^*[A] :=
  ((conjugateIsoEquiv (ProEtale.upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((ProEtale.upperStarLowerStarAdjunction A h₂).comp
        (ProEtale.upperStarLowerStarAdjunction A h₁))).symm
    (ProEtale.lowerStarComp A h₁ h₂).symm).symm

end UpperStar

section Id

variable (X : Scheme.{u})

/-- Base change along the identity of `X` is the identity of the small pro-étale site of `X`,
by uniqueness of right adjoints: it is right adjoint to the localization functor along the
identity, which is the identity functor by `MorphismProperty.Over.mapId`. -/
noncomputable def ProEt.overPullbackId :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝟙 X) ≅ 𝟭 X.ProEt :=
  (conjugateIsoEquiv
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ (𝟙 X) inferInstance _root_.trivial)
    (Adjunction.id (C := X.ProEt)) (MorphismProperty.Over.mapId ⊤ X).symm)

end Id

end Comp

end AlgebraicGeometry
