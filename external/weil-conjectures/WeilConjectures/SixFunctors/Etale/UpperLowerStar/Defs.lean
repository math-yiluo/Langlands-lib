/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The pushforward `g_*` and the pullback `g^*` on small étale sites

For an *arbitrary* morphism of schemes `g : Z ⟶ Y`, base change induces the functor
`MorphismProperty.Over.pullback @Etale ⊤ g : Y.Etale ⥤ Z.Etale` between the small étale
sites, and composition with it defines the pushforward `g_*` on `A`-valued étale sheaves.
Its left adjoint `g^*` is the left Kan extension on presheaves followed by sheafification.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStar`: the pushforward `g_*`, given by composition with the
  base change functor, with scoped notation `(g)_*[A]`.
- `AlgebraicGeometry.Etale.upperStar`: the pullback `g^*`, given by left Kan extension on
  presheaves followed by sheafification, with scoped notation `(g)^*[A]`.
- `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.Etale.lowerStarComp` and `AlgebraicGeometry.Etale.upperStarComp`: the
  composition isomorphisms `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and
  `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter obtained from the former by uniqueness of
  left adjoints.
- `AlgebraicGeometry.Etale.lowerStarCompSheafSectionsTerminalIso`: sections over the terminal
  object are invariant under `g_*`, `(g_* F)(Y) = F(Y ×_Y Z) ≅ F(Z)`.

## Main results

- `AlgebraicGeometry.Etale.isContinuous_overPullback`: base change along an arbitrary
  morphism is continuous for the small étale topologies. It preserves covers since étale
  covers are stable under base change, and it preserves compatible families since it is
  representably flat, being a finite-limit-preserving functor on the finitely complete
  étale slice. This is the `P = Q = @Etale` case of
  `AlgebraicGeometry.Scheme.isContinuous_overPullback`; it is what makes `Etale.lowerStar`
  carry no hypotheses at all.
- `AlgebraicGeometry.Etale.isLeftAdjoint_op_overPullback` and
  `AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback`: for `g` étale, the
  opposite of base change is a left adjoint — base change is right adjoint to the
  localization functor `MorphismProperty.Over.map ⊤ ‹Etale g›` — and all pointwise left Kan
  extensions along it exist. For a general `g` the pointwise left Kan extensions instead
  exist by essential `u + 1`-smallness of the indexing comma categories,
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, with no smallness of
  the small étale site itself.
- `AlgebraicGeometry.Etale.preservesLimitsOfShape_lowerStar` and
  `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerStar`: the pushforward `g_*` preserves
  every limit that exists in the coefficient category. This needs no hypothesis beyond the
  continuity of the base change functor, in particular it does not use the adjunction
  `g^* ⊣ g_*`.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` and
  `AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar`: the pullback `g^*` is left
  exact, hence exact, being also a left adjoint. In contrast to `g_*` this is not
  automatic: it needs sheafification to be left exact and the left Kan extension along the
  opposite of base change to be so as well. For an étale `g` the latter is proved here, the
  Kan extension being precomposition with a right adjoint; for a general `g` it is
  `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`.

## Implementation notes

- The coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
  universe `u + 1`, one above the universe `u` of the base schemes, following the
  convention of the `SixFunctors` folder.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, which requires
  `Etale g`. This is essential for compactifications, whose structure morphism is proper
  and in general is not étale.
- Sheafification on the small étale sites and the left Kan extensions along the opposite
  of base change both hold for every Grothendieck abelian `A`, so `Etale.upperStar` and the
  adjunction `g^* ⊣ g_*` carry no hypotheses either. Sheafification is
  `CategoryTheory.GrothendieckTopology.hasSheafify_smallEtaleTopology` of
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

section Continuity

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Base change along an arbitrary morphism `g : Z ⟶ Y` is continuous for the small étale
topologies. This is the `P = Q = @Etale` case of
`AlgebraicGeometry.Scheme.isContinuous_overPullback`.
(blueprint: `situation-conventions`) -/
instance Etale.isContinuous_overPullback :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale) :=
  Scheme.isContinuous_overPullback @Etale @Etale le_rfl g

end Continuity

section KanExtension

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Etale g]

/-- For an étale morphism `g`, base change is right adjoint to the localization functor
`MorphismProperty.Over.map ⊤ ‹Etale g›`, hence its opposite is a left adjoint. -/
instance Etale.isLeftAdjoint_op_overPullback :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.IsLeftAdjoint :=
  ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g ‹Etale g› _root_.trivial).op).isLeftAdjoint

/-- For an étale morphism `g`, the opposite of base change is a left adjoint by
`Etale.isLeftAdjoint_op_overPullback`, so the indexing comma categories of the pointwise
left Kan extensions along it have terminal objects. In particular all pointwise left Kan
extensions along it exist. -/
instance Etale.hasPointwiseLeftKanExtension_op_overPullback (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasPointwiseLeftKanExtension F := by
  intro V
  have : HasTerminal (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op V) :=
    (mkTerminalOfRightAdjoint _
      (Adjunction.ofIsLeftAdjoint (MorphismProperty.Over.pullback @Etale ⊤ g).op) V).hasTerminal
  infer_instance

/-- For an étale morphism `g`, the left Kan extension along the opposite of base change is
precomposition with the opposite of the localization functor `MorphismProperty.Over.map ⊤
‹Etale g›`, hence preserves all limits that exist in the coefficient category. This is what
makes the pullback `g^*` left exact without any smallness or concreteness assumption on `A`;
compare `CategoryTheory.lan_preservesFiniteLimits_of_flat`. -/
instance Etale.preservesFiniteLimits_op_lan_overPullback :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  inferInstance

end KanExtension

section Star

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

namespace Etale

/-- The pushforward `g_*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
étale sites, given objectwise by `(g_* G)(V → Y) = G(V ×_Y Z → Z)`. The continuity of the
base change functor is `Etale.isContinuous_overPullback`
(blueprint: `def-weil-pbc-direct-image`, `situation-conventions`) -/
noncomputable def lowerStar :
    Sheaf Z.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  (MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous A
    (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)

@[inherit_doc Etale.lowerStar]
scoped notation "(" g ")_*[" A "]" =>
  lowerStar A g

end Etale

open Etale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `g_* G` over `V → Y` are the sections of `G` over `V ×_Y Z → Z`. -/
lemma Etale.lowerStar_obj_val_obj (G : Sheaf Z.smallEtaleTopology A) (b : Y.Etale) :
    ((g)_*[A].obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction maps of `g_* G` are those of `G` along the base changes of the morphisms. -/
lemma Etale.lowerStar_obj_val_map (G : Sheaf Z.smallEtaleTopology A) {b b' : Y.Etale}
    (φ : b ⟶ b') :
    ((g)_*[A].obj G).obj.map φ.op =
      G.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ).op :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback @Etale ⊤ g).op`. -/
lemma Etale.lowerStar_map_hom_app {G G' : Sheaf Z.smallEtaleTopology A} (φ : G ⟶ G')
    (b : Y.Etale) :
    (((g)_*[A].map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) :=
  rfl

/-- The pushforward `g_*` on étale sheaves with values in a preadditive category is
additive: it acts on morphisms by whiskering, which is compatible with the objectwise
addition. -/
instance Etale.lowerStar_additive : (g)_*[A].Additive where

/-- The pushforward `g_*` on étale sheaves with values in a `Λ`-linear category is `Λ`-linear:
it acts on morphisms by whiskering, which is compatible with the objectwise scalar
multiplication. -/
instance Etale.lowerStar_linear (Λ : Type*) [Semiring Λ] [Linear Λ A] : (g)_*[A].Linear Λ where

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance Etale.preservesLimitsOfShape_lowerStar (E : Type*) [Category E]
    [HasLimitsOfShape E A] : PreservesLimitsOfShape E (g)_*[A] :=
  inferInstanceAs (PreservesLimitsOfShape E
    ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous A
      (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)))

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`. -/
instance Etale.preservesFiniteLimits_lowerStar : PreservesFiniteLimits (g)_*[A] :=
  inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous A
      (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)))

section Adjunction

namespace Etale

/-- The pullback `g^*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
étale sites: left Kan extension on presheaves followed by sheafification, left adjoint to
`Etale.lowerStar`. The Kan extensions are provided by
`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, and the sheafification by
`CategoryTheory.GrothendieckTopology.hasSheafify_smallEtaleTopology` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, which is proved
through `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall`. For `g` étale
the Kan extension hypothesis is automatic by
`Etale.hasPointwiseLeftKanExtension_op_overPullback`, and `g^*` is computed by restriction,
see `Etale.upperStarIsoOpenImmersionRestriction`. -/
noncomputable def upperStar :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback @Etale ⊤ g) A
    (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)

@[inherit_doc Etale.upperStar]
scoped notation "(" g ")^*[" A "]" =>
  upperStar A g

end Etale

/-- The adjunction `g^* ⊣ g_*` on sheaves for the small étale sites
(blueprint: `def-weil-pbc-inverse-image`, `situation-conventions`,
`situation-conventions`) -/
noncomputable def Etale.upperStarLowerStarAdjunction : (g)^*[A] ⊣ (g)_*[A] :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ g) A
    (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)

instance : (g)_*[A].IsRightAdjoint :=
  (Etale.upperStarLowerStarAdjunction A g).isRightAdjoint

instance : (g)^*[A].IsLeftAdjoint :=
  (Etale.upperStarLowerStarAdjunction A g).isLeftAdjoint

/-- The pullback `g^*` on étale sheaves is left exact, hence exact, being also a left
adjoint: `g^*` is the composite of the inclusion of sheaves into presheaves, which preserves
finite limits, the left Kan extension along the opposite of base change, and sheafification,
which is left exact by `HasSheafify`. The left exactness of the Kan extension is
`Etale.preservesFiniteLimits_op_lan_overPullback` for an étale `g`, and in general
`Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`, the Kan
extension being a filtered colimit and filtered colimits in the Grothendieck abelian `A`
being exact. -/
instance Etale.preservesFiniteLimits_upperStar
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (g)^*[A] := by
  unfold Etale.upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

/-- The pullback `g^*` on étale sheaves is right exact, being a left adjoint. -/
example : PreservesFiniteColimits (g)^*[A] := inferInstance

/-- The pullback `g^*` on étale sheaves is additive, being a left adjoint. -/
instance Etale.additive_upperStar : (g)^*[A].Additive :=
  (Etale.upperStarLowerStarAdjunction A g).left_adjoint_additive

/-- The pullback `g^*` on étale sheaves with values in a `Λ`-linear category is `Λ`-linear,
being left adjoint to the `Λ`-linear pushforward `g_*`. -/
instance Etale.linear_upperStar (Λ : Type*) [Semiring Λ] [Linear Λ A] : (g)^*[A].Linear Λ :=
  (Etale.upperStarLowerStarAdjunction A g).left_adjoint_linear

/-- The pullback `g^*` on étale sheaves preserves homology, being exact: it preserves
finite limits by `Etale.preservesFiniteLimits_upperStar` and all colimits of size `0`,
being a left adjoint. (blueprint: `situation-conventions`) -/
instance Etale.preservesHomology_upperStar : (g)^*[A].PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (g)^*[A] :=
    (Etale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits
  -- the two fields of `PreservesHomology` are `autoParam`s, found by instance synthesis
  -- from `Etale.preservesFiniteLimits_upperStar` and from `this`
  exact {}

end Adjunction

end Star

section Comp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

open Etale

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on étale
sheaves: both sides send a sheaf `G` to the sheaf `(V → R) ↦ G(V ×_R T → T)`, up to the
pullback pasting isomorphism `(V ×_R S) ×_S T ≅ V ×_R T` of
`MorphismProperty.Over.pullbackComp`. (blueprint: `lem-weil-pbc-inverse-image-composition`) -/
noncomputable def Etale.lowerStarComp (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) : (h₁)_*[A] ⋙ (h₂)_*[A] ≅ (h₁₂)_*[A] :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h₁ h₂ h₁₂ hh₁₂).symm) A
    (R.smallGrothendieckTopology @Etale) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁₂)_*` of étale
pushforwards are the restriction maps along the pullback pasting isomorphisms. -/
lemma Etale.lowerStarComp_hom_app_hom_app (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf T.smallEtaleTopology A) (V : R.Etaleᵒᵖ) :
    ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂ h₁₂ hh₁₂).hom.app V.unop).op := by
  simp only [Etale.lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the inverse of the composition isomorphism
`(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*`. -/
lemma Etale.lowerStarComp_inv_app_hom_app (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf T.smallEtaleTopology A) (V : R.Etaleᵒᵖ) :
    ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂ h₁₂ hh₁₂).inv.app V.unop).op := by
  simp only [Etale.lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on étale
sheaves, obtained from `Etale.lowerStarComp` by uniqueness of left adjoints: both sides are
left adjoint to `(h₁)_* ⋙ (h₂)_*`. (blueprint: `lem-weil-pbc-inverse-image-composition`) -/
noncomputable def Etale.upperStarComp (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) : (h₁₂)^*[A] ≅ (h₂)^*[A] ⋙ (h₁)^*[A] :=
  ((conjugateIsoEquiv (Etale.upperStarLowerStarAdjunction A h₁₂)
      ((Etale.upperStarLowerStarAdjunction A h₂).comp
        (Etale.upperStarLowerStarAdjunction A h₁))).symm
    (Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).symm).symm

end UpperStar

end Comp

section Sections

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Sections over the terminal object are invariant under the pushforward along `g : Z ⟶ Y`:
`(g_* F)(Y) = F(Y ×_Y Z) ≅ F(Z)`, since base change preserves the terminal object of the small
étale site. -/
noncomputable def Etale.lowerStarCompSheafSectionsTerminalIso :
    Etale.lowerStar A g ⋙ (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)) ≅
      (sheafSections Z.smallEtaleTopology A).obj (op (⊤_ Z.Etale)) :=
  NatIso.ofComponents (fun H ↦ H.obj.mapIso (PreservesTerminal.iso g.Etale).op.symm)
    (fun α ↦ (α.hom.naturality _).symm)

end Sections

end AlgebraicGeometry
