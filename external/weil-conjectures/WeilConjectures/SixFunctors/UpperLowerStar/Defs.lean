/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The pushforward `g_*` and the pullback `g^*` on small sites of schemes

Let `P` and `Q` be morphism properties of schemes. For an *arbitrary* morphism of schemes
`g : W ⟶ U`, base change induces the functor
`MorphismProperty.Over.pullback P ⊤ g : P.Over ⊤ U ⥤ P.Over ⊤ W` between the small sites,
and composition with it defines the pushforward `g_*` on `A`-valued sheaves for the small
`Q`-topologies. Its left adjoint `g^*` is the left Kan extension on presheaves followed by
sheafification.

## Main definitions

- `CategoryTheory.GrothendieckTopology.lowerStar`: the pushforward `g_*`, given by
  composition with the base change functor.
- `CategoryTheory.GrothendieckTopology.upperStar`: the pullback `g^*`, given by left Kan
  extension on presheaves followed by sheafification.
- `CategoryTheory.GrothendieckTopology.upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*`.
- `CategoryTheory.GrothendieckTopology.lowerStarComp` and
  `CategoryTheory.GrothendieckTopology.upperStarComp`: the composition isomorphisms
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter
  obtained from the former by uniqueness of left adjoints.
- `CategoryTheory.GrothendieckTopology.lowerStarId` and
  `CategoryTheory.GrothendieckTopology.upperStarId`: the identity isomorphisms
  `(𝟙 V)_* ≅ 𝟭` and `(𝟙 V)^* ≅ 𝟭`, again the latter obtained from the former.

## Main results

- `CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_lowerStar` and
  `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_lowerStar`: the pushforward
  `g_*` preserves every limit that exists in the coefficient category. This needs no
  hypothesis beyond the continuity of the base change functor, in particular it does not
  use the adjunction `g^* ⊣ g_*`.
- `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_upperStar`: the pullback `g^*`
  is left exact, provided sheafification is and the left Kan extension along the opposite
  of the base change functor is. In contrast to `g_*` this is not automatic; see
  `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an
  étale morphism, where the Kan extension is precomposition with a right adjoint.
- `CategoryTheory.GrothendieckTopology.lowerStarComp_id_left`,
  `CategoryTheory.GrothendieckTopology.lowerStarComp_id_right` and
  `CategoryTheory.GrothendieckTopology.lowerStarComp_assoc`, together with their `upperStar`
  counterparts: the unit and associativity laws, which make `V ↦ Sheaf V` a pseudofunctor in
  all but name, both for the pushforwards and for the pullbacks.
- `CategoryTheory.GrothendieckTopology.conjugateIsoEquiv_upperStarComp` and
  `CategoryTheory.GrothendieckTopology.conjugateIsoEquiv_upperStarId`: the composition and
  identity isomorphisms of the pullbacks correspond to those of the pushforwards under
  conjugation along the adjunctions `g^* ⊣ g_*`. These transport each law for `lowerStar` to
  the corresponding law for `upperStar`.

## Implementation notes

- The coefficient category `A` is a Grothendieck abelian category with small site
  coefficients (`CategoryTheory.HasSmallSiteSheafify`, supplying sheafification on the
  small sites) and `Hom`-types in the universe `u + 1`, one above the universe `u` of the
  base schemes, following the convention of the `SixFunctors` folder.
- The composition isomorphisms take the composite `h₁ ≫ h₂` as an optional argument,
  exactly as `MorphismProperty.Over.pullbackComp` does. This is what lets the unit laws be
  stated for `𝟙 S ≫ h₂` and `h₁ ≫ 𝟙 S` without an `eqToIso`, and lets a single associativity
  statement cover both bracketings of `f ≫ g ≫ h`.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`, which requires `P g`.
  This is essential for compactifications, whose structure morphism is proper and in
  general does not satisfy `P`.
- The continuity of the base change functor along an arbitrary morphism is proved, for
  `Q ≤ P`, as `AlgebraicGeometry.Scheme.isContinuous_overPullback` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`. The left Kan extensions on
  presheaves and the sheafification entering the definitions are provided, for `Q ≤ P`, by
  the folder `WeilConjectures.CategoryTheory.GrothendieckAbelian`, under the
  multiplicativity-type assumptions on `P` and `Q` assumed throughout; all of them hold
  for `P = Q = @Etale`. The inequality `hQP : Q ≤ P` is an explicit argument of
  the definitions using continuity.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace GrothendieckTopology

variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
variable (hQP : Q ≤ P)

variable {W U : Scheme.{u}} (g : W ⟶ U)

/-- The pushforward `g_*` along `g : W ⟶ U`, given objectwise by
`(g_* G)(V → U) = G(V ×_U W → W)`. The continuity of the base change functor is
`AlgebraicGeometry.Scheme.isContinuous_overPullback`. -/
noncomputable def lowerStar :
    Sheaf (W.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (U.smallGrothendieckTopology Q (Q := P)) A :=
  have := isContinuous_overPullback P Q hQP g
  (MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The sections of `g_* G` over `V → U` are the sections of `G` over `V ×_U W → W`. -/
lemma lowerStar_obj_val_obj
    (G : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ U) :
    ((lowerStar A P Q hQP g).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback P ⊤ g).op`. -/
lemma lowerStar_map_hom_app
    {G G' : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A} (φ : G ⟶ G') (b : P.Over ⊤ U) :
    (((lowerStar A P Q hQP g).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance preservesLimitsOfShape_lowerStar (E : Type*) [Category E] [HasLimitsOfShape E A] :
    PreservesLimitsOfShape E (lowerStar A P Q hQP g) :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (PreservesLimitsOfShape E
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`, which is
only available under the extra hypotheses of the section below. -/
instance preservesFiniteLimits_lowerStar :
    PreservesFiniteLimits (lowerStar A P Q hQP g) :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

section Adjunction

/-- The pullback `g^*` along `g : W ⟶ U`: left Kan extension on presheaves followed by
sheafification, left adjoint to `lowerStar`. The Kan extensions and the sheafification
are provided by the instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, the latter for `A` with
`CategoryTheory.HasSmallSiteSheafify`. -/
noncomputable def upperStar :
    Sheaf (U.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (W.smallGrothendieckTopology Q (Q := P)) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

/-- The adjunction `g^* ⊣ g_*`. -/
noncomputable def upperStarLowerStarAdjunction :
    upperStar A P Q g ⊣ lowerStar A P Q hQP g :=
  have := isContinuous_overPullback P Q hQP g
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

instance : (lowerStar A P Q hQP g).IsRightAdjoint :=
  (upperStarLowerStarAdjunction A P Q hQP g).isRightAdjoint

include hQP in
/-- `g^*` is a left adjoint. Not an instance, since its statement does not determine the
inequality `hQP : Q ≤ P` entering the adjunction `g^* ⊣ g_*`; for the small étale sites
the corresponding instance is registered in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`. -/
lemma isLeftAdjoint_upperStar : (upperStar A P Q g).IsLeftAdjoint :=
  (upperStarLowerStarAdjunction A P Q hQP g).isLeftAdjoint

/-- `g^*` is left exact as soon as the left Kan extension along the base change functor is:
`g^*` is the composite of the inclusion of sheaves into presheaves, which preserves finite
limits, that left Kan extension, and sheafification, which is left exact by
`HasSheafify`. Unlike `preservesFiniteLimits_lowerStar` this is not automatic; see
`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an étale
morphism, where the Kan extension is precomposition with a right adjoint. -/
instance preservesFiniteLimits_upperStar
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback P ⊤ g).op.lan :
      ((P.Over ⊤ U)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ W)ᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (upperStar A P Q g) := by
  unfold upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

end Adjunction

section Id

variable (V : Scheme.{u})

/-- The identity isomorphism `(𝟙 V)_* ≅ 𝟭` of the pushforward on sheaves for the small
sites: base change along `𝟙 V` is the identity functor by
`MorphismProperty.Over.pullbackId`. -/
noncomputable def lowerStarId : lowerStar A P Q hQP (𝟙 V) ≅ 𝟭 _ :=
  have := isContinuous_overPullback P Q hQP (𝟙 V)
  Functor.sheafPushforwardContinuousId' (MorphismProperty.Over.pullbackId P ⊤ V) A
    (V.smallGrothendieckTopology Q (Q := P))

/-- The identity isomorphism `(𝟙 V)^* ≅ 𝟭` of the pullback on sheaves for the small sites,
obtained from `lowerStarId` by uniqueness of left adjoints: both sides are left adjoint to
`(𝟙 V)_*`. -/
noncomputable def upperStarId : upperStar A P Q (𝟙 V) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A P Q hQP (𝟙 V))).symm
    (lowerStarId A P Q hQP V).symm

/-- Under the conjugation bijection between the adjunctions `𝟭 ⊣ 𝟭` and `(𝟙 V)^* ⊣ (𝟙 V)_*`,
the identity isomorphism of the pullback corresponds to the identity isomorphism of the
pushforward. -/
lemma conjugateIsoEquiv_upperStarId :
    conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A P Q hQP (𝟙 V))
        (upperStarId A P Q hQP V) = (lowerStarId A P Q hQP V).symm :=
  Equiv.apply_symm_apply _ _

end Id

section Comp

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
sheaves for the small sites: both sides send a sheaf `G` to the sheaf
`(V → R) ↦ G(V ×_R T → T)`, up to the pullback pasting isomorphism
`(V ×_R S) ×_S T ≅ V ×_R T` of `MorphismProperty.Over.pullbackComp`. As in
`MorphismProperty.Over.pullbackComp`, the composite `h₁ ≫ h₂` is an optional argument, so
that the isomorphism is also available for a morphism that is merely *equal* to `h₁ ≫ h₂`;
this is what makes the coherence laws below state the equalities one wants. -/
noncomputable def lowerStarComp (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    lowerStar A P Q hQP h₁ ⋙ lowerStar A P Q hQP h₂ ≅ lowerStar A P Q hQP h₁₂ :=
  have := isContinuous_overPullback P Q hQP h₁
  have := isContinuous_overPullback P Q hQP h₂
  have := isContinuous_overPullback P Q hQP h₁₂
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂ h₁₂ hh₁₂).symm) A
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))
    (T.smallGrothendieckTopology Q (Q := P))

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on sheaves
for the small sites, obtained from the composition isomorphism `lowerStarComp` of the
pushforwards by uniqueness of left adjoints: both sides are left adjoint to
`(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def upperStarComp (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    upperStar A P Q h₁₂ ≅ upperStar A P Q h₂ ⋙ upperStar A P Q h₁ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q hQP h₁₂)
      ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁))).symm
    (lowerStarComp A P Q hQP h₁ h₂ h₁₂ hh₁₂).symm).symm

/-- Under the conjugation bijection between the adjunctions `(h₂)^* ⋙ (h₁)^* ⊣ (h₁)_* ⋙ (h₂)_*`
and `(h₁ ≫ h₂)^* ⊣ (h₁ ≫ h₂)_*`, the composition isomorphism of the pullbacks corresponds to
the composition isomorphism of the pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp (h₁₂ : T ⟶ R := h₁ ≫ h₂)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂ := by cat_disch) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁))
      (upperStarLowerStarAdjunction A P Q hQP h₁₂)
      (upperStarComp A P Q hQP h₁ h₂ h₁₂ hh₁₂) = lowerStarComp A P Q hQP h₁ h₂ h₁₂ hh₁₂ := by
  ext : 1
  simp only [upperStarComp, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  exact Equiv.apply_symm_apply _ _

end UpperStar

end Comp

section Coherence

variable {R S T : Scheme.{u}}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The left unit law for `CategoryTheory.GrothendieckTopology.lowerStarComp`: the
composition isomorphism for `𝟙 S ≫ h₂` is `lowerStarId` followed by the left unitor. -/
lemma lowerStarComp_id_left (h₂ : S ⟶ R) :
    lowerStarComp A P Q hQP (𝟙 S) h₂ h₂ (id_comp h₂).symm =
      Functor.isoWhiskerRight (lowerStarId A P Q hQP S) (lowerStar A P Q hQP h₂) ≪≫
        (lowerStar A P Q hQP h₂).leftUnitor := by
  ext M b
  simp only [lowerStarComp, lowerStarId, lowerStar,
    MorphismProperty.Over.pullbackComp_id_left h₂ h₂ (id_comp h₂).symm]
  simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The right unit law for `CategoryTheory.GrothendieckTopology.lowerStarComp`: the
composition isomorphism for `h₁ ≫ 𝟙 S` is `lowerStarId` followed by the right unitor. -/
lemma lowerStarComp_id_right (h₁ : T ⟶ S) :
    lowerStarComp A P Q hQP h₁ (𝟙 S) h₁ (comp_id h₁).symm =
      Functor.isoWhiskerLeft (lowerStar A P Q hQP h₁) (lowerStarId A P Q hQP S) ≪≫
        (lowerStar A P Q hQP h₁).rightUnitor := by
  ext M b
  simp only [lowerStarComp, lowerStarId, lowerStar,
    MorphismProperty.Over.pullbackComp_id_right h₁ h₁ (comp_id h₁).symm]
  simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The associativity law for `CategoryTheory.GrothendieckTopology.lowerStarComp`: the two
ways of writing `f_* ⋙ g_* ⋙ h_* ≅ (f ≫ g ≫ h)_*` agree. -/
lemma lowerStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fgh : X ⟶ V := f ≫ g ≫ h) (hfgh : fgh = f ≫ g ≫ h := by cat_disch) :
    (lowerStar A P Q hQP f).associator (lowerStar A P Q hQP g) (lowerStar A P Q hQP h) ≪≫
        Functor.isoWhiskerLeft (lowerStar A P Q hQP f) (lowerStarComp A P Q hQP g h) ≪≫
          lowerStarComp A P Q hQP f (g ≫ h) fgh hfgh =
      Functor.isoWhiskerRight (lowerStarComp A P Q hQP f g) (lowerStar A P Q hQP h) ≪≫
        lowerStarComp A P Q hQP (f ≫ g) h fgh (by rw [hfgh, assoc]) := by
  ext M b
  have key := congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := ⊤) f g h fgh hfgh)) (unop b)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at key
  simp only [lowerStarComp, lowerStar]
  simp only [Functor.comp_obj, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, id_comp,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op, ← Functor.map_comp,
    ← op_comp, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.sheafPushforwardContinuous_map_hom_app]
  rw [key]

/-- The left unit law for `CategoryTheory.GrothendieckTopology.upperStarComp`, obtained from
`CategoryTheory.GrothendieckTopology.lowerStarComp_id_left` by uniqueness of left adjoints. -/
lemma upperStarComp_id_left (h₂ : S ⟶ R) :
    upperStarComp A P Q hQP (𝟙 S) h₂ h₂ (id_comp h₂).symm =
      (upperStar A P Q h₂).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (upperStar A P Q h₂) (upperStarId A P Q hQP S).symm := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
    (upperStarLowerStarAdjunction A P Q hQP (𝟙 S)))
    (upperStarLowerStarAdjunction A P Q hQP h₂)).injective ?_
  rw [conjugateIsoEquiv_upperStarComp A P Q hQP (𝟙 S) h₂ h₂ (id_comp h₂).symm,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
      (Adjunction.id (C := Sheaf (S.smallGrothendieckTopology Q (Q := P)) A))) _]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_upperStarId, conjugateIsoEquiv_rightUnitor, Iso.symm_symm_eq]
  exact lowerStarComp_id_left A P Q hQP h₂

/-- The right unit law for `CategoryTheory.GrothendieckTopology.upperStarComp`, obtained from
`CategoryTheory.GrothendieckTopology.lowerStarComp_id_right` by uniqueness of left
adjoints. -/
lemma upperStarComp_id_right (h₁ : T ⟶ S) :
    upperStarComp A P Q hQP h₁ (𝟙 S) h₁ (comp_id h₁).symm =
      (upperStar A P Q h₁).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (upperStarId A P Q hQP S).symm (upperStar A P Q h₁) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A P Q hQP (𝟙 S)).comp
    (upperStarLowerStarAdjunction A P Q hQP h₁))
    (upperStarLowerStarAdjunction A P Q hQP h₁)).injective ?_
  rw [conjugateIsoEquiv_upperStarComp A P Q hQP h₁ (𝟙 S) h₁ (comp_id h₁).symm,
    conjugateIsoEquiv_trans _ ((Adjunction.id
        (C := Sheaf (S.smallGrothendieckTopology Q (Q := P)) A)).comp
      (upperStarLowerStarAdjunction A P Q hQP h₁)) _]
  simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_upperStarId, conjugateIsoEquiv_leftUnitor, Iso.symm_symm_eq]
  exact lowerStarComp_id_right A P Q hQP h₁

/-- The associativity law for `CategoryTheory.GrothendieckTopology.upperStarComp`, obtained
from `CategoryTheory.GrothendieckTopology.lowerStarComp_assoc` by uniqueness of left
adjoints. -/
lemma upperStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fgh : X ⟶ V := f ≫ g ≫ h) (hfgh : fgh = f ≫ g ≫ h := by cat_disch) :
    upperStarComp A P Q hQP f (g ≫ h) fgh hfgh ≪≫
        Functor.isoWhiskerRight (upperStarComp A P Q hQP g h) (upperStar A P Q f) ≪≫
          (upperStar A P Q h).associator (upperStar A P Q g) (upperStar A P Q f) =
      upperStarComp A P Q hQP (f ≫ g) h fgh (by rw [hfgh, assoc]) ≪≫
        Functor.isoWhiskerLeft (upperStar A P Q h) (upperStarComp A P Q hQP f g) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A P Q hQP h).comp
    ((upperStarLowerStarAdjunction A P Q hQP g).comp
      (upperStarLowerStarAdjunction A P Q hQP f)))
    (upperStarLowerStarAdjunction A P Q hQP fgh)).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A P Q hQP (g ≫ h)).comp
      (upperStarLowerStarAdjunction A P Q hQP f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction A P Q hQP h).comp
      (upperStarLowerStarAdjunction A P Q hQP g)).comp
      (upperStarLowerStarAdjunction A P Q hQP f)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A P Q hQP h).comp
      (upperStarLowerStarAdjunction A P Q hQP (f ≫ g))) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator, Iso.trans_assoc]
  exact lowerStarComp_assoc A P Q hQP f g h fgh hfgh

end Coherence

end GrothendieckTopology

end CategoryTheory
