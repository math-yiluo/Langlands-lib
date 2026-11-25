/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs

/-!

# Lower shriek along a localization of small sites of schemes

Let `P` and `Q` be morphism properties of schemes and let `f : V ⟶ U` satisfy `h : P f`.
Composition with `f` induces the localization functor
`MorphismProperty.Over.map ⊤ h : P.Over ⊤ V ⥤ P.Over ⊤ U` between the small sites of
`P`-schemes over `V` resp. `U`, equipped with the small `Q`-topologies
`Scheme.smallGrothendieckTopology`. In this file we define the lower shriek functor
`j_{f!}` on `A`-valued sheaves along this localization functor, and its right adjoint,
the restriction functor `j_f^*`.

## Main definitions

- `GrothendieckTopology.localizationLowerShriek`: the lower shriek `j_{f!}`.
- `GrothendieckTopology.localizationRestriction`: the restriction `j_f^*`.
- `GrothendieckTopology.localizationLowerShriekAdjunction`: the adjunction `j_{f!} ⊣ j_f^*`.
- `GrothendieckTopology.localizationRestrictionLowerStarAdjunction`: the adjunction
  `j_f^* ⊣ f_*`, completing the triple `j_{f!} ⊣ j_f^* ⊣ f_*`.
- `GrothendieckTopology.upperStarIsoLocalizationRestriction`: for `f` satisfying `P` the
  pullback `f^*` of `WeilConjectures.SixFunctors.UpperLowerStar.Defs` is computed by
  restriction, both being left adjoint to `f_*`.
- `GrothendieckTopology.localizationLowerShriekUpperStarAdjunction`: the adjunction
  `j_{f!} ⊣ f^*`.
- `GrothendieckTopology.localizationAdjunctionTriple`: the triple `j_{f!} ⊣ j_f^* ⊣ f_*` as
  a `CategoryTheory.Adjunction.Triple`. Via
  `CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit` this is what makes `j_{f!}`
  fully faithful as soon as `f_*` is.
- `localizationLowerShriekPresheaf` and `localizationLowerShriekPresheafAdjunction`: the
  presheaf-level Kan extension `j_{f,!}^{pre}` and its adjunction with restriction.
- `GrothendieckTopology.isContinuous_overMap_of_le` and
  `GrothendieckTopology.isCocontinuous_overMap_of_le`: for `Q ≤ P` the localization
  functor is continuous and cocontinuous for the small `Q`-topologies, with instances
  for `Q = P`.

## Implementation notes

- `j_{f!}` is defined as the left Kan extension along `(MorphismProperty.Over.map ⊤ h).op`
  on presheaves followed by sheafification; this holds definitionally, see
  `localizationLowerShriek_eq`. The Kan extension existence hypothesis is satisfied
  e.g. as soon as `A` has colimits of the relevant size.
- `j_f^*` restricts along the localization functor, so it requires `P f`, but it needs
  neither Kan extensions nor sheafification. The pullback `GrothendieckTopology.upperStar`
  of `WeilConjectures.SixFunctors.UpperLowerStar.Defs` is defined for an arbitrary morphism at
  the cost of both; the two agree for `f` satisfying `P`, by
  `upperStarIsoLocalizationRestriction`. Consequently
  `localizationLowerShriekUpperStarAdjunction` carries the hypotheses of both
  constructions, whereas `localizationLowerShriekAdjunction` does not.
- The continuity of the localization functor is derived from the inequality `hQP : Q ≤ P`
  via `isContinuous_overMap_of_le`; since `Q ≤ P` is not a class, `hQP` is an explicit
  argument of the definitions using it, and instances are provided for `Q = P`.

When `f` is an open immersion (in particular a monomorphism), `j_{f!}` is the *extension by
zero* functor. It is then fully faithful; for the small étale sites this is
`AlgebraicGeometry.Etale.fullyFaithfulOpenImmersionLowerShriek` in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`, proved from
`localizationAdjunctionTriple` above.
-/

@[expose] public section

set_option linter.style.show false

universe w u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace GrothendieckTopology

/- The left Kan extensions on presheaves and the sheafification entering the definitions
below are provided by the results of the folder
`WeilConjectures.CategoryTheory.GrothendieckAbelian`, the sheafification by the
`CategoryTheory.HasSmallSiteSheafify` hypothesis on `A`, and the continuity of the base
change functor by `AlgebraicGeometry.Scheme.isContinuous_overPullback`, under the
following multiplicativity-type assumptions on `P` and `Q` and the inequality
`hQP : Q ≤ P`; all of them hold for `P = Q = @Etale`. -/
variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
variable (hQP : Q ≤ P)

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : P f)

section LowerShriek

variable [Mono f]

/-- The lower shriek `j_{f!}` along `f : V ⟶ U` with `h : P f`: left Kan extension on
presheaves followed by sheafification, left adjoint to `localizationRestriction`. -/
noncomputable def localizationLowerShriek :
    Sheaf (V.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (U.smallGrothendieckTopology Q (Q := P)) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h) A _ _

end LowerShriek

/-! ### Continuity and cocontinuity of the localization functor -/

section SiteInstances

variable {P Q f}

/-- For `Q ≤ P` the localization functor is cocontinuous for the small `Q`-topologies. -/
lemma isCocontinuous_overMap_of_le (hQP : Q ≤ P) :
    (MorphismProperty.Over.map ⊤ h).IsCocontinuous
      (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P)) where
  cover_lift {W S} hS := by
    have heqV : V.smallGrothendieckTopology Q (Q := P) =
        (V.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology V hQP
    have heqU : U.smallGrothendieckTopology Q (Q := P) =
        (U.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP
    rw [heqU] at hS
    rw [heqV]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun x => ?_
    obtain ⟨Y, φ, y, hSφ, hφl, hφy⟩ := hS x
    let W' : P.Over ⊤ V := MorphismProperty.Over.mk ⊤ (φ.left ≫ W.hom)
      (P.comp_mem _ _ (hQP _ hφl) W.prop)
    let ψ : W' ⟶ W := MorphismProperty.Over.homMk φ.left rfl
    refine ⟨W', ψ, y, ?_, hφl, hφy⟩
    -- Compare the image of `ψ` under the localization functor with `φ` via the identity
    -- on `Y.left`.
    have hY : 𝟙 Y.left ≫ Y.hom = (φ.left ≫ W.hom) ≫ f := by
      simp only [Category.id_comp, Category.assoc]
      exact (MorphismProperty.Over.w φ).symm
    let e : (MorphismProperty.Over.map ⊤ h).obj W' ⟶ Y :=
      MorphismProperty.Over.homMk (𝟙 Y.left) hY
    have hge : (MorphismProperty.Over.map ⊤ h).map ψ = e ≫ φ := by
      apply MorphismProperty.Over.Hom.ext
      show φ.left = 𝟙 Y.left ≫ φ.left
      exact (Category.id_comp _).symm
    show S.arrows ((MorphismProperty.Over.map ⊤ h).map ψ)
    rw [hge]
    exact S.downward_closed hSφ e

/-- For `Q ≤ P` the localization functor preserves covering sieves of the small
`Q`-topologies. -/
lemma coverPreserving_overMap_of_le (hQP : Q ≤ P) :
    CoverPreserving (V.smallGrothendieckTopology Q (Q := P))
      (U.smallGrothendieckTopology Q (Q := P)) (MorphismProperty.Over.map ⊤ h) where
  cover_preserve {W S} hS := by
    have heqV : V.smallGrothendieckTopology Q (Q := P) =
        (V.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology V hQP
    have heqU : U.smallGrothendieckTopology Q (Q := P) =
        (U.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP
    rw [heqV] at hS
    rw [heqU]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun v => ?_
    obtain ⟨Z, g, z, hSg, hgl, hgz⟩ := hS v
    exact ⟨(MorphismProperty.Over.map ⊤ h).obj Z, (MorphismProperty.Over.map ⊤ h).map g, z,
      ⟨Z, g, 𝟙 _, hSg, (Category.id_comp _).symm⟩, hgl, hgz⟩

omit [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [P.IsStableUnderBaseChange] in
/-- The localization functor preserves compatible families of elements. -/
lemma compatiblePreserving_overMap :
    CompatiblePreserving.{w} (U.smallGrothendieckTopology Q (Q := P))
      (MorphismProperty.Over.map ⊤ h) where
  compatible := by
    intro ℱ Z T x hx Y₁ Y₂ T' f₁ f₂ g₁ g₂ hg₁ hg₂ hcomp
    have hleft : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      have h' : (f₁ ≫ (MorphismProperty.Over.map ⊤ h).map g₁).left =
          (f₂ ≫ (MorphismProperty.Over.map ⊤ h).map g₂).left := by
        rw [hcomp]
      exact h'
    have hw : f₂.left ≫ Y₂.hom = f₁.left ≫ Y₁.hom := by
      have w₁ : g₁.left ≫ Z.hom = Y₁.hom := MorphismProperty.Over.w g₁
      have w₂ : g₂.left ≫ Z.hom = Y₂.hom := MorphismProperty.Over.w g₂
      rw [← w₁, ← w₂, ← Category.assoc, ← Category.assoc, hleft]
    -- `f₁.left` satisfies `P` since it is a morphism between `P`-schemes over `U`.
    have hf₁P : P f₁.left := by
      apply P.of_postcomp (W' := P) f₁.left
        ((MorphismProperty.Over.map ⊤ h).obj Y₁).hom (MorphismProperty.Comma.prop _)
      rw [MorphismProperty.Over.w f₁]
      exact MorphismProperty.Comma.prop _
    let W' : P.Over ⊤ V := MorphismProperty.Over.mk ⊤ (f₁.left ≫ Y₁.hom)
      (P.comp_mem _ _ hf₁P Y₁.prop)
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left hw
    have hcomm : g₁' ≫ g₁ = g₂' ≫ g₂ := by
      apply MorphismProperty.Over.Hom.ext
      show f₁.left ≫ g₁.left = f₂.left ≫ g₂.left
      exact hleft
    have hT' : 𝟙 T'.left ≫ (f₁.left ≫ Y₁.hom) ≫ f = T'.hom := by
      simp only [Category.id_comp, Category.assoc]
      exact MorphismProperty.Over.w f₁
    let e : T' ⟶ (MorphismProperty.Over.map ⊤ h).obj W' :=
      MorphismProperty.Over.homMk (𝟙 T'.left) hT'
    have hf₁ : f₁ = e ≫ (MorphismProperty.Over.map ⊤ h).map g₁' := by
      apply MorphismProperty.Over.Hom.ext
      show f₁.left = 𝟙 T'.left ≫ f₁.left
      exact (Category.id_comp _).symm
    have hf₂ : f₂ = e ≫ (MorphismProperty.Over.map ⊤ h).map g₂' := by
      apply MorphismProperty.Over.Hom.ext
      show f₂.left = 𝟙 T'.left ≫ f₂.left
      exact (Category.id_comp _).symm
    have key := hx g₁' g₂' hg₁ hg₂ hcomm
    rw [hf₁, hf₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (ℱ.obj.map e.op) key

/-- For `Q ≤ P` the localization functor is continuous for the small `Q`-topologies. -/
lemma isContinuous_overMap_of_le (hQP : Q ≤ P) :
    (MorphismProperty.Over.map ⊤ h).IsContinuous
      (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_overMap h)
    (coverPreserving_overMap_of_le h hQP)

instance {P : MorphismProperty Scheme} {V U : Scheme} {f : V ⟶ U} (h : P f)
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative] :
    (MorphismProperty.Over.map ⊤ h).IsCocontinuous
      (V.smallGrothendieckTopology P) (U.smallGrothendieckTopology P) :=
  isCocontinuous_overMap_of_le h le_rfl

instance {P : MorphismProperty Scheme} {V U : Scheme} {f : V ⟶ U} (h : P f)
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative] :
    (MorphismProperty.Over.map ⊤ h).IsContinuous
      (V.smallGrothendieckTopology P) (U.smallGrothendieckTopology P) :=
  isContinuous_overMap_of_le h le_rfl

end SiteInstances

section Restriction

/-- The restriction functor `j_f^*` along `f : V ⟶ U` with `h : P f`, given objectwise by
`(j_f^* G)(T → V) = G(T → V → U)`. The continuity of the localization functor is proved,
for `Q ≤ P`, as `isContinuous_overMap_of_le` above. -/
def localizationRestriction :
    Sheaf (U.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (V.smallGrothendieckTopology Q (Q := P)) A :=
  have := isContinuous_overMap_of_le h hQP
  (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
    (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P))

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The sections of `j_f^* G` over `T → V` are the sections of `G` over `T → V → U`. -/
lemma localizationRestriction_obj_val_obj
    (G : Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ V) :
    ((localizationRestriction A P Q hQP f h).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- `j_f^*` acts on morphisms by whiskering along `(MorphismProperty.Over.map ⊤ h).op`. -/
lemma localizationRestriction_map_hom_app
    {G G' : Sheaf (U.smallGrothendieckTopology Q (Q := P)) A} (φ : G ⟶ G') (b : P.Over ⊤ V) :
    (((localizationRestriction A P Q hQP f h).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

section Adjunction

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ j_f^*`. -/
noncomputable def localizationLowerShriekAdjunction :
    localizationLowerShriek A P Q f h ⊣ localizationRestriction A P Q hQP f h :=
  have := isContinuous_overMap_of_le h hQP
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P))

include hQP in
/-- `j_{f!}` is a left adjoint. Not an instance, since its statement does not determine
the inequality `hQP : Q ≤ P` entering the adjunction `j_{f!} ⊣ j_f^*`; for the small
étale sites the corresponding instance is registered in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`. -/
lemma isLeftAdjoint_localizationLowerShriek : (localizationLowerShriek A P Q f h).IsLeftAdjoint :=
  (localizationLowerShriekAdjunction A P Q hQP f h).isLeftAdjoint

instance : (localizationRestriction A P Q hQP f h).IsRightAdjoint :=
  (localizationLowerShriekAdjunction A P Q hQP f h).isRightAdjoint

/-- The lower shriek agrees with mathlib's abstract left adjoint
`(MorphismProperty.Over.map ⊤ h).sheafPullback` of the restriction functor. -/
noncomputable def localizationLowerShriekIsoSheafPullback :
    have := isContinuous_overMap_of_le h hQP
    (MorphismProperty.Over.map ⊤ h).sheafPullback A
        (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P)) ≅
      localizationLowerShriek A P Q f h :=
  have := isContinuous_overMap_of_le h hQP
  Functor.sheafPullbackConstruction.sheafPullbackIso (MorphismProperty.Over.map ⊤ h) A
    (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P))

end Adjunction

/-! ### Comparison with the pullback `f^*` -/

section UpperStar

/-- Restriction along the localization functor is left adjoint to the pushforward `f_*`:
this is the right half of the triple `j_{f!} ⊣ j_f^* ⊣ f_*`. It is induced by the
adjunction `MorphismProperty.Over.mapPullbackAdj` between the two site functors, and in
particular requires neither Kan extensions nor sheafification. -/
noncomputable def localizationRestrictionLowerStarAdjunction :
    localizationRestriction A P Q hQP f h ⊣ lowerStar A P Q hQP f :=
  have := isContinuous_overMap_of_le h hQP
  have := isContinuous_overPullback P Q hQP f
  (MorphismProperty.Over.mapPullbackAdj P ⊤ f h _root_.trivial).sheafPushforwardContinuous
    (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P))

section

/-- For `f` satisfying `P`, the pullback `f^*` is computed by restriction along the
localization functor: both are left adjoint to `f_*`. In particular `f^*` needs no
sheafification in this case, and its sections are given by
`localizationRestriction_obj_val_obj`. -/
noncomputable def upperStarIsoLocalizationRestriction :
    upperStar A P Q f ≅ localizationRestriction A P Q hQP f h :=
  (upperStarLowerStarAdjunction A P Q hQP f).leftAdjointUniq
    (localizationRestrictionLowerStarAdjunction A P Q hQP f h)

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ f^*` between the lower shriek and the pullback, obtained from
`localizationLowerShriekAdjunction` by transporting along
`upperStarIsoLocalizationRestriction`. -/
noncomputable def localizationLowerShriekUpperStarAdjunction :
    localizationLowerShriek A P Q f h ⊣ upperStar A P Q f :=
  (localizationLowerShriekAdjunction A P Q hQP f h).ofNatIsoRight
    (upperStarIsoLocalizationRestriction A P Q hQP f h).symm

/-- The adjoint triple `j_{f!} ⊣ j_f^* ⊣ f_*` on sheaves, bundling
`localizationLowerShriekAdjunction` and `localizationRestrictionLowerStarAdjunction`. -/
noncomputable def localizationAdjunctionTriple :
    Adjunction.Triple (localizationLowerShriek A P Q f h)
      (localizationRestriction A P Q hQP f h) (lowerStar A P Q hQP f) where
  adj₁ := localizationLowerShriekAdjunction A P Q hQP f h
  adj₂ := localizationRestrictionLowerStarAdjunction A P Q hQP f h

end

end UpperStar

end Restriction

end GrothendieckTopology

section Presheaf

variable (P : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
variable {V U : Scheme.{u}} (f : V ⟶ U) (h : P f) [Mono f]

/-- The presheaf-level lower shriek `j_{f,!}^{pre}`: left Kan extension along
`(MorphismProperty.Over.map ⊤ h).op`. -/
noncomputable def localizationLowerShriekPresheaf :
    ((P.Over ⊤ V)ᵒᵖ ⥤ A) ⥤ ((P.Over ⊤ U)ᵒᵖ ⥤ A) :=
  (MorphismProperty.Over.map ⊤ h).op.lan

/-- The presheaf-level adjunction between `j_{f,!}^{pre}` and restriction. -/
noncomputable def localizationLowerShriekPresheafAdjunction :
    localizationLowerShriekPresheaf A P f h ⊣
      (Functor.whiskeringLeft (P.Over ⊤ V)ᵒᵖ (P.Over ⊤ U)ᵒᵖ A).obj
        (MorphismProperty.Over.map ⊤ h).op :=
  (MorphismProperty.Over.map ⊤ h).op.lanAdjunction A

end Presheaf

namespace GrothendieckTopology

variable (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
variable {V U : Scheme.{u}} (f : V ⟶ U) (h : P f) [Mono f]

/-- The lower shriek is definitionally the left Kan extension on presheaves followed by
sheafification. -/
lemma localizationLowerShriek_eq :
    localizationLowerShriek A P Q f h =
      sheafToPresheaf (V.smallGrothendieckTopology Q (Q := P)) A ⋙
        localizationLowerShriekPresheaf A P f h ⋙
          presheafToSheaf (U.smallGrothendieckTopology Q (Q := P)) A :=
  rfl

end GrothendieckTopology

end CategoryTheory
