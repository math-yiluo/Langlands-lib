/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.ProjectionComposition
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism
public import WeilConjectures.Tactic.ExactByKernel

/-!

# The exceptional projection morphism and the composition of lower shrieks

The exceptional projection morphism `PF_f : Rf_! T ⊗ M ⟶ Rf_! (T ⊗ Lf^* M)` of bounded
constructible `ℚ̄_ℓ`-complexes is compatible with the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` and `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`
(`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_comp_whiskerLeft`,
blueprint
`prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2).

The composition isomorphism of the lower shriek is computed through a triangle of
compactifications and the composition isomorphism `compIso` of the exchange formalism of bounded
constructible complexes
(`boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl_hom_eq`).
The proof transports the abstract compatibility
`CategoryTheory.ExchangeFormalism.compIso_inv_app_whiskerRight_comp_of_eq` to bounded
constructible complexes:

1. the exceptional projection morphism of a compactification is the exceptional projection
   morphism of the factorization in the exchange formalism
   (`homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection`);
2. the comparison with the chosen compactification of `f ≫ g` intertwines the exceptional
   projection morphisms
   (`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_hom_app_whiskerRight_comp`).

## Implementation notes

The data of the exchange formalism (its categories, pullbacks, monoidal structures) unfold to those
of bounded constructible complexes, but the elaborator compares the two spellings by eagerly
reducing projections of instances, which does not terminate in reasonable time on these large
terms, in particular when a natural transformation is applied to two spellings of the same object.
The abstract statement therefore takes all heavy data as variables, they are passed in the
spelling of the goal (including the instance arguments of the triangle of factorizations), and
the two remaining identifications are left to the kernel with `exact_by_kernel`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

/-- The categories of the exchange formalism of bounded constructible `ℚ̄_ℓ`-sheaves are
monoidal. -/
noncomputable instance boundedConstructibleExchangeFormalism.monoidalCategory
    (X : SepFinType k) : MonoidalCategory ((𝔽).obj X) :=
  monoidalCategory_boundedConstructible X.obj

/-- The pullbacks of the exchange formalism of bounded constructible `ℚ̄_ℓ`-sheaves are
monoidal. -/
noncomputable instance boundedConstructibleExchangeFormalism.monoidal_pb {X Y : SepFinType k}
    (f : X ⟶ Y) : ((𝔽).pb f).Monoidal :=
  monoidal_boundedConstructibleUpperStar ℓ f.hom

/-- The projection comparisons of the extensions by zero of the exchange formalism of bounded
constructible `ℚ̄_ℓ`-sheaves are isomorphisms. -/
instance boundedConstructibleExchangeFormalism.isIso_projectionComparison {X Y : SepFinType k}
    (j : X ⟶ Y) [Fact (SepFinType.openImmersion j)] (K : (𝔽).obj X) (N : (𝔽).obj Y) :
    IsIso (((𝔽).shAdj j).projectionComparison K N) :=
  isIso_boundedConstructibleOpenImmersionProjectionComparison ℓ j.hom K N

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The composition isomorphism of the pullbacks of a compactification in the exchange formalism
is that of the bounded constructible pullbacks. -/
lemma boundedConstructibleExchangeFormalism_pbComp'_compactification
    (c : Compactification f.left) :
    (𝔽).pbComp' (SepFinType.homMk c.overI) (SepFinType.homMk c.overG) (SepFinType.homMk f)
        (ObjectProperty.hom_ext _ c.overI_overG) =
      eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) c.overI_overG.symm) ≪≫
        boundedConstructibleUpperStarComp _ ℓ c.overI c.overG :=
  rfl

/-- The exceptional projection morphism of a compactification on bounded constructible
`ℚ̄_ℓ`-complexes is the exceptional projection morphism of the factorization in the exchange
formalism. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (𝔽).shriekProjection (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
        (SepFinType.homMk f) (ObjectProperty.hom_ext _ c.overI_overG) K B := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ c K B _
    (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ c B)]
  unfold ExchangeFormalism.shriekProjection
  refine congrArg₂ (· ≫ ·) rfl (congrArg _ (congrArg₂ (· ≫ ·) rfl ?_))
  exact congrArg (fun e : boundedConstructibleUpperStar _ ℓ f ≅
      boundedConstructibleUpperStar _ ℓ c.overG ⋙ boundedConstructibleUpperStar _ ℓ c.overI ↦
        (boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).map (K ◁ e.inv.app B))
    (boundedConstructibleExchangeFormalism_pbComp'_compactification ℓ c).symm


/-- The composition isomorphisms of the pullbacks of bounded constructible `ℚ̄_ℓ`-complexes are
compatible with the comultiplications, in the exchange formalism. -/
lemma boundedConstructibleExchangeFormalism_δ_pbComp {X Y Z : SepFinType k} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M N : (𝔽).obj Z) :
    Functor.OplaxMonoidal.δ ((𝔽).pb (f ≫ g)) M N ≫
        (((𝔽).pbComp f g).hom.app M ⊗ₘ ((𝔽).pbComp f g).hom.app N) =
      ((𝔽).pbComp f g).hom.app (M ⊗ N) ≫
        ((𝔽).pb f).map (Functor.OplaxMonoidal.δ ((𝔽).pb g) M N) ≫
          Functor.OplaxMonoidal.δ ((𝔽).pb f) (((𝔽).pb g).obj M) (((𝔽).pb g).obj N) :=
  boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ f.hom g.hom M N

section Composite

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {g : Y ⟶ Z}

/-- The composition isomorphism of the pullbacks of a compactification of a composite in the
exchange formalism is that of the bounded constructible pullbacks. -/
lemma boundedConstructibleExchangeFormalism_pbComp'_compactification_comp
    (c : Compactification (f ≫ g).left) :
    (𝔽).pbComp' (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
        (SepFinType.homMk f ≫ SepFinType.homMk g) (ObjectProperty.hom_ext _ c.overI_overG) =
      eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) c.overI_overG.symm) ≪≫
        boundedConstructibleUpperStarComp _ ℓ c.overI c.overG :=
  rfl

/-- `homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection` for a
compactification of a composite `f ≫ g`, written with the composite `homMk f ≫ homMk g` in the
exchange formalism. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection_comp
    (c : Compactification (f ≫ g).left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Z.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (𝔽).shriekProjection (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
        (SepFinType.homMk f ≫ SepFinType.homMk g) (ObjectProperty.hom_ext _ c.overI_overG) K B := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ c K B _
    (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ c B)]
  unfold ExchangeFormalism.shriekProjection
  refine congrArg₂ (· ≫ ·) rfl (congrArg _ (congrArg₂ (· ≫ ·) rfl ?_))
  exact congrArg (fun e : boundedConstructibleUpperStar _ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar _ ℓ c.overG ⋙ boundedConstructibleUpperStar _ ℓ c.overI ↦
        (boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).map (K ◁ e.inv.app B))
    (boundedConstructibleExchangeFormalism_pbComp'_compactification_comp ℓ c).symm


end Composite

section Comp

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom]

/-- The triangle of factorizations of the exchange formalism attached to a triangle of
compactifications. -/
local notation "τ" => triangleShriekTriangle

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
private lemma comp_eqToHom_self {C : Type*} [Category C] {X A : C} (x : X ⟶ A) (h : A = A) :
    x ≫ eqToHom h = x := by
  simp

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
private lemma comp_map_eqToHom_self {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X : D}
    {A : C} (x : X ⟶ F.obj A) (h : A = A) : x ≫ F.map (eqToHom h) = x := by
  simp

/-- The exceptional projection morphism of a morphism is that of its chosen compactification. -/
lemma boundedConstructibleExceptionalProjectionMorphism_eq_homMk {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : X ⟶ Y) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ g K B =
      ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ
          (compactificationOverField g)).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ
          (compactificationOverField g)).obj (K ⊗ (boundedConstructibleUpperStar _ ℓ g).obj B))
        (exceptionalProjectionMorphismOfCompactification _ (compactificationOverField g)
          K.obj B.obj) :=
  rfl

variable (f : X ⟶ Y) (g : Y ⟶ Z)
  (d : Compactification ((compactificationOverField f).overG ≫
    (compactificationOverField g).overI).left)
  (hd : IsPullback (compactificationOverField f).overG d.overI
    (compactificationOverField g).overI d.overG)

/-- The exceptional projection morphism of the second factor of the triangle of the chosen
compactifications, in the exchange formalism. -/
private lemma exceptionalProjection_snd_eq_shriekProjection (T : Dᵇc(X.left)⟦𝐐⟧)
    (B : Dᵇc(Z.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ g
        ((boundedConstructibleLowerShriek ℓ f).obj T) B =
      @ExchangeFormalism.shriekProjection _ _ _ (𝔽) _ _ _ _ _
        (τ (triangleOfCompactifications _ _ d hd)).i₂
        (τ (triangleOfCompactifications _ _ d hd)).fact_i₂
        (τ (triangleOfCompactifications _ _ d hd)).p₂ (SepFinType.homMk g)
        (ObjectProperty.hom_ext _ (compactificationOverField g).overI_overG)
        (@boundedConstructibleExchangeFormalism.isIso_projectionComparison ℓ _ k _ _ _ _ _
          (τ (triangleOfCompactifications _ _ d hd)).i₂
          (τ (triangleOfCompactifications _ _ d hd)).fact_i₂)
        ((@ExchangeFormalism.shriek _ _ _ (𝔽) _ _ _ (τ (triangleOfCompactifications _ _ d hd)).i₁
          (τ (triangleOfCompactifications _ _ d hd)).fact_i₁
          (τ (triangleOfCompactifications _ _ d hd)).p₁).obj T) B := by
  rw [boundedConstructibleExceptionalProjectionMorphism_eq_homMk ℓ g]
  exact homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection ℓ
    (compactificationOverField g) ((boundedConstructibleLowerShriek ℓ f).obj T) B

/-- The exceptional projection morphism of the first factor of the triangle of the chosen
compactifications, in the exchange formalism. -/
private lemma exceptionalProjection_fst_eq_shriekProjection (T : Dᵇc(X.left)⟦𝐐⟧)
    (B : Dᵇc(Z.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ f T
        ((boundedConstructibleUpperStar _ ℓ g).obj B) =
      @ExchangeFormalism.shriekProjection _ _ _ (𝔽) _ _ _ _ _
          (τ (triangleOfCompactifications _ _ d hd)).i₁
          (τ (triangleOfCompactifications _ _ d hd)).fact_i₁
          (τ (triangleOfCompactifications _ _ d hd)).p₁ (SepFinType.homMk f)
          (ObjectProperty.hom_ext _ (compactificationOverField f).overI_overG)
          (@boundedConstructibleExchangeFormalism.isIso_projectionComparison ℓ _ k _ _ _ _ _
            (τ (triangleOfCompactifications _ _ d hd)).i₁
            (τ (triangleOfCompactifications _ _ d hd)).fact_i₁) T
          (((𝔽).pb (SepFinType.homMk g)).obj B) := by
  rw [boundedConstructibleExceptionalProjectionMorphism_eq_homMk ℓ f]
  exact homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection ℓ
    (compactificationOverField f) T ((boundedConstructibleUpperStar _ ℓ g).obj B)

/-- `exceptionalProjection_fst_eq_shriekProjection` followed by the identification of
`T ⊗ f^* g^* B` in the exchange formalism with its bounded constructible form. -/
private lemma exceptionalProjection_fst_eq_shriekProjection_comp_eqToHom (T : Dᵇc(X.left)⟦𝐐⟧)
    (B : Dᵇc(Z.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ f T
        ((boundedConstructibleUpperStar _ ℓ g).obj B) =
      @ExchangeFormalism.shriekProjection _ _ _ (𝔽) _ _ _ _ _
          (τ (triangleOfCompactifications _ _ d hd)).i₁
          (τ (triangleOfCompactifications _ _ d hd)).fact_i₁
          (τ (triangleOfCompactifications _ _ d hd)).p₁ (SepFinType.homMk f)
          (ObjectProperty.hom_ext _ (compactificationOverField f).overI_overG)
          (@boundedConstructibleExchangeFormalism.isIso_projectionComparison ℓ _ k _ _ _ _ _
            (τ (triangleOfCompactifications _ _ d hd)).i₁
            (τ (triangleOfCompactifications _ _ d hd)).fact_i₁) T
          (((𝔽).pb (SepFinType.homMk g)).obj B) ≫
      (@ExchangeFormalism.shriek _ _ _ (𝔽) _ _ _ (τ (triangleOfCompactifications _ _ d hd)).i₁
        (τ (triangleOfCompactifications _ _ d hd)).fact_i₁
        (τ (triangleOfCompactifications _ _ d hd)).p₁).map
          (eqToHom (rfl : T ⊗ ((𝔽).pb (SepFinType.homMk f)).obj
              (((𝔽).pb (SepFinType.homMk g)).obj B) =
            (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
              ((boundedConstructibleUpperStar _ ℓ g).obj B) : Dᵇc(X.left)⟦𝐐⟧))) :=
  (exceptionalProjection_fst_eq_shriekProjection ℓ f g d hd T B).trans
    (comp_map_eqToHom_self _ _ _).symm

/-- The lower shriek of the composite compactification is the composite of the extension by zero
and the pushforward of the exchange formalism. -/
private lemma lowerShriekOfCompactification_map_eq {A B : Dᵇc(X.left)⟦𝐐⟧} (x : A ⟶ B) :
    (boundedConstructibleLowerShriekOfCompactification ℓ
      ((compactificationOverField f).overComp (compactificationOverField g) d)).map x =
    (@ExchangeFormalism.shriek _ _ _ (𝔽) _ _ _ (τ (triangleOfCompactifications _ _ d hd)).i
      (τ (triangleOfCompactifications _ _ d hd)).fact_i
      (τ (triangleOfCompactifications _ _ d hd)).p).map x :=
  rfl

omit d hd in
/-- Whiskering by `T` in the exchange formalism, followed by the identification of
`T ⊗ f^* g^* M` with its bounded constructible form. -/
private lemma whiskerLeft_eq_comp_eqToHom (T : Dᵇc(X.left)⟦𝐐⟧) (M : Dᵇc(Z.left)⟦𝐐⟧)
    (s : (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj M ⟶
      (boundedConstructibleUpperStar _ ℓ g ⋙ boundedConstructibleUpperStar _ ℓ f).obj M)
    (h : T ⊗ ((𝔽).pb (SepFinType.homMk g) ⋙ (𝔽).pb (SepFinType.homMk f)).obj M =
      (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
        ((boundedConstructibleUpperStar _ ℓ g).obj M) : Dᵇc(X.left)⟦𝐐⟧)) :
    (T ◁ s : T ⊗ _ ⟶ T ⊗ _) =
      @MonoidalCategoryStruct.whiskerLeft ((𝔽).obj (SepFinType.mk X)) _ _ T
        (((𝔽).pb (SepFinType.homMk f ≫ SepFinType.homMk g)).obj M)
        (((𝔽).pb (SepFinType.homMk g) ⋙ (𝔽).pb (SepFinType.homMk f)).obj M) s ≫
          eqToHom h := by
  rw [comp_eqToHom_self]

-- Comparing the two compactification triangles unfolds the lower shriek definitions.
/-- **The exceptional projection morphism is compatible with the composition isomorphism attached
to compactifications** (blueprint `prop-sf-pf-coherence`): for the chosen compactifications of
`f` and `g` and a compactification `d` of `p ≫ j` with cartesian square, through the
composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` attached to them, the exceptional projection
morphism of `f ≫ g` is that of `g` followed by `Rg_!` of that of `f`. -/
theorem boundedConstructibleExceptionalProjectionMorphism_comp_of_compactifications
    (T : Dᵇc(X.left)⟦𝐐⟧) (M : Dᵇc(Z.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (f ≫ g) T M ≫
        (boundedConstructibleLowerShriek ℓ (f ≫ g)).map
          (T ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app M) =
      (boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g _ _ d hd).hom.app
          T ▷ M ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ g
          ((boundedConstructibleLowerShriek ℓ f).obj T) M ≫
        (boundedConstructibleLowerShriek ℓ g).map
          (boundedConstructibleExceptionalProjectionMorphism ℓ f T
            ((boundedConstructibleUpperStar _ ℓ g).obj M)) ≫
        (boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g _ _ d hd).inv.app
          (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
            ((boundedConstructibleUpperStar _ ℓ g).obj M)) := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications _ _ d hd)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications _ _ d hd)
  have hhom := boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl_hom_eq ℓ
    (compactificationOverField f) (compactificationOverField g) d hd
  have hinv : (boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g _ _ d
      hd).inv = ((𝔽).compIso (τ (triangleOfCompactifications _ _ d hd))).hom ≫
        (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
          (compactificationOverField (f ≫ g)) ((compactificationOverField f).overComp
            (compactificationOverField g) d)).inv := by
    rw [← cancel_epi (boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g _ _
      d hd).hom, Iso.hom_inv_id, hhom]
    simp
  rw [hhom, hinv]
  simp only [NatTrans.comp_app, comp_whiskerRight, Category.assoc]
  -- cancel the comparison `J` of the chosen compactification of `f ≫ g` with the composite one
  rw [← cancel_mono ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
    (compactificationOverField (f ≫ g)) ((compactificationOverField f).overComp
      (compactificationOverField g) d)).hom.app (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
        ((boundedConstructibleUpperStar _ ℓ g).obj M)))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hn := (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
    (compactificationOverField (f ≫ g)) ((compactificationOverField f).overComp
      (compactificationOverField g) d)).hom.naturality
      (X := T ⊗ (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj M)
      (Y := T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
        ((boundedConstructibleUpperStar _ ℓ g).obj M))
      (T ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app M)
  erw [hn]
  have hJ :=
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_hom_app_whiskerRight_comp ℓ
      (compactificationOverField (f ≫ g)) ((compactificationOverField f).overComp
      (compactificationOverField g) d) T M
  refine ((reassoc_of% hJ) _).symm.trans ?_
  refine congrArg (_ ≫ ·) ?_
  -- the composition isomorphism of the triangle of compactifications
  refine ((𝔽).compIso_inv_app_whiskerRight_comp_of_eq
    (instMonoidal := boundedConstructibleExchangeFormalism.monoidalCategory ℓ (k := k))
    (instMonoidalPb := @boundedConstructibleExchangeFormalism.monoidal_pb ℓ _ k _ _ _)
    (boundedConstructibleExchangeFormalism_δ_pbComp ℓ)
    (τ (triangleOfCompactifications _ _ d hd))
    (hbc := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications _ _ d hd))
    (hex := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications _ _ d hd))
    (f := SepFinType.homMk f) (g := SepFinType.homMk g)
    (ObjectProperty.hom_ext _ (compactificationOverField f).overI_overG)
    (ObjectProperty.hom_ext _ (compactificationOverField g).overI_overG)
    (ObjectProperty.hom_ext _ (Compactification.Triangle.overCfg
      (triangleOfCompactifications _ _ d hd)).overI_overG) T M
    (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj ((boundedConstructibleUpperStar _ ℓ g).obj M) :
      Dᵇc(X.left)⟦𝐐⟧) rfl _ ?_
    ((boundedConstructibleUpperStarComp _ ℓ f g).hom.app M :
      (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj M ⟶ _) ?_
    (T ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app M) ?_ _ ?_ _ ?_ _ ?_).symm
  · exact homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection_comp ℓ _ T M
  · refine congrArg (fun e : boundedConstructibleUpperStar _ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar _ ℓ g ⋙ boundedConstructibleUpperStar _ ℓ f ↦ e.hom.app M) ?_
    rfl
  · exact whiskerLeft_eq_comp_eqToHom ℓ f g T M _ _
  · exact lowerShriekOfCompactification_map_eq ℓ f g d hd _
  -- the two typings differ only by unfolding the exchange formalism, see `exact_by_kernel`
  · exact_by_kernel exceptionalProjection_snd_eq_shriekProjection ℓ f g d hd T M
  · exact_by_kernel exceptionalProjection_fst_eq_shriekProjection_comp_eqToHom ℓ f g d hd T M

omit d hd in
/-- **The exceptional projection morphism is compatible with composition** (blueprint
`prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2): through the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` and `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, the exceptional projection morphism of
`f ≫ g` is that of `g` followed by `Rg_!` of that of `f`. -/
theorem boundedConstructibleExceptionalProjectionMorphism_comp_whiskerLeft
    (T : Dᵇc(X.left)⟦𝐐⟧) (M : Dᵇc(Z.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (f ≫ g) T M ≫
        (boundedConstructibleLowerShriek ℓ (f ≫ g)).map
          (T ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app M) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app T ▷ M ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ g
          ((boundedConstructibleLowerShriek ℓ f).obj T) M ≫
        (boundedConstructibleLowerShriek ℓ g).map
          (boundedConstructibleExceptionalProjectionMorphism ℓ f T
            ((boundedConstructibleUpperStar _ ℓ g).obj M)) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).inv.app
          (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
            ((boundedConstructibleUpperStar _ ℓ g).obj M)) := by
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_eq]
  exact boundedConstructibleExceptionalProjectionMorphism_comp_of_compactifications ℓ f g _ _ T M

end Comp

end AlgebraicGeometry.ProEtale.CondensedRing
