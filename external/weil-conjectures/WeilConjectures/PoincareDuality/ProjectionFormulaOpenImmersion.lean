/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaOfCompactification
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionRefinement
public import WeilConjectures.PoincareDuality.RefinementProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.RefinementCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-!

# The projection formula of an open immersion

Let `j : U ⟶ X` be an open immersion of separated `k`-schemes of finite type. Through the
identification `Rj_! ≅ j_!`
(`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`),
the exceptional projection morphism `PF_j : Rj_! K ⊗ B ⟶ Rj_! (K ⊗ Lj^* B)` of bounded
constructible `ℚ̄_ℓ`-complexes is the inverse of the projection comparison of `j_! ⊣ Lj^*`
(`boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison`,
blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2 and 5.1.2).

The proof follows the definition of `Rj_! ≅ j_!`: the lower shriek `Rj_!` is defined through the
compactification of `j` chosen by Nagata's theorem, compared with the trivial compactification
`(j, 𝟙)` through a common refinement.

1. On bounded constructible complexes, the exceptional projection morphism of a compactification
   `c = (X ⟶[i] Z ⟶[p] Y)` is the projection morphism of `Lp^* ⊣ Rp_*`, followed by the inverse
   projection comparison of `i_! ⊣ Li^*` and the identification `Lf^* ≅ Lp^* ⋙ Li^*`
   (`ProEtale.CondensedRing.homMk_exceptionalProjectionMorphismOfCompactification_eq`).
2. The comparison `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement of factorizations intertwines
   these morphisms
   (`boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp`),
   by the abstract `CategoryTheory.Adjunction.whiskerRight_refinement_comp_exceptionalProjection`;
   hence so does the comparison `Rf_!^{c₁} ≅ Rf_!^{c₂}` of two compactifications
   (`boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp`).
3. For the trivial compactification, the statement is the abstract
   `CategoryTheory.Adjunction.trivial_exceptionalProjection_comp_projectionComparison`
   (`homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion`).

## Implementation notes

The coefficient ring is written `_` wherever it is determined by the bounded constructible
complexes: elaborating `ℚ̲̄_ℓ` explicitly synthesizes its ring structure along a path whose proof
terms differ from those of the categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, and the comparison of the two is
prohibitively expensive. For the same reason the projection of the monoidal structure of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is the preferred tensor product, as in
`WeilConjectures.TraceFormula.KunnethVerdierOpen`.

The comparisons of factorizations are typed by `i_! ⋙ Rp_*` and those of compactifications by
`Rf_!^c`, whose categories carry different proof terms. A concrete comparison applied to objects
elaborated on either side is compared by the kernel by unfolding it completely; the two typings are
therefore related only for a variable natural transformation
(`natTrans_app_whiskerRight_comp_homMk_exceptionalProjectionMorphismOfCompactification`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- The inverse of the composition isomorphism of the trivial compactification `(j, 𝟙)` of an
open immersion is `Lj^*` of the identity isomorphism `L(𝟙 Y)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarCompactificationIso_ofIsOpenImmersion_inv_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompactificationIso Λ (Compactification.ofIsOpenImmersion j)).inv.app M =
      (L((j)^*⟦Λ⟧)).map ((leftDerivedUpperStarId Λ Y).hom.app M) := by
  have h := leftDerivedUpperStarComp_id_right_app Λ j M
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ j (𝟙 Y)).hom.app M), h]
  simp only [leftDerivedUpperStarCompactificationIso, Iso.trans_inv, NatTrans.comp_app,
    eqToIso.inv, eqToHom_app]
  exact Iso.hom_inv_id_app_assoc _ _ _

end General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

section Bridge

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The projection comparison of `j_! ⊣ Lj^*` on bounded constructible complexes is that of the
ambient derived categories. -/
lemma boundedConstructibleOpenImmersionProjectionComparison_hom (M : Dᵇc(U.left)⟦𝐐⟧)
    (N : Dᵇc(X.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).projectionComparison
        M N) =
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j.left).projectionComparison
        M.obj N.obj :=
  Adjunction.ι_map_projectionComparison_restrictFullyFaithful _ _ _ M N

/-- The projection comparison of `j_! ⊣ Lj^*` on bounded constructible `ℚ̄_ℓ`-complexes is an
isomorphism: the derived projection formula for the extension by zero. -/
instance isIso_boundedConstructibleOpenImmersionProjectionComparison (M : Dᵇc(U.left)⟦𝐐⟧)
    (N : Dᵇc(X.left)⟦𝐐⟧) :
    IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
      j).projectionComparison M N) := by
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        j).projectionComparison M N)) := by
    rw [boundedConstructibleOpenImmersionProjectionComparison_hom]
    infer_instance
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

/-- On the ambient derived categories, the extension by zero of bounded constructible complexes acts
on morphisms as that of the derived categories. -/
lemma ι_map_boundedConstructibleOpenImmersionLowerShriek_map {K K' : Dᵇc(U.left)⟦𝐐⟧}
    (φ : K ⟶ K') :
    (boundedConstructible _).ι.map ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).map φ) =
      (D((j.left)_!open⟦_⟧)).map ((boundedConstructible _).ι.map φ) :=
  rfl

end OpenImmersion

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Z ⟶ Y)

/-- The projection morphism of `Lg^* ⊣ Rg_*` on bounded constructible complexes is that of the
ambient derived categories. -/
lemma boundedConstructibleProjectionMorphism_hom (A : Dᵇc(Z.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).projectionMorphism A B) =
      (derivedUpperStarLowerStarAdjunction _ g.left).projectionMorphism A.obj B.obj :=
  Adjunction.ι_map_projectionMorphism_restrictFullyFaithful _ _ _ A B

/-- On the ambient derived categories, the pushforward of bounded constructible complexes acts on
morphisms as that of the derived categories. -/
lemma ι_map_boundedConstructibleLowerStar_map {A A' : Dᵇc(Z.left)⟦𝐐⟧} (φ : A ⟶ A') :
    (boundedConstructible _).ι.map ((boundedConstructibleLowerStar ℓ g).map φ) =
      (R((g.left)_*⟦_⟧)).map ((boundedConstructible _).ι.map φ) :=
  rfl

end LowerStar

/-- The inclusion of bounded constructible complexes into the derived category commutes with
left whiskering. -/
lemma boundedConstructible_ι_map_whiskerLeft {W : Over (Spec (.of k))} [LocallyOfFiniteType W.hom]
    [QuasiCompact W.hom] [IsSeparated W.hom] (A : Dᵇc(W.left)⟦𝐐⟧) {M N : Dᵇc(W.left)⟦𝐐⟧}
    (φ : M ⟶ N) :
    (boundedConstructible _).ι.map (A ◁ φ) = A.obj ◁ (boundedConstructible _).ι.map φ :=
  rfl

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- **The exceptional projection morphism of a compactification on bounded constructible
complexes**: for a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, `PF^c_{K,B}` is the
projection morphism of `Lp^* ⊣ Rp_*` at `i_! K`, followed by `Rp_*` of the inverse of the
projection comparison of `i_! ⊣ Li^*` and of `Li^* Lp^* ≅ Lf^*`. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_eq (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧)
    (ε : (boundedConstructibleUpperStar _ ℓ c.overI).obj
      ((boundedConstructibleUpperStar _ ℓ c.overG).obj B) ⟶
        (boundedConstructibleUpperStar _ ℓ f).obj B)
    (hε : (boundedConstructible _).ι.map ε =
      (leftDerivedUpperStarOverCompactificationIso _ c).inv.app B.obj) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ c.overG).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).obj K) B ≫
        (boundedConstructibleLowerStar ℓ c.overG).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              c.overI).projectionComparison K
              ((boundedConstructibleUpperStar _ ℓ c.overG).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).map
              (K ◁ ε)) := by
  refine (ObjectProperty.fullyFaithfulι (boundedConstructible _)).map_injective ?_
  conv_lhs => rw [ObjectProperty.ι_map, ObjectProperty.homMk_hom,
    exceptionalProjectionMorphismOfCompactification_eq_adjunction]
  conv_rhs =>
    rw [Functor.map_comp, boundedConstructibleProjectionMorphism_hom,
      ι_map_boundedConstructibleLowerStar_map, Functor.map_comp, Functor.map_inv]
    simp only [boundedConstructibleOpenImmersionProjectionComparison_hom]
    rw [ι_map_boundedConstructibleOpenImmersionLowerShriek_map]
    simp only [boundedConstructible_ι_map_whiskerLeft, hε]
  rfl

end Bridge

section Refine

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The projection morphism of a composite** `h ≫ p₁` on bounded constructible complexes: the
projection morphism of `Lp₁^* ⊣ Rp₁_*` followed by `Rp₁_*` of that of `Lh^* ⊣ Rh_*`, through the
composition isomorphisms. -/
lemma boundedConstructibleProjectionMorphism_comp (h : Z ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (A : Dᵇc(Z.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (h ≫ p₁)).projectionMorphism A B =
      (boundedConstructibleLowerStarComp ℓ h p₁).inv.app A ▷ B ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁).projectionMorphism
          ((boundedConstructibleLowerStar ℓ h).obj A) B ≫
        (boundedConstructibleLowerStar ℓ p₁).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ h).projectionMorphism A
            ((boundedConstructibleUpperStar _ ℓ p₁).obj B)) ≫
        (boundedConstructibleLowerStarComp ℓ h p₁).hom.app _ ≫
        (boundedConstructibleLowerStar ℓ (h ≫ p₁)).map
          (A ◁ (boundedConstructibleUpperStarComp _ ℓ h p₁).inv.app B) := by
  rw [Adjunction.projectionMorphism_eq_of_iso _
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ h))
    (boundedConstructibleUpperStarComp _ ℓ h p₁) (fun M N ↦ by
      rw [Functor.OplaxMonoidal.comp_δ]
      exact boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ h p₁ M N) A B,
    Adjunction.projectionMorphism_comp]
  simp only [Category.assoc]
  rfl

section Refinement

variable {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The comparison `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement is `Rp₁_*` of the abstract
pushforward comparison `CategoryTheory.Adjunction.refinementPushforward`, followed by the
composition isomorphism. -/
lemma boundedConstructibleLowerShriekRefinementIso_hom_app (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)]
    [∀ M, IsIso (Adjunction.restrictionComparison
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i₁)
      (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id) M)]
    (M : Dᵇc(X.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekRefinementIso ℓ sq (p₁ := p₁) rfl).hom.app M =
      (boundedConstructibleLowerStar ℓ p₁).map (Adjunction.refinementPushforward
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i₁)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
        (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ
          sq.toCommSq.snd_comp_eq_of_fst_eq_id) M) ≫
        (boundedConstructibleLowerStarComp ℓ h p₁).hom.app _ := by
  have hR := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement 𝐐 ℓ sq
  simp only [boundedConstructibleLowerShriekRefinementIso,
    boundedConstructibleOpenImmersionLowerShriekRefinementPushforward, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, asIso_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, eqToIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, NatIso.isIso_inv_app]
  simp only [boundedConstructibleOpenImmersionLowerShriekRefinement_app,
    Adjunction.refinementPushforward, Functor.map_comp]

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
/-- The composition isomorphisms of the pullbacks along `i₁ = i ≫ h` and `f = i₁ ≫ p₁ = i ≫ h ≫ p₁`
are compatible. -/
lemma boundedConstructibleUpperStarComp_refinement_hom_app {p₁ : Z₁ ⟶ Y} {f : X ⟶ Y}
    (w : i ≫ h = i₁) (hf₁ : i₁ ≫ p₁ = f) (hf : i ≫ h ≫ p₁ = f) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf₁.symm) ≪≫
        boundedConstructibleUpperStarComp 𝐐 ℓ i₁ p₁).hom.app B ≫
      (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ w).hom.app
        ((boundedConstructibleUpperStar 𝐐 ℓ p₁).obj B) =
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf.symm) ≪≫
        boundedConstructibleUpperStarComp 𝐐 ℓ i (h ≫ p₁)).hom.app B ≫
      (boundedConstructibleUpperStar 𝐐 ℓ i).map
        ((boundedConstructibleUpperStarComp 𝐐 ℓ h p₁).hom.app B) := by
  subst w hf₁
  simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp, boundedConstructibleUpperStarComp_assoc_app]
  rw [eqToHom_refl, Category.id_comp]

/-- **The comparison along a refinement intertwines the exceptional projection morphisms**: for
factorizations `f = i ≫ p` and `f = i₁ ≫ p₁` into open immersions followed by morphisms and a
refinement `h` (`i ≫ h = i₁` cartesian, `h ≫ p₁ = p`), the comparison
`ρ : i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` carries the exceptional projection morphism of `(i₁, p₁)` to that
of `(i, p)` (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2). -/
theorem boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp
    (sq : IsPullback (𝟙 X) i i₁ h) {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p) {f : X ⟶ Y}
    (hf : i ≫ p = f) (hf₁ : i₁ ≫ p₁ = f)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)]
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekRefinementIso ℓ sq wp).hom.app K ▷ B ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ i).obj K) B ≫
        (boundedConstructibleLowerStar ℓ p).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              i).projectionComparison K ((boundedConstructibleUpperStar _ ℓ p).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek _ ℓ i).map
              (K ◁ (eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) hf.symm) ≪≫
                boundedConstructibleUpperStarComp _ ℓ i p).inv.app B)) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ i₁).obj K) B ≫
        (boundedConstructibleLowerStar ℓ p₁).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
              i₁).projectionComparison K ((boundedConstructibleUpperStar _ ℓ p₁).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek _ ℓ i₁).map
              (K ◁ (eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) hf₁.symm) ≪≫
                boundedConstructibleUpperStarComp _ ℓ i₁ p₁).inv.app B)) ≫
        (boundedConstructibleLowerShriekRefinementIso ℓ sq wp).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) := by
  subst wp hf
  obtain rfl : i ≫ h = i₁ := sq.toCommSq.snd_comp_eq_of_fst_eq_id
  have hR := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement 𝐐 ℓ sq
  have : ∀ M, IsIso (Adjunction.restrictionComparison
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ (i ≫ h))
      (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id) M) := fun M ↦ by
    rw [← boundedConstructibleOpenImmersionLowerShriekRefinement_app]
    infer_instance
  rw [boundedConstructibleLowerShriekRefinementIso_hom_app,
    boundedConstructibleLowerShriekRefinementIso_hom_app]
  have key := Adjunction.whiskerRight_refinement_comp_exceptionalProjection
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ (i ≫ h))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
    (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ sq.toCommSq.snd_comp_eq_of_fst_eq_id)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (h ≫ p₁))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁)
    (fun K M ↦ by
      refine Adjunction.μ_comp_hom_app_eq_of_δ _ (fun K M ↦ ?_) K M
      simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
        Iso.refl_hom, Category.id_comp, Functor.OplaxMonoidal.comp_δ]
      exact boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ i h K M)
    (boundedConstructibleLowerStarComp ℓ h p₁) (boundedConstructibleUpperStarComp 𝐐 ℓ h p₁)
    (boundedConstructibleProjectionMorphism_comp ℓ h p₁)
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) rfl) ≪≫
      boundedConstructibleUpperStarComp 𝐐 ℓ i (h ≫ p₁))
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf₁.symm) ≪≫
      boundedConstructibleUpperStarComp 𝐐 ℓ (i ≫ h) p₁)
    (boundedConstructibleUpperStarComp_refinement_hom_app ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id hf₁ rfl) K B
  simpa only [Category.assoc] using key

end Refinement

section Compactification

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The composition isomorphism `Lf^* ≅ Lp^* ⋙ Li^*` of a compactification, through
`f = i ≫ p`, is that of the ambient derived categories. -/
lemma ι_map_eqToIso_trans_upperStarComp_inv_app_compactification (c : Compactification f.left)
    (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) c.overI_overG.symm) ≪≫
        boundedConstructibleUpperStarComp _ ℓ c.overI c.overG).inv.app B) =
      (leftDerivedUpperStarOverCompactificationIso _ c).inv.app B.obj := by
  rw [leftDerivedUpperStarOverCompactificationIso_eq]
  exact ι_map_eqToIso_trans_boundedConstructibleUpperStarComp_inv_app _ ℓ c.overI c.overG
    c.overI_overG B

/-- **The comparison along a refinement of compactifications intertwines the exceptional
projection morphisms** (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2). -/
theorem boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp_compactification
    {c d : Compactification f.left} (r : Compactification.OverRefinement d c)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ r.isPullback)]
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekRefinementIso ℓ r.isPullback r.hom_overG).hom.app K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ d K.obj B.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) ≫
        (boundedConstructibleLowerShriekRefinementIso ℓ r.isPullback r.hom_overG).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ d K B _
      (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ d B),
    homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ c K B _
      (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ c B)]
  simpa only [Category.assoc] using
    boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp ℓ r.isPullback
      r.hom_overG d.overI_overG c.overI_overG K B

/-- The comparison `boundedConstructibleLowerShriekRefinementIso` along a refinement of
compactifications intertwines the exceptional projection morphisms, through its inverse. -/
theorem boundedConstructibleLowerShriekRefinementIso_inv_app_whiskerRight_comp_compactification
    {c d : Compactification f.left} (r : Compactification.OverRefinement d c)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ r.isPullback)]
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
        (exceptionalProjectionMorphismOfCompactification _ d K.obj B.obj) ≫
        (boundedConstructibleLowerShriekRefinementIso ℓ r.isPullback r.hom_overG).inv.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) =
      (boundedConstructibleLowerShriekRefinementIso ℓ r.isPullback r.hom_overG).inv.app K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) := by
  rw [← cancel_mono ((boundedConstructibleLowerShriekRefinementIso ℓ r.isPullback
      r.hom_overG).hom.app _), Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Category.assoc,
    ← boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp_compactification ℓ r K
      B, ← comp_whiskerRight_assoc, Iso.inv_hom_id_app]
  erw [id_whiskerRight, Category.id_comp]

/-- A natural transformation `i_! ⋙ Rp_* ⟶ i'_! ⋙ Rp'_*` between the lower shrieks of two
compactifications which intertwines their exceptional projection morphisms also does so as a
natural transformation `Rf_!^c ⟶ Rf_!^d`.

The two statements agree up to unfolding `boundedConstructibleLowerShriekOfCompactification`; the
natural transformation is a variable so that the kernel compares them without unfolding it. -/
theorem natTrans_app_whiskerRight_comp_homMk_exceptionalProjectionMorphismOfCompactification
    {c d : Compactification f.left}
    (η : boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ c.overI ⋙
        boundedConstructibleLowerStar ℓ c.overG ⟶
      boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ d.overI ⋙
        boundedConstructibleLowerStar ℓ d.overG)
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧)
    (h : η.app K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ d K.obj B.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) ≫
        η.app (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B)) :
    @NatTrans.app _ _ _ _ (boundedConstructibleLowerShriekOfCompactification ℓ c)
        (boundedConstructibleLowerShriekOfCompactification ℓ d) η K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ d K.obj B.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) ≫
        @NatTrans.app _ _ _ _ (boundedConstructibleLowerShriekOfCompactification ℓ c)
          (boundedConstructibleLowerShriekOfCompactification ℓ d) η
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) := h

/-- `natTrans_app_whiskerRight_comp_homMk_exceptionalProjectionMorphismOfCompactification` for a
natural transformation in the other direction. -/
theorem homMk_exceptionalProjectionMorphismOfCompactification_comp_natTrans_app
    {c d : Compactification f.left}
    (η : boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ d.overI ⋙
        boundedConstructibleLowerStar ℓ d.overG ⟶
      boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ c.overI ⋙
        boundedConstructibleLowerStar ℓ c.overG)
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧)
    (h : ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ d K.obj B.obj) ≫
        η.app (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) =
      η.app K ▷ B ≫ ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj)) :
    ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ d).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ d K.obj B.obj) ≫
        @NatTrans.app _ _ _ _ (boundedConstructibleLowerShriekOfCompactification ℓ d)
          (boundedConstructibleLowerShriekOfCompactification ℓ c) η
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) =
      @NatTrans.app _ _ _ _ (boundedConstructibleLowerShriekOfCompactification ℓ d)
          (boundedConstructibleLowerShriekOfCompactification ℓ c) η K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) := h

/-- The comparison `boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl` of the lower
shrieks of two compactifications intertwines the exceptional projection morphisms. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_hom_app_whiskerRight_comp
    (c₁ c₂ : Compactification f.left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂).hom.app K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c₂).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c₂).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c₂ K.obj B.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c₁).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c₁).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c₁ K.obj B.obj) ≫
        (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) := by
  have := (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isProper
  have := (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
  have h₁ := boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp_compactification
    ℓ (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some K B
  have h₂ := boundedConstructibleLowerShriekRefinementIso_inv_app_whiskerRight_comp_compactification
    ℓ (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some K B
  have h₁' := natTrans_app_whiskerRight_comp_homMk_exceptionalProjectionMorphismOfCompactification
    ℓ (boundedConstructibleLowerShriekRefinementIso ℓ
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.hom_overG).hom K B h₁
  have h₂' := homMk_exceptionalProjectionMorphismOfCompactification_comp_natTrans_app
    ℓ (boundedConstructibleLowerShriekRefinementIso ℓ
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.hom_overG).inv K B h₂
  rw [boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq_refinementIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, comp_whiskerRight]
  rw [← h₂', ← Category.assoc, h₁', Category.assoc]

/-- **The comparison of the lower shrieks of two compactifications intertwines the exceptional
projection morphisms** (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2): through
`Rf_!^{c₁} ≅ Rf_!^{c₂}`, the exceptional projection morphism of `c₁` is that of `c₂`. -/
theorem boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp
    (c₁ c₂ : Compactification f.left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂).hom.app K ▷ B ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c₂).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c₂).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c₂ K.obj B.obj) =
      ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c₁).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c₁).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification _ c₁ K.obj B.obj) ≫
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁ c₂).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) := by
  rw [← boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq']
  exact boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_hom_app_whiskerRight_comp ℓ
    c₁ c₂ K B

end Compactification

end Refine

section Trivial

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The inverse of the composition isomorphism of the trivial compactification `(j, 𝟙)` of an
open immersion is `Lj^*` of the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`. -/
lemma ι_map_upperStar_map_upperStarId_hom_app (B : Dᵇc(X.left)⟦𝐐⟧) :
    (boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar _ ℓ (Compactification.ofIsOpenImmersion j.left).overI).map
        ((boundedConstructibleUpperStarId _ ℓ X).hom.app B)) =
      (leftDerivedUpperStarOverCompactificationIso _
        (Compactification.ofIsOpenImmersion j.left)).inv.app B.obj := by
  rw [leftDerivedUpperStarOverCompactificationIso,
    leftDerivedUpperStarCompactificationIso_ofIsOpenImmersion_inv_app,
    ← boundedConstructibleUpperStarId_hom_app_hom _ ℓ (X := X) B]
  rfl

/-- **The projection formula of the trivial compactification** `(j, 𝟙)` of an open immersion:
through `R(𝟙 X)_* ≅ 𝟭`, the exceptional projection morphism followed by the projection comparison
of `j_! ⊣ Lj^*` is the identification. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion
    (K : Dᵇc(U.left)⟦𝐐⟧) (B : Dᵇc(X.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsOpenImmersion j.left)).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsOpenImmersion j.left)).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ j).obj B))
        (exceptionalProjectionMorphismOfCompactification _
          (Compactification.ofIsOpenImmersion j.left) K.obj B.obj) ≫
      (boundedConstructibleLowerStarId ℓ X).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek _ ℓ
          j).obj (K ⊗ (boundedConstructibleUpperStar _ ℓ j).obj B)) ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          j).projectionComparison K B =
      (boundedConstructibleLowerStarId ℓ X).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj K) ▷ B := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ _ K B _
    (ι_map_upperStar_map_upperStarId_hom_app ℓ j B)]
  exact Adjunction.trivial_exceptionalProjection_comp_projectionComparison _ _ _
    (fun X' Y' ↦ boundedConstructibleUpperStarId_hom_app_tensor_δ ℓ X X' Y') K B

/-- `homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion` through the
identification `j_! ⋙ R(𝟙 X)_* ≅ j_!`. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion'
    (K : Dᵇc(U.left)⟦𝐐⟧) (B : Dᵇc(X.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsOpenImmersion j.left)).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ
          (Compactification.ofIsOpenImmersion j.left)).obj
            (K ⊗ (boundedConstructibleUpperStar _ ℓ j).obj B))
        (exceptionalProjectionMorphismOfCompactification _
          (Compactification.ofIsOpenImmersion j.left) K.obj B.obj) ≫
      (Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
          (boundedConstructibleLowerStarId ℓ X) ≪≫ Functor.rightUnitor _).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ j).obj B) ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          j).projectionComparison K B =
      (Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
          (boundedConstructibleLowerStarId ℓ X) ≪≫ Functor.rightUnitor _).hom.app K ▷ B := by
  have hW : ∀ M, (Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
      (boundedConstructibleLowerStarId ℓ X) ≪≫ Functor.rightUnitor _).hom.app M =
      (boundedConstructibleLowerStarId ℓ X).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).obj M) := fun M ↦
    Category.comp_id _
  rw [hW, hW]
  exact homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion ℓ j K B

end Trivial

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **The projection formula of an open immersion is the adjoint of the monoidal structure of the
pullback** (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2 and 5.1.2): for an open
immersion `j`, through the identification `Rj_! ≅ j_!` with the extension by zero, the projection
morphism `PF_j : Rj_! K ⊗ B ⟶ Rj_! (K ⊗ Lj^* B)` is the inverse of the projection comparison
`j_! (K ⊗ Lj^* B) ⟶ j_! K ⊗ B` of the adjunction `j_! ⊣ Lj^*`, the adjoint of the tensor
structure of `Lj^*`. -/
theorem boundedConstructibleExceptionalProjectionMorphism_comp_projectionComparison
    (K : Dᵇc(U.left)⟦𝐐⟧) (B : Dᵇc(X.left)⟦𝐐⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ j K B ≫
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ j).obj B) ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          j).projectionComparison K B =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).hom.app K ▷
        B := by
  have h₃ := homMk_exceptionalProjectionMorphismOfCompactification_ofIsOpenImmersion' ℓ j K B
  have hI : boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j =
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField j) (.ofIsOpenImmersion j.left) ≪≫
      (Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
        (boundedConstructibleLowerStarId ℓ X) ≪≫ Functor.rightUnitor _) := rfl
  rw [hI]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, comp_whiskerRight] at h₃ ⊢
  change ObjectProperty.homMk _ ≫ _ = _
  rw [← reassoc_of%
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp
    ℓ (compactificationOverField j) (.ofIsOpenImmersion j.left) K B)]
  exact congrArg (fun t ↦ _ ▷ B ≫ t) h₃

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
