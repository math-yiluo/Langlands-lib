/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardData

/-!
# The exchange formalism of a pushforward datum

A pushforward datum `P` for a coefficient ring `Λ`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`) makes the bounded constructible
derived categories `Dᵇc(X)⟦Λ⟧` of the separated `k`-schemes of finite type, with the derived
pullbacks `Lf^*`, the pushforwards `Rf_*` of `P` and the extensions by zero `j_!` along open
immersions, into a `CategoryTheory.ExchangeFormalism`
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData.exchangeFormalism`), exactly as for
the coefficient ring `ℚ̲̄_ℓ` (`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`).

This file identifies the pullback comparisons of commutative squares, the base change morphisms
`Ex_*` of `P`, the extension-by-zero exchange morphisms, the composition isomorphisms of the
pushforwards and the comparisons `P.lowerShriekRefinementIso` along refinements with the
corresponding constructions of the exchange formalism, so that the formal coherence results of
`CategoryTheory.ExchangeFormalism` apply to them.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace BoundedConstructiblePushforwardData

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (P : BoundedConstructiblePushforwardData Λ ℓ k)

/-- **The exchange formalism of a pushforward datum** `P`: the bounded constructible derived
categories `Dᵇc(X)⟦Λ⟧` of the separated `k`-schemes of finite type, with the derived pullbacks
`Lf^*`, their composition and identity isomorphisms, the pushforwards `Rf_*` of `P` and the
extensions by zero `j_!` along open immersions. -/
noncomputable def exchangeFormalism :
    ExchangeFormalism (SepFinType k) SepFinType.openImmersion where
  obj X := Dᵇc(X.obj.left)⟦Λ⟧
  pb f := boundedConstructibleUpperStar Λ ℓ f.hom
  pbId X := boundedConstructibleUpperStarId Λ ℓ X.obj
  pbComp f g := boundedConstructibleUpperStarComp Λ ℓ f.hom g.hom
  pbComp_assoc f g h M := boundedConstructibleUpperStarComp_assoc_app Λ ℓ f.hom g.hom h.hom M
  pbId_comp f M := boundedConstructibleUpperStarComp_id_left_app Λ ℓ f.hom M
  pbComp_id f M := boundedConstructibleUpperStarComp_id_right_app Λ ℓ f.hom M
  pf f := P.lowerStar f.hom
  adj f := P.adj f.hom
  sh j _ := boundedConstructibleOpenImmersionLowerShriek Λ ℓ j.hom
  shAdj j _ := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j.hom

/-- The exchange formalism of the pushforward datum `P`. -/
local notation "𝔽" => exchangeFormalism P

section Squares

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square is the square
isomorphism of the exchange formalism of `P`. -/
lemma boundedConstructiblePullbackSquareComparison_eq_sqIso (sq : CommSq g' f' f g) :
    boundedConstructiblePullbackSquareComparison Λ ℓ sq =
      (𝔽).sqIso (SepFinType.homMk f') (SepFinType.homMk g') (SepFinType.homMk g)
        (SepFinType.homMk f) (SepFinType.homMk_comp_homMk sq.w.symm) := by
  rw [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp'_rfl]
  unfold ExchangeFormalism.pbComp' boundedConstructiblePullbackSquareComparison
  rfl

/-- The base change morphism `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of `P` is the base change map
of the pushforwards of the exchange formalism of `P`. -/
lemma baseChange_eq_pfBaseChange (sq : CommSq g' f' f g) :
    P.baseChange sq =
      ((𝔽).pfBaseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [baseChange, Adjunction.exchangeRight_eq_mateEquiv, ExchangeFormalism.pfBaseChange,
    P.boundedConstructiblePullbackSquareComparison_eq_sqIso, ← Iso.symm_hom,
    ExchangeFormalism.sqIso_symm]
  rfl

variable [IsOpenImmersion f.left] [IsOpenImmersion f'.left]

/-- The extension-by-zero exchange morphism `Lg'^* ⋙ f'_! ⟶ f_! ⋙ Lg^*` of a commutative square
of open immersions is the base change map of the extension by zero of the exchange formalism of
`P`. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange
    (sq : CommSq g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq =
      ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
    Adjunction.exchangeLeft_eq_mateEquiv_symm, ExchangeFormalism.baseChange,
    P.boundedConstructiblePullbackSquareComparison_eq_sqIso]
  rfl

/-- Base change for extension by zero in the exchange formalism of `P`: the base change map of a
cartesian square of open immersions is an isomorphism. -/
lemma isIso_baseChange_exchangeFormalism (sq : IsPullback g' f' f g) :
    IsIso ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
      (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [← P.boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange]
  exact isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq

/-- The extension-by-zero base-change isomorphism `f_! ⋙ Lg^* ≅ Lg'^* ⋙ f'_!` of a cartesian
square is the inverse of the base change map of the extension by zero of the exchange formalism
of `P`. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq
    (sq : IsPullback g' f' f g) :
    haveI := P.isIso_baseChange_exchangeFormalism sq
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom =
      inv ((𝔽).baseChange (SepFinType.homMk g') (SepFinType.homMk f') (SepFinType.homMk f)
        (SepFinType.homMk g) (SepFinType.homMk_comp_homMk sq.w)) := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso, Iso.symm_hom, asIso_inv]
  simp only [P.boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_baseChange]

end Squares

section Refinement

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- Base change for extension by zero in the exchange formalism of `P`, for a cartesian square
with an identity as top side. -/
lemma isIso_baseChange_exchangeFormalism_id (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk i) (SepFinType.homMk i₁)
      (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)) :=
  P.isIso_baseChange_exchangeFormalism sq

/-- The inverse of the composition isomorphism of the pushforwards of the exchange formalism of
`P` along `h ≫ p₁` is the composition isomorphism `Rh_* ⋙ Rp₁_* ≅ R(h ≫ p₁)_*` of `P`. -/
lemma pfComp'_homMk_comp_inv {p₁ : Z₁ ⟶ Y} (hp : SepFinType.homMk h ≫ SepFinType.homMk p₁ =
      SepFinType.homMk (h ≫ p₁)) :
    ((𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁) (SepFinType.homMk (h ≫ p₁))
      hp).inv = (P.lowerStarComp h p₁).hom := by
  have hrfl : (𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁)
      (SepFinType.homMk (h ≫ p₁)) hp = (𝔽).pfComp' (SepFinType.homMk h) (SepFinType.homMk p₁)
        (SepFinType.homMk h ≫ SepFinType.homMk p₁) rfl :=
    rfl
  rw [hrfl, ExchangeFormalism.pfComp', ExchangeFormalism.pbComp'_rfl, lowerStarComp]
  rfl

variable (Λ ℓ) in
/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` is the exchange morphism of the triangle
comparison. -/
lemma openImmersionLowerShriekRefinement_eq_exchangeLeft (w : i ≫ h = i₁) :
    boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
        (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ ℓ w) := by
  unfold boundedConstructibleOpenImmersionLowerShriekRefinement
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep
    boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep Adjunction.exchangeLeft
  rfl

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
/-- The triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` is the composition isomorphism of the
pullbacks of the exchange formalism of `P`. -/
lemma boundedConstructibleUpperStarTriangleComparison_eq_pbComp' (w : i ≫ h = i₁) :
    boundedConstructibleUpperStarTriangleComparison Λ ℓ w =
      (𝔽).pbComp' (SepFinType.homMk i) (SepFinType.homMk h) (SepFinType.homMk i₁)
        (ObjectProperty.hom_ext _ w) :=
  rfl

/-- The comparison isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` of `P` along a refinement
(`BoundedConstructiblePushforwardData.lowerShriekRefinementIso`) is the comparison along a
refinement of the exchange formalism of `P`. -/
lemma lowerShriekRefinementIso_hom_eq (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (P.openImmersionLowerShriekRefinementPushforward sq)] :
    haveI := P.isIso_baseChange_exchangeFormalism_id sq
    (P.lowerShriekRefinementIso sq wp).hom =
      (𝔽).refinementComparison (SepFinType.homMk i) (SepFinType.homMk p) (SepFinType.homMk i₁)
        (SepFinType.homMk p₁) (SepFinType.homMk h) (SepFinType.homMk_comp_homMk (a := 𝟙 X) sq.w)
        (ObjectProperty.hom_ext _ wp) := by
  subst wp
  have hw : i ≫ h = i₁ := sq.toCommSq.snd_comp_eq_of_fst_eq_id
  have hR := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  have := P.isIso_baseChange_exchangeFormalism_id sq
  have : IsIso (Adjunction.exchangeLeft ((𝔽).shAdj (SepFinType.homMk i₁))
      ((𝔽).shAdj (SepFinType.homMk i)) (Functor.rightUnitor ((𝔽).pb (SepFinType.homMk i₁)) ≪≫
        (𝔽).pbComp' (SepFinType.homMk i) (SepFinType.homMk h) (SepFinType.homMk i₁)
          (ObjectProperty.hom_ext _ hw))) := by
    rwa [openImmersionLowerShriekRefinement_eq_exchangeLeft,
      P.boundedConstructibleUpperStarTriangleComparison_eq_pbComp'] at hR
  rw [ExchangeFormalism.refinementComparison_eq_exchangeLeft _ _ _ _ _ _ _ _
    (ObjectProperty.hom_ext _ hw)]
  refine NatTrans.ext (funext fun K ↦ ?_)
  simp only [lowerShriekRefinementIso, openImmersionLowerShriekRefinementPushforward,
    openImmersionLowerShriekRefinement_eq_exchangeLeft,
    P.boundedConstructibleUpperStarTriangleComparison_eq_pbComp', P.pfComp'_homMk_comp_inv,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, asIso_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.map_comp, Functor.rightUnitor_inv_app, Category.assoc,
    Functor.comp_obj, Functor.comp_map]
  rfl

end Refinement

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The lower shriek of `P` attached to a compactification is the compactly supported direct
image of the exchange formalism of `P`. -/
lemma lowerShriekOfCompactification_eq_shriek (c : Compactification f.left) :
    P.lowerShriekOfCompactification c =
      (𝔽).shriek (SepFinType.homMk c.overI) (SepFinType.homMk c.overG) :=
  rfl

end Shriek

end BoundedConstructiblePushforwardData

end AlgebraicGeometry.ProEtale.CondensedRing
