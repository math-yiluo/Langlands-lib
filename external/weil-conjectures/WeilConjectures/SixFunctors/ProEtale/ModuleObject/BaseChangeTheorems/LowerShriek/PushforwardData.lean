/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!
# Pushforward data for the bounded constructible six functors

For a general coefficient ring `Λ`, only the pullbacks `Lf^*` and the extensions by zero `j_!`
along open immersions are defined on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`;
the pushforwards `Rf_*` are defined separately for each of the `ℓ`-adic coefficient rings. A
*pushforward datum* for `Λ` (`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`) consists
of functors `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` with adjunctions `Lf^* ⊣ Rf_*`. From such a datum, this
file defines, by the same formulas as for the `ℓ`-adic coefficient rings
(the files `MorphismDefs` and `CompactificationIndependence` of this directory):

* the composition isomorphisms `Rh_* ⋙ Rp_* ≅ R(h ≫ p)_*`;
* the base change morphism `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`;
* the lower shriek `Rf_!^c = i_! ⋙ Rp_*` of a compactification and the compact-support base
  change morphism for a compactification;
* the comparisons along a refinement of compactifications and the independence isomorphisms
  `Rf_!^{c₁} ≅ Rf_!^{c₂}`, through the common refinement chosen by
  `Compactification.exists_overRefinement`;
* the compact-support base change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for the chosen
  compactifications.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- A *pushforward datum* for the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`: functors
`Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` with adjunctions `Lf^* ⊣ Rf_*`. -/
structure BoundedConstructiblePushforwardData where
  /-- The pushforward `Rf_* : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧`. -/
  lowerStar {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧
  /-- The adjunction `Lf^* ⊣ Rf_*`. -/
  adj {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : boundedConstructibleUpperStar Λ ℓ f ⊣ lowerStar f

namespace BoundedConstructiblePushforwardData

variable {Λ ℓ k} (P : BoundedConstructiblePushforwardData Λ ℓ k)

section LowerStar

variable {X Y Z X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`: the conjugate of
`boundedConstructibleUpperStarComp`. -/
noncomputable def lowerStarComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.lowerStar f ⋙ P.lowerStar g ≅ P.lowerStar (f ≫ g) :=
  (conjugateIsoEquiv (P.adj (f ≫ g)) ((P.adj g).comp (P.adj f))
    (boundedConstructibleUpperStarComp Λ ℓ f g).symm).symm

/-- The base change morphism `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of a commutative square: the
exchange morphism of the pullback comparison under the adjunctions `Lf^* ⊣ Rf_*` and
`Lf'^* ⊣ Rf'_*`. -/
noncomputable def baseChange {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    P.lowerStar f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ P.lowerStar f' :=
  Adjunction.exchangeRight (P.adj f) (P.adj f')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq)

end LowerStar

section Compactification

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_*` attached to a compactification
`c = (X ⟶[i] Z ⟶[p] Y)` of `f`. -/
noncomputable def lowerShriekOfCompactification (c : Compactification f.left) :
    Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ⋙ P.lowerStar c.overG

/-- The compact-support base change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
for a compactification `c` of `f`: the pasting of the base change morphism of the proper square
of the base-changed compactification with the inverse of the extension-by-zero exchange of its
open-immersion square. -/
noncomputable def lowerShriekOfCompactificationBaseChangePasting (c : Compactification f.left)
    (sq : IsPullback g' f' f g) :
    P.lowerShriekOfCompactification c ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        P.lowerShriekOfCompactification (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI)
      (P.baseChange (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (P.lowerStar (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

end Compactification

section Refinement

variable {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a cartesian square of open immersions `i`,
`i₁` and a morphism `h`: the unit of `Lh^* ⊣ Rh_*` followed by the inverse of the restriction
comparison `i_! ⟶ i₁_! ⋙ Lh^*`. -/
noncomputable def openImmersionLowerShriekRefinementPushforward (sq : IsPullback (𝟙 X) i i₁ h) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⋙ P.lowerStar h :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (P.adj h).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) _

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p`, when the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` is an isomorphism. -/
noncomputable def lowerShriekRefinementIso (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (P.openImmersionLowerShriekRefinementPushforward sq)] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙ P.lowerStar p₁ ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⋙ P.lowerStar p :=
  Functor.isoWhiskerRight (asIso (P.openImmersionLowerShriekRefinementPushforward sq)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (P.lowerStarComp h p₁ ≪≫ eqToIso (by rw [wp]))

end Refinement

/-- The pushforward comparisons `i₁_! ⟶ i_! ⋙ Rh_*` along proper refinements `h` with cartesian
square are isomorphisms. -/
def IsIsoRefinementPushforward : Prop :=
  ∀ {X Z Z₁ : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom] [IsSeparated Z₁.hom]
    {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]
    [IsProper h.left] (sq : IsPullback (𝟙 X) i i₁ h),
    IsIso (P.openImmersionLowerShriekRefinementPushforward sq)

section Independence

variable {P} (hP : P.IsIsoRefinementPushforward) {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The independence of the lower shriek from the compactification: for two compactifications
`c₁` and `c₂` of `f`, the composite `Rf_!^{c₁} ≅ Rf_!^c ≅ Rf_!^{c₂}` of the isomorphisms along
the refinements, for the common refinement `c` chosen by
`Compactification.exists_overRefinement`. -/
noncomputable def lowerShriekOfCompactificationIso {f : X ⟶ Y}
    (c₁ c₂ : Compactification f.left) :
    P.lowerShriekOfCompactification c₁ ≅ P.lowerShriekOfCompactification c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := hP r₁.isPullback
  have := hP r₂.isPullback
  P.lowerShriekRefinementIso r₁.isPullback r₁.hom_overG ≪≫
    (P.lowerShriekRefinementIso r₂.isPullback r₂.hom_overG).symm

/-- The compact-support base change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for the lower
shrieks of the chosen compactifications `c_f` and `c_{f'}`: the pasting for `c_f`, followed by
the independence isomorphism from `c_f.ofIsPullback sq` to `c_{f'}`. -/
noncomputable def lowerShriekBaseChange {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) :
    P.lowerShriekOfCompactification (compactificationOverField f) ⋙
      boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        P.lowerShriekOfCompactification (compactificationOverField f') :=
  P.lowerShriekOfCompactificationBaseChangePasting (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (lowerShriekOfCompactificationIso hP
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

end Independence

end BoundedConstructiblePushforwardData

end AlgebraicGeometry.ProEtale.CondensedRing
