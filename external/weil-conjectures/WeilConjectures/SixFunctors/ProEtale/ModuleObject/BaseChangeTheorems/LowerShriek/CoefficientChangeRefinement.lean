/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePasting

/-!
# Coefficient changes and the independence of the lower shriek from the compactification

Let `C` be a coefficient change `Λ ⟶ Λ'` of the bounded constructible six functors
(`ProEtale.CondensedRing.BoundedConstructibleCoefficientChange`). For a refinement `h : Z ⟶ Z₁`
of compactifications `X ⟶[i] Z ⟶[p] Y` and `X ⟶[i₁] Z₁ ⟶[p₁] Y`, the comparisons along the
refinement of `CompactificationIndependence` are compatible with the coefficient comparisons of
`C`:

* the restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*`, an exchange morphism for the adjunctions
  `i_! ⊣ Li^*` and `i₁_! ⊣ Li₁^*`
  (`...squareCompatible_openImmersionLowerShriekRefinement`);
* the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*`
  (`...squareCompatible_openImmersionLowerShriekRefinementPushforward`);
* the isomorphism `Rf_!^{c₁} ≅ Rf_!^c` (`...squareCompatible_lowerShriekRefinementIso`) and the
  isomorphisms `Rf_!^{c₁} ≅ Rf_!^{c₂}` through a common refinement
  (`...squareCompatible_lowerShriekRefinementIso_trans_symm`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {ℓ : ℕ} [Fact ℓ.Prime]
  [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- For any coefficient ring `Λ`, the restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` along a refinement
is the exchange morphism of the triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` for the adjunctions
`i₁_! ⊣ Li₁^*` and `i_! ⊣ Li^*`. -/
lemma boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft' (w : i ≫ h = i₁) :
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

namespace BoundedConstructibleCoefficientChange

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  {P : BoundedConstructiblePushforwardData Λ ℓ k} {P' : BoundedConstructiblePushforwardData Λ' ℓ k}
  {T : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom], Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧}
  {pull : ∀ {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y),
    boundedConstructibleUpperStar Λ ℓ f ⋙ T X ≅ T Y ⋙ boundedConstructibleUpperStar Λ' ℓ f}
  (C : BoundedConstructibleCoefficientChange Λ Λ' ℓ P P' T pull)

/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` along a refinement is compatible with the
coefficient comparisons. -/
lemma squareCompatible_openImmersionLowerShriekRefinement (w : i ≫ h = i₁) :
    NatTrans.SquareCompatible (C.shriek i) (Functor.pasteSquareIso (C.shriek i₁) (pull h))
      (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w)
      (boundedConstructibleOpenImmersionLowerShriekRefinement Λ' ℓ w) := by
  have hθ := (NatTrans.SquareCompatible.rightUnitor_hom (pull i₁)).comp
    ((squareCompatible_eqToHom pull w.symm (by rw [w]) (by rw [w])).comp (C.pull_comp i h))
  have hθ' : NatTrans.SquareCompatible
      (Functor.pasteSquareIso (pull i₁) (Functor.idSquareIso (T X)))
      (Functor.pasteSquareIso (pull h) (pull i))
      (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom
      (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ' ℓ w).hom := by
    simpa only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso.hom]
      using hθ
  have h := NatTrans.SquareCompatible.exchangeLeft (ιH := Functor.idSquareIso (T X))
    (C.isMateSquare_shriek_pull i₁) (C.isMateSquare_shriek_pull i) hθ'
  rw [boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft',
    boundedConstructibleOpenImmersionLowerShriekRefinement_eq_exchangeLeft']
  exact NatTrans.SquareCompatible.of_pasteSquareIso_idSquareIso h

/-- The pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` along a refinement with cartesian square is
compatible with the coefficient comparisons. -/
lemma squareCompatible_openImmersionLowerShriekRefinementPushforward [IsProper h.left]
    (sq : IsPullback (𝟙 X) i i₁ h) :
    NatTrans.SquareCompatible (C.shriek i₁) (Functor.pasteSquareIso (C.shriek i) (C.push h))
      (P.openImmersionLowerShriekRefinementPushforward sq)
      (P'.openImmersionLowerShriekRefinementPushforward sq) := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ' ℓ sq
  exact (NatTrans.SquareCompatible.rightUnitor_inv _).comp
    ((NatTrans.SquareCompatible.whiskerLeft _
      (NatTrans.SquareCompatible.unit (C.isMateSquare_pull_push h))).comp
    ((NatTrans.SquareCompatible.associator_inv _ _ _).comp
    (NatTrans.SquareCompatible.whiskerRight _
      (C.squareCompatible_openImmersionLowerShriekRefinement
        sq.toCommSq.snd_comp_eq_of_fst_eq_id).isIso_inv)))

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- (Push) is compatible with the identifications `Rp_* = Rp'_*` for equal proper morphisms. -/
lemma squareCompatible_push_eqToHom {p p' : Z ⟶ Y} [IsProper p.left] [IsProper p'.left]
    (hp : p = p') (h₁ : P.lowerStar p = P.lowerStar p') (h₂ : P'.lowerStar p = P'.lowerStar p') :
    NatTrans.SquareCompatible (C.push p) (C.push p') (eqToHom h₁) (eqToHom h₂) := by
  subst hp
  simpa only [eqToHom_refl] using NatTrans.SquareCompatible.id (C.push p)

/-- (Push) is compatible with the composition isomorphisms `Rh_* ⋙ Rp_* ≅ R(h ≫ p)_*`, the
conjugates of the composition isomorphisms of the pullbacks. -/
lemma squareCompatible_lowerStarComp {p : Z₁ ⟶ Y} [IsProper h.left] [IsProper p.left]
    [IsProper (h ≫ p).left] :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.push h) (C.push p)) (C.push (h ≫ p))
      (P.lowerStarComp h p).hom (P'.lowerStarComp h p).hom :=
  NatTrans.SquareCompatible.conjugateEquiv
    ((C.isMateSquare_pull_push p).comp (C.isMateSquare_pull_push h))
    (C.isMateSquare_pull_push (h ≫ p)) (C.pull_comp h p)

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement is compatible with the
coefficient comparisons: the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` is, and (Push) commutes
with the composition isomorphism `Rh_* ⋙ Rp_* ≅ R(h ≫ p)_*` since (Push) is the mate of (Pull) and
transposes of composites are composites. -/
lemma squareCompatible_lowerShriekRefinementIso [IsProper h.left] (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} [IsProper p₁.left] [IsProper p.left] (wp : h ≫ p₁ = p)
    [IsIso (P.openImmersionLowerShriekRefinementPushforward sq)]
    [IsIso (P'.openImmersionLowerShriekRefinementPushforward sq)] :
    NatTrans.SquareCompatible (Functor.pasteSquareIso (C.shriek i₁) (C.push p₁))
      (Functor.pasteSquareIso (C.shriek i) (C.push p))
      (P.lowerShriekRefinementIso sq wp).hom (P'.lowerShriekRefinementIso sq wp).hom := by
  have : IsProper (h ≫ p₁).left := by
    rw [Over.comp_left]
    infer_instance
  -- (Push) is compatible with the composition isomorphism `Rh_* ⋙ Rp₁_* ≅ R(h ≫ p₁)_*`: the
  -- composition isomorphisms are the conjugates of those of the pullbacks, (Push) is the mate of
  -- (Pull), and (Pull) is compatible with composition; transposes of composites are composites.
  have hcomp : NatTrans.SquareCompatible (Functor.pasteSquareIso (C.push h) (C.push p₁))
      (C.push (h ≫ p₁)) (P.lowerStarComp h p₁).hom (P'.lowerStarComp h p₁).hom :=
    NatTrans.SquareCompatible.conjugateEquiv
      ((C.isMateSquare_pull_push p₁).comp (C.isMateSquare_pull_push h))
      (C.isMateSquare_pull_push (h ≫ p₁)) (C.pull_comp h p₁)
  have h₁ := (NatTrans.SquareCompatible.whiskerRight (C.push p₁)
      (C.squareCompatible_openImmersionLowerShriekRefinementPushforward sq)).comp
    ((NatTrans.SquareCompatible.associator_hom _ _ _).comp
    (NatTrans.SquareCompatible.whiskerLeft (C.shriek i)
      (hcomp.comp (C.squareCompatible_push_eqToHom wp (by rw [wp]) (by rw [wp])))))
  simpa only [BoundedConstructiblePushforwardData.lowerShriekRefinementIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, asIso_hom, eqToIso.hom,
    Functor.whiskerLeft_comp] using h₁

section Independence

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The isomorphism `Rf_!^{c₁} ≅ Rf_!^{c₂}` through a common refinement `c` of `c₁` and `c₂` is
compatible with the coefficient comparisons. -/
lemma squareCompatible_lowerShriekRefinementIso_trans_symm {c c₁ c₂ : Compactification f.left}
    (r₁ : c.OverRefinement c₁) (r₂ : c.OverRefinement c₂)
    [IsIso (P.openImmersionLowerShriekRefinementPushforward r₁.isPullback)]
    [IsIso (P'.openImmersionLowerShriekRefinementPushforward r₁.isPullback)]
    [IsIso (P.openImmersionLowerShriekRefinementPushforward r₂.isPullback)]
    [IsIso (P'.openImmersionLowerShriekRefinementPushforward r₂.isPullback)] :
    NatTrans.SquareCompatible (C.shriekOfCompactification c₁) (C.shriekOfCompactification c₂)
      (P.lowerShriekRefinementIso r₁.isPullback r₁.hom_overG ≪≫
        (P.lowerShriekRefinementIso r₂.isPullback r₂.hom_overG).symm).hom
      (P'.lowerShriekRefinementIso r₁.isPullback r₁.hom_overG ≪≫
        (P'.lowerShriekRefinementIso r₂.isPullback r₂.hom_overG).symm).hom := by
  have := r₁.isProper
  have := r₂.isProper
  exact (C.squareCompatible_lowerShriekRefinementIso r₁.isPullback r₁.hom_overG).comp
    (C.squareCompatible_lowerShriekRefinementIso r₂.isPullback r₂.hom_overG).inv

/-- The independence isomorphism `Rf_!^{c₁} ≅ Rf_!^{c₂}` is compatible with the coefficient
comparisons. -/
lemma squareCompatible_lowerShriekOfCompactificationIso (hP : P.IsIsoRefinementPushforward)
    (hP' : P'.IsIsoRefinementPushforward) (c₁ c₂ : Compactification f.left) :
    NatTrans.SquareCompatible (C.shriekOfCompactification c₁) (C.shriekOfCompactification c₂)
      (BoundedConstructiblePushforwardData.lowerShriekOfCompactificationIso hP c₁ c₂).hom
      (BoundedConstructiblePushforwardData.lowerShriekOfCompactificationIso hP' c₁ c₂).hom := by
  have := (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isProper
  have := (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isProper
  have := hP (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
  have := hP' (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
  have := hP (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
  have := hP' (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
  exact C.squareCompatible_lowerShriekRefinementIso_trans_symm
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some

end Independence

section BaseChange

variable {Y X' Y' : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The compact-support base change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` of the chosen
compactifications is compatible with the coefficient comparisons. -/
lemma squareCompatible_lowerShriekBaseChange (hP : P.IsIsoRefinementPushforward)
    (hP' : P'.IsIsoRefinementPushforward) (sq : IsPullback g' f' f g) :
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (C.shriekOfCompactification (compactificationOverField f))
        (pull g))
      (Functor.pasteSquareIso (pull g')
        (C.shriekOfCompactification (compactificationOverField f')))
      (BoundedConstructiblePushforwardData.lowerShriekBaseChange hP sq)
      (BoundedConstructiblePushforwardData.lowerShriekBaseChange hP' sq) :=
  (C.squareCompatible_lowerShriekOfCompactificationBaseChangePasting _ sq).comp
    (NatTrans.SquareCompatible.whiskerLeft (pull g')
      (C.squareCompatible_lowerShriekOfCompactificationIso hP hP' _ _))

end BaseChange

end BoundedConstructibleCoefficientChange

end AlgebraicGeometry.ProEtale.CondensedRing
