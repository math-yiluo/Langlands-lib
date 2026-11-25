/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisons
public import WeilConjectures.CategoryTheory.ProperBaseChange.TransportedCompositeIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ResidueExchangeAmbient

/-! # The specified bounded exchange viewed in the ambient category

Source: the defining unit-square-counit formula for boundedConstructibleBaseChange.
Stated for each coefficient ring with bounded constructible pushforwards: `ℚ̄_ℓ`, a finite
discrete ring `T` (`FiniteDiscreteRingObj`) and a unit ball `O` (`UnitBallRingObj`).
(blueprint: lem-weil-pbc-bounded-exchange-ambient)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_boundedExchangeAmbient
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeAdjunction residueExchangeUpperStarComp

private theorem bounded_comp_hom {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] (h : Y ⟶ Z) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Z)) :
    ((boundedConstructibleUpperStarComp Λ ℓ (f.asOver (Spec (.of k)))
      (h.asOver (Spec (.of k)))).hom.app K).hom =
      (residueExchangeUpperStarComp Λ f h).hom.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleUpperStarComp,
    CategoryTheory.Functor.FullyFaithful.preimageIso,
    CategoryTheory.Functor.FullyFaithful.whiskeringRight, Functor.whiskeringRight_obj_obj,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.trans_hom,
    Iso.refl_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_inv, CategoryTheory.Functor.FullyFaithful.preimage_comp, NatTrans.id_app,
    ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Functor.associator_hom_app, Category.comp_id,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, residueExchangeUpperStarComp, id_eq]
  exact Category.id_comp _

private theorem subcat_iso_inv {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (e : A ≅ B) (d : A.obj ≅ B.obj)
    (h : e.hom.hom = d.hom) : e.inv.hom = d.inv := by
  apply Iso.inv_ext'
  rw [← h]
  exact ObjectProperty.isoHom_inv_id_hom e

private theorem bounded_comp_inv_hom {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] (h : Y ⟶ Z) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Z)) :
    ((boundedConstructibleUpperStarComp Λ ℓ (f.asOver (Spec (.of k)))
      (h.asOver (Spec (.of k)))).inv.app K).hom =
      (residueExchangeUpperStarComp Λ f h).inv.app K.obj := by
  exact subcat_iso_inv ((boundedConstructibleUpperStarComp Λ ℓ
    (f.asOver (Spec (.of k))) (h.asOver (Spec (.of k)))).app K)
    ((residueExchangeUpperStarComp Λ f h).app K.obj) (bounded_comp_hom Λ ℓ k h K)

private theorem bounded_transport_obj_hom
    (h i : X' ⟶ Y) [h.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    (w : h = i)
    (hf : boundedConstructibleUpperStar Λ ℓ (h.asOver (Spec (.of k))) =
      boundedConstructibleUpperStar Λ ℓ (i.asOver (Spec (.of k))))
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    (eqToHom (congrArg (fun F : ProEtale.BoundedConstructible (condensedRingObj Λ Y) ⥤
        ProEtale.BoundedConstructible (condensedRingObj Λ X') ↦ F.obj K) hf)).hom =
      eqToHom (congrArg
        (fun t : X' ⟶ Y ↦ (residueExchangeUpperStar Λ t).obj K.obj) w) := by
  cases w
  rfl

private theorem bounded_square_hom (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app K).hom =
      (residueExchangeSquare Λ sq).hom.app K.obj := by
  let hB : boundedConstructibleUpperStar Λ ℓ ((f' ≫ g).asOver (Spec (.of k))) =
      boundedConstructibleUpperStar Λ ℓ ((g' ≫ f).asOver (Spec (.of k))) := by simp only [sq.w]
  have hs : boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k))) =
      transportedCompositeIso (boundedConstructibleUpperStarComp Λ ℓ
        (f'.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))).symm
        (boundedConstructibleUpperStarComp Λ ℓ (g'.asOver (Spec (.of k)))
          (f.asOver (Spec (.of k)))) hB :=
    (transportedCompositeIso_eq (boundedConstructibleUpperStarComp Λ ℓ
      (f'.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))).symm
      (boundedConstructibleUpperStarComp Λ ℓ (g'.asOver (Spec (.of k)))
        (f.asOver (Spec (.of k)))) hB).symm
  rw [hs]
  dsimp only [transportedCompositeIso, residueExchangeSquare,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    ObjectProperty.FullSubcategory.comp_hom, eqToIso.hom]
  rw [bounded_comp_inv_hom Λ ℓ k (f := f') g K,
    bounded_comp_hom Λ ℓ k (f := g') f K,
    bounded_transport_obj_hom Λ ℓ k _ _ sq.w.symm hB K]

section General

/-- The restricted pushforward through a given finiteness proof `hP`: the shape of every
per-ring `boundedConstructibleLowerStar`. -/
private noncomputable def gLowerStar {Xo Yo : Over (Spec (.of k))} (φ : Xo ⟶ Yo)
    (hP : ∀ K : ProEtale.BoundedConstructible (condensedRingObj Λ Xo.left),
      boundedConstructible (condensedRingObj Λ Yo.left) ((R((φ.left)_*⟦Λ⟧)).obj K.obj)) :
    ProEtale.BoundedConstructible (condensedRingObj Λ Xo.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Yo.left) :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((φ.left)_*⟦Λ⟧)) hP

private noncomputable def gLowerStarCompatibility {Xo Yo : Over (Spec (.of k))} (φ : Xo ⟶ Yo)
    (hP : ∀ K : ProEtale.BoundedConstructible (condensedRingObj Λ Xo.left),
      boundedConstructible (condensedRingObj Λ Yo.left) ((R((φ.left)_*⟦Λ⟧)).obj K.obj)) :
    gLowerStar Λ k φ hP ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((φ.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restricted adjunction through a given finiteness proof `hP`: the shape of every
per-ring `boundedConstructibleUpperStarLowerStarAdjunction`. -/
private noncomputable def gAdj {Xo Yo : Over (Spec (.of k))}
    [LocallyOfFiniteType Xo.hom] [QuasiCompact Xo.hom] [IsSeparated Xo.hom]
    [LocallyOfFiniteType Yo.hom] [QuasiCompact Yo.hom] [IsSeparated Yo.hom] (φ : Xo ⟶ Yo)
    (hP : ∀ K : ProEtale.BoundedConstructible (condensedRingObj Λ Xo.left),
      boundedConstructible (condensedRingObj Λ Yo.left) ((R((φ.left)_*⟦Λ⟧)).obj K.obj)) :
    boundedConstructibleUpperStar Λ ℓ φ ⊣ gLowerStar Λ k φ hP :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ φ.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ φ).symm
    (gLowerStarCompatibility Λ k φ hP).symm

private theorem bounded_counit_hom
    (hP : ∀ K : ProEtale.BoundedConstructible
        (condensedRingObj Λ (OverClass.asOver X (Spec (.of k))).left),
      boundedConstructible (condensedRingObj Λ (OverClass.asOver Y (Spec (.of k))).left)
        ((R(((f.asOver (Spec (.of k))).left)_*⟦Λ⟧)).obj K.obj))
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((gAdj Λ ℓ k (f.asOver (Spec (.of k))) hP).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f).counit.app K.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f.asOver (Spec (.of k)))).symm
    (gLowerStarCompatibility Λ k (f.asOver (Spec (.of k))) hP).symm K
  change ((gAdj Λ ℓ k (f.asOver (Spec (.of k))) hP).counit.app K).hom =
    𝟙 _ ≫ (L((f)^*⟦Λ⟧)).map (𝟙 _) ≫
      (derivedUpperStarLowerStarAdjunction Λ f).counit.app K.obj at h
  rw [(L((f)^*⟦Λ⟧)).map_id] at h
  simpa only [Category.id_comp] using h

private lemma squareExchange_map_counit_of_eq {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D') (θ : G ⋙ L' ≅ L ⋙ H)
    {β : R ⋙ G ⟶ H ⋙ R'} (h : β = Adjunction.squareExchange a b G H θ) (N : D) :
    L'.map (β.app N) ≫ b.counit.app (H.obj N) = θ.hom.app (R.obj N) ≫ H.map (a.counit.app N) := by
  subst h
  exact Adjunction.squareExchange_map_counit a b G H θ N

/-- The snapshot proof, for a general `Λ` and any exchange `bc` satisfying the adjunct equation
of the restricted adjunctions. -/
private theorem baseChange_hom_eq_ambient_general (sq : CommSq g' f' f g)
    (hf : ∀ K : ProEtale.BoundedConstructible
        (condensedRingObj Λ (OverClass.asOver X (Spec (.of k))).left),
      boundedConstructible (condensedRingObj Λ (OverClass.asOver Y (Spec (.of k))).left)
        ((R(((f.asOver (Spec (.of k))).left)_*⟦Λ⟧)).obj K.obj))
    (hf' : ∀ K : ProEtale.BoundedConstructible
        (condensedRingObj Λ (OverClass.asOver X' (Spec (.of k))).left),
      boundedConstructible (condensedRingObj Λ (OverClass.asOver Y' (Spec (.of k))).left)
        ((R(((f'.asOver (Spec (.of k))).left)_*⟦Λ⟧)).obj K.obj))
    (bc : gLowerStar Λ k (f.asOver (Spec (.of k))) hf ⋙
        boundedConstructibleUpperStar Λ ℓ (g.asOver (Spec (.of k))) ⟶
      boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k))) ⋙
        gLowerStar Λ k (f'.asOver (Spec (.of k))) hf')
    (hbc : bc = Adjunction.squareExchange (gAdj Λ ℓ k (f.asOver (Spec (.of k))) hf)
      (gAdj Λ ℓ k (f'.asOver (Spec (.of k))) hf')
      (boundedConstructibleUpperStar Λ ℓ (g.asOver (Spec (.of k))))
      (boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k))))
      (boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))))
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    (bc.app K).hom = (residueExchangeBaseChange Λ sq).app K.obj := by
  apply ((residueExchangeAdjunction Λ f').homEquiv _ _).symm.injective
  change (residueExchangeUpperStar Λ f').map (bc.app K).hom ≫
      (residueExchangeAdjunction Λ f').counit.app
        ((residueExchangeUpperStar Λ g').obj K.obj) =
    (residueExchangeUpperStar Λ f').map ((residueExchangeBaseChange Λ sq).app K.obj) ≫
      (residueExchangeAdjunction Λ f').counit.app
        ((residueExchangeUpperStar Λ g').obj K.obj)
  have h0 : ∀ N : ProEtale.BoundedConstructible
      (condensedRingObj Λ (OverClass.asOver X (Spec (.of k))).left),
      (boundedConstructibleUpperStar Λ ℓ (f'.asOver (Spec (.of k)))).map (bc.app N) ≫
        (gAdj Λ ℓ k (f'.asOver (Spec (.of k))) hf').counit.app
          ((boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k)))).obj N) =
      (boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app
          ((gLowerStar Λ k (f.asOver (Spec (.of k))) hf).obj N) ≫
        (boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k)))).map
          ((gAdj Λ ℓ k (f.asOver (Spec (.of k))) hf).counit.app N) := by
    exact squareExchange_map_counit_of_eq _ _ _ _ _ hbc
  have h := congrArg (fun z ↦ z.hom) (h0 K)
  change (residueExchangeUpperStar Λ f').map (bc.app K).hom ≫
      ((gAdj Λ ℓ k (f'.asOver (Spec (.of k))) hf').counit.app
        ((boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k)))).obj K)).hom =
    ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app
      ((gLowerStar Λ k (f.asOver (Spec (.of k))) hf).obj K)).hom ≫
      (residueExchangeUpperStar Λ g').map
        (((gAdj Λ ℓ k (f.asOver (Spec (.of k))) hf).counit.app K).hom) at h
  simp only [bounded_counit_hom Λ ℓ k, bounded_square_hom Λ ℓ k sq] at h
  exact h.trans (residueExchangeBaseChange_counit Λ sq K.obj).symm

end General

section PadicAlgCl

-- Keep the concrete coefficient ring opaque, as the generic `Λ` was before the restatement.
attribute [local irreducible] Profinite.padicAlgClCondensedRing

/-- Inclusion identifies the specified bounded exchange with the ambient adjunction mate
(ℚ̄_ℓ-coefficient).

Source: the defining three-step formula in MorphismDefs and Mathlib adjunction restriction.
(blueprint: lem-weil-pbc-bounded-exchange-ambient)

Proof. Apply injectivity of the ambient f-prime inverse hom equivalence. The existing
bounded exchange adjunct equation gives the restricted square followed by the pulled
counit. Fully faithful restriction has the same underlying counit because its
compatibility isomorphisms are identities. The restricted pull-composition constraints
likewise have the original underlying components. Equality transport commutes with
inclusion, so the square comparison has the ambient component. Substituting these
component identities gives the ambient mate counit equation, hence the desired equality.
This identification requires no properness and does not assert invertibility. -/
theorem boundedConstructibleBaseChange_hom_eq_ambient (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) :
    ((boundedConstructibleBaseChange ℓ (sq.asOver (Spec (.of k)))).app K).hom =
      (residueExchangeBaseChange (Profinite.padicAlgClRingObj.{u} ℓ) sq).app K.obj := by
  exact baseChange_hom_eq_ambient_general (Profinite.padicAlgClRingObj.{u} ℓ) ℓ k sq
    (boundedConstructible_rightDerivedLowerStar_obj ℓ (f.asOver (Spec (.of k))))
    (boundedConstructible_rightDerivedLowerStar_obj ℓ (f'.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange ℓ (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange_eq_squareExchange ℓ (sq.asOver (Spec (.of k)))) K

end PadicAlgCl

namespace FiniteDiscreteRingObj

-- Keep the concrete coefficient ring opaque, as the generic `Λ` was before the restatement.
attribute [local irreducible] Profinite.continuousMapRingSheaf

variable (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] [Fact (IsNilpotent (ℓ : T))]

/-- Inclusion identifies the specified bounded exchange with the ambient adjunction mate
(`T`-coefficient).

Source: the defining three-step formula in MorphismDefs and Mathlib adjunction restriction.
(blueprint: lem-weil-pbc-bounded-exchange-ambient)

Proof. Apply injectivity of the ambient f-prime inverse hom equivalence. The existing
bounded exchange adjunct equation gives the restricted square followed by the pulled
counit. Fully faithful restriction has the same underlying counit because its
compatibility isomorphisms are identities. The restricted pull-composition constraints
likewise have the original underlying components. Equality transport commutes with
inclusion, so the square comparison has the ambient component. Substituting these
component identities gives the ambient mate counit equation, hence the desired equality.
This identification requires no properness and does not assert invertibility. -/
theorem boundedConstructibleBaseChange_hom_eq_ambient (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X)) :
    ((boundedConstructibleBaseChange ℓ T (sq.asOver (Spec (.of k)))).app K).hom =
      (residueExchangeBaseChange (Profinite.continuousMapRingObj.{u} T) sq).app K.obj := by
  exact baseChange_hom_eq_ambient_general (Profinite.continuousMapRingObj.{u} T) ℓ k sq
    (boundedConstructible_rightDerivedLowerStar_obj ℓ T (f.asOver (Spec (.of k))))
    (boundedConstructible_rightDerivedLowerStar_obj ℓ T (f'.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange ℓ T (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange_eq_squareExchange ℓ T (sq.asOver (Spec (.of k)))) K

end FiniteDiscreteRingObj

namespace UnitBallRingObj

-- Keep the concrete coefficient ring opaque, as the generic `Λ` was before the restatement.
attribute [local irreducible] Profinite.continuousMapRingSheaf

variable {E : Type} [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  (O : Subring E) [Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)]

/-- Inclusion identifies the specified bounded exchange with the ambient adjunction mate
(`O`-coefficient).

Source: the defining three-step formula in MorphismDefs and Mathlib adjunction restriction.
(blueprint: lem-weil-pbc-bounded-exchange-ambient)

Proof. Apply injectivity of the ambient f-prime inverse hom equivalence. The existing
bounded exchange adjunct equation gives the restricted square followed by the pulled
counit. Fully faithful restriction has the same underlying counit because its
compatibility isomorphisms are identities. The restricted pull-composition constraints
likewise have the original underlying components. Equality transport commutes with
inclusion, so the square comparison has the ambient component. Substituting these
component identities gives the ambient mate counit equation, hence the desired equality.
This identification requires no properness and does not assert invertibility. -/
theorem boundedConstructibleBaseChange_hom_eq_ambient (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} O) X)) :
    ((boundedConstructibleBaseChange ℓ O (sq.asOver (Spec (.of k)))).app K).hom =
      (residueExchangeBaseChange (Profinite.continuousMapRingObj.{u} O) sq).app K.obj := by
  exact baseChange_hom_eq_ambient_general (Profinite.continuousMapRingObj.{u} O) ℓ k sq
    (boundedConstructible_rightDerivedLowerStar_obj ℓ O (f.asOver (Spec (.of k))))
    (boundedConstructible_rightDerivedLowerStar_obj ℓ O (f'.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange ℓ O (sq.asOver (Spec (.of k))))
    (boundedConstructibleBaseChange_eq_squareExchange ℓ O (sq.asOver (Spec (.of k)))) K

end UnitBallRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
