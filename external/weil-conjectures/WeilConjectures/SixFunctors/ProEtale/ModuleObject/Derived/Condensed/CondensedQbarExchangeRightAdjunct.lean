/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

open scoped CategoryTheory.TwoSquare

section MateIdentity

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {T : A ⥤ B} {S : B ⥤ A} {T' : A' ⥤ B'} {S' : B' ⥤ A'}
  {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}

private theorem push_eq_mate_pull_inv (a : T ⊣ S) (b : T' ⊣ S')
    (c : l ⊣ r) (d : l' ⊣ r') (e : r' ⋙ S' ≅ S ⋙ r) :
    Adjunction.pushHomOfComapIso a b e =
      (mateEquiv c d (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a b c d e).inv)) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm c d b a
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (mateEquiv c d).symm.injective
  change (mateEquiv c d).symm ((mateEquiv a b).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv c d).symm
      (mateEquiv c d (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a b c d e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

end MateIdentity

private theorem restrict_counit_hom {C D : Type*} [Category C] [Category D]
     (P : ObjectProperty C) (Q : ObjectProperty D)
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (hL : ∀ K : P.FullSubcategory, Q (L.obj K.obj))
    (hR : ∀ K : Q.FullSubcategory, P (R.obj K.obj))
    (K : Q.FullSubcategory) :
    ((a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι P)
      (ObjectProperty.fullyFaithfulι Q) (Q.liftCompιIso (P.ι ⋙ L) hL).symm
      (P.liftCompιIso (Q.ι ⋙ R) hR).symm).counit.app K).hom = a.counit.app K.obj := by
  have hc := a.map_restrictFullyFaithful_counit_app
    (ObjectProperty.fullyFaithfulι P) (ObjectProperty.fullyFaithfulι Q)
    (Q.liftCompιIso (P.ι ⋙ L) hL).symm (P.liftCompιIso (Q.ι ⋙ R) hR).symm K
  simpa [ObjectProperty.liftCompιIso] using hc

section
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (PC : ObjectProperty C) (PD : ObjectProperty D)
    (PE : ObjectProperty E) (PF : ObjectProperty F)
    {l : C ⥤ D} {tD : D ⥤ F} {tC : C ⥤ E} {l' : E ⥤ F}
    (hl : ∀ K : PC.FullSubcategory, PD (l.obj K.obj))
    (htD : ∀ K : PD.FullSubcategory, PF (tD.obj K.obj))
    (htC : ∀ K : PC.FullSubcategory, PE (tC.obj K.obj))
    (hl' : ∀ K : PE.FullSubcategory, PF (l'.obj K.obj))

private theorem lifted_inv_naturality (α : l ⋙ tD ≅ tC ⋙ l')
    {K M : PC.FullSubcategory} (v : K ⟶ M) :
    (PF.lift (PE.ι ⋙ l') hl').map ((PE.lift (PC.ι ⋙ tC) htC).map v) ≫
        (PF.isoMk (α.app M.obj)).inv =
      (PF.isoMk (α.app K.obj)).inv ≫
        (PF.lift (PD.ι ⋙ tD) htD).map ((PD.lift (PC.ι ⋙ l) hl).map v) := by
  exact ObjectProperty.hom_ext _ (α.inv.naturality v.hom)

/-- The mate counit identity after restriction to four full subcategories.
Source: Mathlib/CategoryTheory/Adjunction/Mates.lean, mateEquiv_counit and
iterated_mateEquiv_conjugateEquiv_symm; Adjunction.restrictFullyFaithful
(blueprint: lem-weil-pbc-qbar-condensed-push-counit).

Proof in words. Iterated mate cancellation identifies the coefficient push map with
the mate of the inverse coefficient pull isomorphism. The mate counit equation gives
the ambient equality. The fully faithful restriction counit formula identifies both
restricted counits with their ambient counterparts. Faithfulness of the inclusion
then proves the stated equality. All four subcategories are arbitrary, so this
calculation also supplies the finite-to-Qbar constructible specialization. -/
theorem lifted_push_counit
    {r : D ⥤ C} {r' : F ⥤ E} (a : l ⊣ r) (b : l' ⊣ r')
    (hr : ∀ K : PD.FullSubcategory, PC (r.obj K.obj))
    (hr' : ∀ K : PF.FullSubcategory, PE (r'.obj K.obj))
    {sD : F ⥤ D} {sC : E ⥤ C} (aExt : tD ⊣ sD) (bExt : tC ⊣ sC)
    (e : r' ⋙ sC ≅ sD ⋙ r) (K : PD.FullSubcategory) :
    let α := Adjunction.pullIsoOfComapIso aExt bExt a b e
    let δ := Adjunction.pushHomOfComapIso aExt bExt e
    let L := PD.lift (PC.ι ⋙ l) hl
    let R := PC.lift (PD.ι ⋙ r) hr
    let L' := PF.lift (PE.ι ⋙ l') hl'
    let TD := PF.lift (PD.ι ⋙ tD) htD
    let TC := PE.lift (PC.ι ⋙ tC) htC
    let i : TD.obj (L.obj (R.obj K)) ≅ L'.obj (TC.obj (R.obj K)) :=
      PF.isoMk (α.app (r.obj K.obj))
    L'.map (ObjectProperty.homMk (δ.app K.obj)) ≫
        (b.restrictFullyFaithful (ObjectProperty.fullyFaithfulι PE)
          (ObjectProperty.fullyFaithfulι PF) (PF.liftCompιIso _ hl').symm
          (PE.liftCompιIso _ hr').symm).counit.app (TD.obj K) =
      i.inv ≫ TD.map
        ((a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι PC)
          (ObjectProperty.fullyFaithfulι PD) (PD.liftCompιIso _ hl).symm
          (PC.liftCompιIso _ hr).symm).counit.app K) := by
  apply ObjectProperty.hom_ext PF
  change l'.map ((Adjunction.pushHomOfComapIso aExt bExt e).app K.obj) ≫ _ =
    (Adjunction.pullIsoOfComapIso aExt bExt a b e).inv.app (r.obj K.obj) ≫ tD.map _
  simp only [ObjectProperty.ι_map]
  rw [restrict_counit_hom, restrict_counit_hom,
    push_eq_mate_pull_inv aExt bExt a b e]
  exact mateEquiv_counit a b
    (TwoSquare.mk _ _ _ _ (Adjunction.pullIsoOfComapIso aExt bExt a b e).inv) K.obj

end

section RightNormalization
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {l : A ⥤ B} {r : B ⥤ A} {l' : C ⥤ D} {r' : D ⥤ C}
  {tA : A ⥤ C} {tB : B ⥤ D}
private theorem right_normalization (ε : r ⋙ l ⟶ 𝟭 B) (ε' : r' ⋙ l' ⟶ 𝟭 D)
    (q : ∀ U, l'.obj (tA.obj U) ⟶ tB.obj (l.obj U))
    (hn : ∀ {U V : A} (v : U ⟶ V), l'.map (tA.map v) ≫ q V =
      q U ≫ tB.map (l.map v))
    {U : A} {W : B} {V : D} (β : U ⟶ r.obj W) (δ : tA.obj (r.obj W) ⟶ r'.obj (tB.obj W))
    (α : tB.obj W ⟶ V)
    (hδ : l'.map δ ≫ ε'.app (tB.obj W) = q (r.obj W) ≫ tB.map (ε.app W)) :
    l'.map (tA.map β ≫ (δ ≫ r'.map α)) ≫ ε'.app V =
      q U ≫ tB.map (l.map β ≫ ε.app W) ≫ α := by
  have he := ε'.naturality α
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at he
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [he]
  slice_lhs 2 3 => rw [hδ]
  slice_lhs 1 2 => rw [hn β]
  simp only [Category.assoc]
end RightNormalization

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

private theorem pull_inv_naturality {K M : PadicSubfieldConstructible U ℓ E}
    (v : K ⟶ M) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).map
        ((constructibleToPadicAlgCl U ℓ E).map v) ≫
      (constructibleToQbarPullIso ℓ k E h M).inv =
    (constructibleToQbarPullIso ℓ k E h K).inv ≫
      (constructibleToPadicAlgCl T ℓ E).map
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k)))).map v) := by
  exact lifted_inv_naturality _ _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj U ℓ E K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h) v

-- Matching the goal against `lifted_push_counit` must compare these terms by their arguments;
-- unfolding them reaches compositions in the derived categories (about 30 s of unification).
attribute [local irreducible] derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction derivedComapLowerStarIso
  Adjunction.pushHomOfComapIso Adjunction.pullIsoOfComapIso Adjunction.restrictFullyFaithful in
/-- Scalar extension's push comparison satisfies the mate counit identity.
Source: ChangeOfCoefficients.lean, derivedPullIso and derivedPushHom;
Mathlib/CategoryTheory/Adjunction/Mates.lean, iterated_mateEquiv_conjugateEquiv_symm
and mateEquiv_counit (blueprint: lem-weil-pbc-qbar-condensed-push-counit).

Proof in words. The two coefficient extension/restriction adjunctions and the two
geometric pullback/pushforward adjunctions form a square. Iterated mate cancellation
identifies pushHomOfComapIso with the mate of inverse pullIsoOfComapIso. Apply the
mate counit equation at the underlying object K. Fully faithful restriction to
bounded constructible objects preserves counits, and its inclusion is faithful,
so the ambient equation gives exactly the displayed restricted equation. -/
theorem constructibleToQbar_push_counit (K : PadicSubfieldConstructible T ℓ E) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj.{u} ℓ) ℓ
        (h.asOver (Spec (.of k)))).map
        (constructibleToQbarPushHom ℓ k E h K) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (h.asOver (Spec (.of k)))).counit.app
            ((constructibleToPadicAlgCl T ℓ E).obj K) =
      (constructibleToQbarPullIso ℓ k E h
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
            (h.asOver (Spec (.of k)))).obj K)).inv ≫
        (constructibleToPadicAlgCl T ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
              (h.asOver (Spec (.of k)))).counit.app K) := by
  exact lifted_push_counit _ _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj U ℓ E K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    _ _
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E
      (h.asOver (Spec (.of k))) K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ (h.asOver (Spec (.of k))) K)
    _ _ _ K

end Edge
variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

-- The normalization uses only the functor laws and the already proved comparison laws.
-- Keep the concrete derived constructions folded while specializing those laws.
attribute [local irreducible] constructibleToQbarPullIso constructibleToQbarPushHom
  boundedConstructibleUpperStar boundedConstructibleLowerStar
  ContinuousMapRingObj.boundedConstructibleLowerStar constructibleToPadicAlgCl
  boundedConstructibleUpperStarLowerStarAdjunction
  ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction in
set_option backward.isDefEq.respectTransparency true in
/-- Normalization of the right side of coefficient exchange under the pullback adjunction.
Source: ModuleObject/Colimit/TwoColimit.lean, final transport paragraph;
ChangeOfCoefficients.lean, derivedPullIso and derivedPushHom;
Mathlib/CategoryTheory/Adjunction/Mates.lean
(blueprint: lem-weil-pbc-qbar-condensed-exchange-right-adjunct).

Proof in words. Expand the target comparison and functoriality of pullback. Naturality of the
Omega pullback/pushforward counit moves alpha_g' to the right of that counit. The adjunct
of the push comparison for f' is inverse alpha_f' at its E pushforward followed by scalar
extension of the E counit. Indeed pushHomOfComapIso is the mate of inverse
pullIsoOfComapIso, by iterated mate/conjugation cancellation. Restriction along the fully
faithful constructible inclusions preserves this counit identity. Naturality of inverse
alpha_f' at the E base-change morphism moves that morphism across inverse alpha_f'.
Finally scalar-extension functoriality combines its pullback and the E counit. This is the
displayed middle expression. This step uses no coefficient square coherence, and applies
to any morphism with the type of the E base-change component. Thus it is independent of the
left-side normalization. Identity and zero morphisms satisfy the same naturality laws. -/
theorem constructibleToQbar_exchange_right_adjunct
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).map
      ((constructibleToPadicAlgCl Y' ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
              (sq.asOver (Spec (.of k)))).app K) ≫
        constructibleToQbarTargetHom ℓ k E f' g' K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f'.asOver (Spec (.of k)))).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              (g'.asOver (Spec (.of k)))).obj
            ((constructibleToPadicAlgCl X ℓ E).obj K)) =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g.asOver (Spec (.of k)))).obj
          ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
              (f.asOver (Spec (.of k)))).obj K))).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (f'.asOver (Spec (.of k)))).map
            ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
                (sq.asOver (Spec (.of k)))).app K) ≫
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
              (f'.asOver (Spec (.of k)))).counit.app
              ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
                  (g'.asOver (Spec (.of k)))).obj K)) ≫
      (constructibleToQbarPullIso ℓ k E g' K).hom := by
  dsimp only [constructibleToQbarTargetHom]
  exact right_normalization
    (l := boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (f'.asOver (Spec (.of k))))
    (r := ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E (f'.asOver (Spec (.of k))))
    (l' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k))))
    (r' := boundedConstructibleLowerStar ℓ (f'.asOver (Spec (.of k))))
    (tA := constructibleToPadicAlgCl Y' ℓ E)
    (tB := constructibleToPadicAlgCl X' ℓ E)
    (U := (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (g.asOver (Spec (.of k)))).obj
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E (f.asOver (Spec (.of k)))).obj K))
    (W := (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (g'.asOver (Spec (.of k)))).obj K)
    (V := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (g'.asOver (Spec (.of k)))).obj ((constructibleToPadicAlgCl X ℓ E).obj K))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
        (f'.asOver (Spec (.of k)))).counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f'.asOver (Spec (.of k)))).counit
    (fun U ↦ (constructibleToQbarPullIso ℓ k E f' U).inv)
    (fun v ↦ pull_inv_naturality ℓ k E f' v)
    ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E (sq.asOver (Spec (.of k)))).app K)
    (constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k)))).obj K))
    (constructibleToQbarPullIso ℓ k E g' K).hom
    (constructibleToQbar_push_counit ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k)))).obj K))

end AlgebraicGeometry.ProEtale.CondensedRing

-- The concrete identities' inferred derived-category instances make Lean's two
-- premise-index export passes expensive. Their names are used explicitly by the equality
-- proofs; exclude just these identities from suggestions using Lean's documented API.
-- This changes neither their signatures, proofs, visibility nor kernel checking.
run_cmd do
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "constructibleToQbar_exchange_right_adjunct"
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "constructibleToQbar_push_counit"
