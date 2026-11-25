/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.WeilTrace

/-!
# Weil objects for the identity with the identity structure

Let `X` be a separated scheme of finite type over a finite field `k`. Every bounded constructible
complex `K` on `X` is a Weil object for the identity of `X`, with the structure isomorphism
`L(𝟙)^* K ≅ K` (`ProEtale.CondensedRing.boundedConstructibleUpperStarId`); likewise every module
object `M` on `X` is a Weil sheaf for the identity, with the structure isomorphism
`(𝟙)^* M ≅ M` (`ProEtale.CondensedRing.upperStarId`). This file shows that these identity
structures are preserved by the compactly supported cohomology and by the homology sheaves.

## Main results

- `boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_horizontal_id`: the
  compact-support base change of the square `𝟙 ≫ f = f ≫ 𝟙` is
  `L(𝟙)^* Rf_! K ≅ Rf_! K ≅ Rf_! L(𝟙)^* K`. It follows from the idempotence of the square under
  horizontal pasting (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`).
- `ProEtale.CondensedRing.weilCompactSupportCohomology_obj_str_hom_of_id`: the compactly
  supported cohomology `RΓ_c(X, K)` of a Weil object with the identity structure has the identity
  structure.
- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id`: the
  homology sheaves of a Weil object with the identity structure have the identity structure.
- `ProEtale.CondensedRing.WeilSheaf.isoOfId`: Weil sheaves with the identity structure are
  isomorphic as soon as their underlying module objects are.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChange

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Compact-support base change of the identity square**: for the cartesian square
`𝟙 ≫ f = f ≫ 𝟙`, the base change `L(𝟙)^* Rf_! K ⟶ Rf_! L(𝟙)^* K` is
`L(𝟙)^* Rf_! K ≅ Rf_! K ≅ Rf_! L(𝟙)^* K`. Pasting the square with itself gives the square
back, so that, after the identification `L(𝟙)^* ≅ 𝟭`, the base change is an idempotent
isomorphism (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`), hence the
identity. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_horizontal_id
    {f : X ⟶ Y}
    (sq : IsPullback (𝟙 X) f f (𝟙 Y)) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.app K) := by
  have hp : (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 Y) (𝟙 Y)).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 Y)).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj K) ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) (𝟙 X)).inv.app
            K) :=
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ sq sq K
  have hY :
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 Y) (𝟙 Y)).hom.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 Y)).obj
          ((boundedConstructibleLowerShriek ℓ f).obj K)) = 𝟙 _ :=
    boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ
      (𝟙 Y) ((boundedConstructibleLowerShriek ℓ f).obj K)
  have hX :
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) (𝟙 X)).hom.app K ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj K) = 𝟙 _ :=
    boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) K
  have hYc := (Iso.comp_hom_eq_id
    ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 Y)).obj
        ((boundedConstructibleLowerShriek ℓ f).obj K)))).1 hY
  have hXc :
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) (𝟙 X)).inv.app K =
        (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app _ :=
    ((Iso.hom_comp_eq_id
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X) (𝟙 X)).app
        K)).1 hX).symm
  rw [hYc, hXc, Iso.app_inv] at hp
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have hn := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).inv.naturality
    ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K)
  rw [Functor.id_map] at hn
  rw [← reassoc_of% hn] at hp
  have key := (cancel_epi ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K)).1
    (hp.symm.trans (Category.comp_id _).symm)
  have hβ : (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).inv.app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K) =
      𝟙 _ := by
    rw [← ((boundedConstructibleLowerShriek ℓ f).mapIso
      ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app
        K)).cancel_iso_hom_left]
    erw [Category.comp_id]
    rw [Functor.mapIso_hom, Iso.app_hom]
    have h1 := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).inv.naturality
      ((boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K))
    have h2 := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality
      ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K)
    have h3 := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.naturality
      ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K)
    simp only [Functor.id_map, Functor.comp_map] at h1 h2 h3
    rw [reassoc_of% h1, reassoc_of% h2, ← Functor.map_comp]
    erw [h3]
    rw [Functor.map_comp, reassoc_of% key]
  have h4 := (Iso.inv_comp_eq ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ
    Y).app ((boundedConstructibleLowerShriek ℓ f).obj K))).1 hβ
  erw [Category.comp_id] at h4
  rw [Iso.app_hom] at h4
  exact (Iso.eq_comp_inv ((boundedConstructibleLowerShriek ℓ f).mapIso
    ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app K))).2 h4

end BaseChange

section CompactSupport

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **Compactly supported cohomology of a Weil object with the identity structure**: if the
structure isomorphism of a Weil object `K` for the identity of `X` is the identity isomorphism
`L(𝟙)^* K ≅ K`, then so is the structure isomorphism of `RΓ_c(X, K)`
(`weilCompactSupportCohomology`), by
`boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_horizontal_id`. -/
theorem weilCompactSupportCohomology_obj_str_hom_of_id
    (K : WeilBoundedConstructible ℓ (Iso.refl X).hom)
    (hK : K.str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K.carrier) :
    ((weilCompactSupportCohomology ℓ (Iso.refl X)).obj K).str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app
        ((weilCompactSupportCohomology ℓ (Iso.refl X)).obj K).carrier := by
  rw [weilCompactSupportCohomology, weilLowerShriek_obj_str, Iso.trans_hom, Iso.app_hom,
    weilLowerShriekComparison_hom,
    boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_of_horizontal_id,
    Functor.mapIso_hom, hK, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    ]
  exact (congrArg _ ((boundedConstructibleLowerShriek ℓ (toPoint X)).map_id _)).trans
    (Category.comp_id _)

end CompactSupport

section Homology

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **Homology sheaves of a Weil object with the identity structure**: if the structure
isomorphism of a Weil object `K` for the identity of `X` is the identity isomorphism
`L(𝟙)^* K ≅ K`, then the structure isomorphism of each homology sheaf `Hⁿ(K)` is the identity
isomorphism `(𝟙)^* Hⁿ(K) ≅ Hⁿ(K)` (`leftDerivedUpperStarHomologyIso_hom_app_id`). -/
theorem WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id
    (K : WeilBoundedConstructible ℓ (Iso.refl X).hom)
    (hK : K.str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K.carrier)
    (n : ℤ) :
    ((WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj K).str.hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app
        ((WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj K).carrier := by
  rw [WeilBoundedConstructible.homologyFunctor_obj_str, Iso.trans_hom, Iso.app_hom,
    weilHomologyComparison_hom_app, Functor.mapIso_hom, hK, Functor.comp_map, ObjectProperty.ι_map,
    boundedConstructibleUpperStarId_hom_app_hom, Category.assoc, ← Functor.map_comp]
  have h := leftDerivedUpperStarHomologyIso_hom_app_id _ X.left n K.carrier.obj
  simp only [leftDerivedUpperStarHomologyIso, Functor.leftDerivedFunctorHomologyFunctorIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc] at h
  rw [Functor.map_comp]
  exact h

/-- Two Weil sheaves for the identity of `X` whose structure isomorphisms are the identity
isomorphism `(𝟙)^* M ≅ M` are isomorphic as soon as their underlying module objects are: every
morphism commutes with the identity isomorphisms. -/
noncomputable def WeilSheaf.isoOfId {F G : WeilSheaf ℓ (Iso.refl X)}
    (hF : F.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app F.carrier)
    (hG : G.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app G.carrier)
    (e : F.carrier ≅ G.carrier) : F ≅ G :=
  IsoAlgebra.isoMk e (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, hF, hG]
    exact (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.naturality e.hom)

end Homology

end AlgebraicGeometry.ProEtale.CondensedRing
