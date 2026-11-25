/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteCoherence

/-!

# `closedExtension` is the composite of the lower shriek identifications

For a proper `g : B ⟶ C` and an open immersion `h : C ⟶ P` with `g ≫ h` proper, the morphism
`closedExtension : h_! Rg_* ⟶ R(g ≫ h)_*` (adjoint to the inverse of the base change map
`Lh^* R(g ≫ h)_* ⟶ Rg_*`) is the composite `openProperExtension` of the identifications
`h_! ≅ Rh_!`, `Rg_* ≅ Rg_!`, `Rh_! Rg_! ≅ R(g ≫ h)_!` and `R(g ≫ h)_! ≅ R(g ≫ h)_*`
(`openProperExtension_adjunction`): its adjoint is computed through the compact-support base
change `Ex_!` of the cartesian square `(g, 𝟙, h, g ≫ h)`, which is both the mate of the
composition isomorphism (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv`) and
the extension-by-zero base change
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ


/-- The identity of an object of `Over S` is an open immersion. -/
lemma isOpenImmersion_over_id_left {S : Scheme.{u}} (X : Over S) :
    IsOpenImmersion (𝟙 X : X ⟶ X).left :=
  inferInstanceAs (IsOpenImmersion (𝟙 X.left))

/-- The identity of an object of `Over S` is proper. -/
lemma isProper_over_id_left {S : Scheme.{u}} (X : Over S) : IsProper (𝟙 X : X ⟶ X).left :=
  inferInstanceAs (IsProper (𝟙 X.left))

attribute [local instance] isOpenImmersion_over_id_left isProper_over_id_left
section Identity

variable {B C P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The pullback comparison of the square `𝟙 ≫ (g ≫ h) = g ≫ h`, followed by `L(𝟙)^* ≅ 𝟭`, is the
inverse composition isomorphism `Lg^* Lh^* ≅ L(g ≫ h)^*`. -/
lemma pullbackSquareComparison_hom_app_comp_upperStarId (g : B ⟶ C) (h : C ⟶ P)
    (sq : CommSq (𝟙 B) g (g ≫ h) h) (Z : Dᵇc(P.left)⟦Λℓ⟧) :
    (boundedConstructiblePullbackSquareComparison Λℓ ℓ sq).hom.app Z ≫
        (boundedConstructibleUpperStarId Λℓ ℓ B).hom.app
          ((boundedConstructibleUpperStar Λℓ ℓ (g ≫ h)).obj Z) =
      (boundedConstructibleUpperStarComp Λℓ ℓ g h).inv.app Z := by
  rw [boundedConstructiblePullbackSquareComparison_hom_app, Category.assoc, Category.assoc,
    boundedConstructibleUpperStarComp_id_left_app, eqToHom_trans, eqToHom_refl, Category.comp_id]

variable (B) in
/-- The adjunction `(𝟙)_! ⊣ L(𝟙)^*` is trivialized by `(𝟙)_! ≅ R(𝟙)_! ≅ 𝟭` and `L(𝟙)^* ≅ 𝟭`. -/
lemma lowerShriekId_inv_app_comp_isoOpen_hom_app_comp_counit (W : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerShriekId ℓ B).inv.app
        ((boundedConstructibleUpperStar Λℓ ℓ (𝟙 B)).obj W) ≫
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (𝟙 B)).hom.app
        ((boundedConstructibleUpperStar Λℓ ℓ (𝟙 B)).obj W) ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ (𝟙 B)).counit.app W =
    (boundedConstructibleUpperStarId Λℓ ℓ B).hom.app W := by
  exact inv_app_comp_hom_app_comp_counit_of_unit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ (𝟙 B))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 B))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (𝟙 B))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 B))
    (boundedConstructibleLowerStarId ℓ B) (boundedConstructibleUpperStarId Λℓ ℓ B)
    (boundedConstructibleLowerStarId_hom_app ℓ)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_clopen_of (𝟙 B) ℓ
      (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_counit (𝟙 B) ℓ)) W

end Identity


section Restriction

variable {B C P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The composition isomorphism of the square `g ≫ h = 𝟙 ≫ (g ≫ h)`, followed by
`R(𝟙)_! ≅ 𝟭`, is the inverse composition isomorphism of `g ≫ h`. -/
lemma lowerShriekSquareIso_hom_app_comp_map_lowerShriekId (g : B ⟶ C) (h : C ⟶ P)
    (w : g ≫ h = 𝟙 B ≫ (g ≫ h)) (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app N ≫
        (boundedConstructibleLowerShriek ℓ (g ≫ h)).map
          ((boundedConstructibleLowerShriekId ℓ B).hom.app N) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).inv.app N := by
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, boundedConstructibleLowerShriekId,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc]
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_left, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

-- instantiating the abstract lemma with the restricted functors is slow
/-- **The restriction of `Ex_!` along the open immersion `h`**: for the cartesian square
`(g, 𝟙, h, g ≫ h)`, `Lg^*(η_h) ≫ (Lg^* Lh^* ≅ L(g ≫ h)^*) ≫ L(g ≫ h)^*(Rh_! ≅ h_!)⁻¹ ≫ Ex_! ≫
(R(𝟙)_! ≅ 𝟭)` is the identity. -/
theorem map_unit_comp_upperStarComp_inv_comp_baseChange (g : B ⟶ C) (h : C ⟶ P)
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ h).left]
    (sq : IsPullback g (𝟙 B) h (g ≫ h)) (K : Dᵇc(C.left)⟦Λℓ⟧) :
    (boundedConstructibleUpperStar Λℓ ℓ g).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ h).unit.app K) ≫
      (boundedConstructibleUpperStarComp Λℓ ℓ g h).inv.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj K) ≫
      (boundedConstructibleUpperStar Λℓ ℓ (g ≫ h)).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h).inv.app K) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≫
      (boundedConstructibleLowerShriekId ℓ B).hom.app
        ((boundedConstructibleUpperStar Λℓ ℓ g).obj K) = 𝟙 _ := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have hO := boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen ℓ sq
  exact map_unit_comp_inv_comp_baseChange_eq_id
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ h)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ (𝟙 B))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (𝟙 B))
    (boundedConstructibleLowerShriekId ℓ B) (boundedConstructibleUpperStarId Λℓ ℓ B)
    (boundedConstructibleUpperStarComp Λℓ ℓ g h)
    (boundedConstructiblePullbackSquareComparison Λℓ ℓ sq.toCommSq.flip)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λℓ ℓ sq.toCommSq)
    (boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft Λℓ ℓ sq.toCommSq)
    (fun K ↦ by simpa using congr_app hO K)
    (pullbackSquareComparison_hom_app_comp_upperStarId ℓ g h sq.toCommSq.flip)
    (lowerShriekId_inv_app_comp_isoOpen_hom_app_comp_counit ℓ B) K

end Restriction

section ClosedExtension

variable {B C P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- On the ambient derived category, the unit of `h_! ⊣ Lh^*` on bounded constructible complexes
is the unit of `openImmersionAdjunction`. -/
lemma openImmersionLowerShriekUpperStarAdjunction_unit_app_hom (h : C ⟶ P)
    [IsOpenImmersion h.left] (K : Dᵇc(C.left)⟦Λℓ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ h).unit.app K).hom =
      (openImmersionAdjunction ℓ h.left).unit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app (openImmersionAdjunction ℓ h.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).symm
    (boundedConstructibleUpperStarCompatibility Λℓ ℓ h).symm K).trans ?_
  simp [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso]



/-- On the ambient derived category, the inverse composition isomorphism of the derived pullbacks
on bounded constructible complexes is that of `leftDerivedUpperStarComp`. -/
lemma upperStarComp_inv_app_hom (g : B ⟶ C) (h : C ⟶ P) (K : Dᵇc(P.left)⟦Λℓ⟧) :
    ((boundedConstructibleUpperStarComp Λℓ ℓ g h).inv.app K).hom =
      (leftDerivedUpperStarComp Λℓ g.left h.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]
-- instantiating the abstract lemmas with the restricted functors is slow
/-- **`openProperExtension` is adjoint to the inverse of the base change map**: the hypothesis of
`closedExtension_app_eq_openProperExtension`, so that `closedExtension = openProperExtension`. -/
theorem openProperExtension_unit_comp_closedBaseChange (g : B ⟶ C) (h : C ⟶ P)
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ h).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (openImmersionAdjunction ℓ h.left).unit.app (R((g.left)_*⟦Λℓ⟧).obj N.obj) ≫
        L((h.left)^*⟦Λℓ⟧).map ((openProperExtension ℓ g h).hom.app N).hom ≫
        (closedBaseChange Λℓ (rfl : g.left ≫ h.left = _)).app N.obj = 𝟙 _ := by
  have : Mono h := Over.mono_of_mono_left h
  have sq : IsPullback g (𝟙 B) h (g ≫ h) :=
    (IsPullback.of_horiz_isIso_mono (⟨by simp⟩ : CommSq (𝟙 B) g (g ≫ h) h)).flip
  have hP3 := map_openProperExtension_comp_counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (g ≫ h))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (g ≫ h))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h)
    (boundedConstructibleLowerShriekId ℓ B) (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ sq.w).hom
    (lowerShriekSquareIso_hom_app_comp_map_lowerShriekId ℓ g h sq.w)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ sq) N
  have hK := map_unit_comp_upperStarComp_inv_comp_baseChange ℓ g h sq
    ((boundedConstructibleLowerStar ℓ g).obj N)
  have hι := (boundedConstructibleLowerShriekId ℓ B).hom.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).counit.app N)
  simp only [Functor.id_map, Functor.id_obj] at hι
  rw [hι] at hP3
  refine unit_comp_map_comp_baseChange_eq_id'
    (derivedUpperStarLowerStarAdjunction Λℓ g.left)
    (derivedUpperStarLowerStarAdjunction Λℓ (g.left ≫ h.left)) (openImmersionAdjunction ℓ h.left)
    (leftDerivedUpperStarCompOfEq Λℓ rfl) (closedBaseChange Λℓ rfl) N.obj
    (map_closedBaseChange_app_comp_counit Λℓ rfl N.obj) _
    ((boundedConstructibleUpperStar Λℓ ℓ (g ≫ h)).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h).inv.app
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        ((boundedConstructibleLowerStar ℓ g).obj N) ≫
      (boundedConstructibleLowerShriekId ℓ B).hom.app
        ((boundedConstructibleUpperStar Λℓ ℓ g).obj
          ((boundedConstructibleLowerStar ℓ g).obj N))).hom
    ?_ ?_
  · have h₁ := congrArg (fun x ↦ x.hom) hP3
    simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
      boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom] at h₁
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    refine Eq.trans ?_ h₁
    simp only [openProperExtension, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
    rfl
  · have h₂ := congrArg (fun x ↦ x.hom) hK
    simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
      openImmersionLowerShriekUpperStarAdjunction_unit_app_hom,
      upperStarComp_inv_app_hom,
      ObjectProperty.FullSubcategory.id_hom] at h₂
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    exact h₂

/-- **`closedExtension` is `openProperExtension`**: for `g` proper and `h` an open immersion with
`g ≫ h` proper, `h_! Rg_* ⟶ R(g ≫ h)_*` adjoint to the inverse of the base change map is
`h_! Rg_* ≅ Rh_! Rg_! ≅ R(g ≫ h)_! ≅ R(g ≫ h)_*`. -/
theorem closedExtension_app_eq_openProperExtension' (g : B ⟶ C) (h : C ⟶ P)
    [IsOpenImmersion h.left] [IsProper g.left] [IsProper (g ≫ h).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (closedExtension (openImmersionAdjunction ℓ h.left) (rfl : g.left ≫ h.left = _)).app N.obj =
      ((openProperExtension ℓ g h).hom.app N).hom :=
  closedExtension_app_eq_openProperExtension ℓ g h N
    (openProperExtension_unit_comp_closedBaseChange ℓ g h N)
end ClosedExtension
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

variable {B F C P X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The compactification route is the fixed-square route** (no hypothesis): the composite of
`ExchangeOnProperBdc` at `g = j ≫ ι` (`compactificationLowerShriekIso`, compatibilities,
`closedExtension`, `lowerStarCompOfEq`), preceded by `Rc_!(Rι_* Rj_* ≅ R(j ≫ ι)_*)` and followed by
the transport along `((j ≫ ι) ≫ h) ≫ p = (j ≫ d) ≫ Δ`, is the underlying morphism of the
fixed-square route `Rc_! Rι_* Rj_* ≅ RΔ_* Rd_! Rj_* ≅ RΔ_* R(j ≫ d)_* ≅ R((j ≫ d) ≫ Δ)_*`
(`Ξ = lowerStarLowerShriekCompIso`). -/
theorem compactificationRoute_ambient_eq_fixedSquareRoute' (j : B ⟶ F) {ι : F ⟶ C} {c : C ⟶ Y}
    {d : F ⟶ X} {Δ : X ⟶ Y} (sq : ι ≫ c = d ≫ Δ) (h : C ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion h.left] [IsProper p.left] (w : h ≫ p = c) [IsProper ι.left]
    [IsProper Δ.left] [IsProper j.left] [IsProper (j ≫ ι).left] [IsProper (j ≫ d).left]
    [IsProper ((j ≫ d) ≫ Δ).left] [IsProper ((j ≫ ι) ≫ c).left] [IsProper ((j ≫ ι) ≫ h).left]
    [IsProper (((j ≫ ι) ≫ h) ≫ p).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    type_of% (compactificationRoute_ambient_eq_fixedSquareRoute ℓ j sq h p w N
      (openProperExtension_unit_comp_closedBaseChange ℓ (j ≫ ι) h N)) :=
  compactificationRoute_ambient_eq_fixedSquareRoute ℓ j sq h p w N
    (openProperExtension_unit_comp_closedBaseChange ℓ (j ≫ ι) h N)

end AlgebraicGeometry.ProEtale.CondensedRing
