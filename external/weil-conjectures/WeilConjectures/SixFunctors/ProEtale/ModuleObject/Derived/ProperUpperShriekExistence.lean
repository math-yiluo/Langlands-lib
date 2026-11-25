/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.RestrictEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RationalProperLowerStarAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingRestriction

/-!
# The proper direct image on `Dᵇc` is a left adjoint

Let `ℓ` be a prime and `k` a field in which `ℓ` is invertible. For a proper morphism
`p : Z ⟶ Y` of separated `k`-schemes of finite type and the `ℓ`-adic coefficient rings
`Λ = E, 𝒪_E, ℚ̄_ℓ`, the derived pushforward `Rp_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint
when `k` is finite or separably closed (blueprint `theorem-exceptional-inverse-image--18`):

* `isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_finite_or_isSepClosed`,
* `isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_finite_or_isSepClosed`,
* `isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_finite_or_isSepClosed`.

## Proof

The trivial compactification `Z ⟶[𝟙] Z ⟶[p] Y` of `p` (`Compactification.ofIsProper`) has
`Rp_!(c) = Rp_* ∘ (𝟙)_! ≅ Rp_*`. By Brown representability (blueprint
`theorem-existence-exceptional-inverse-image`,
`exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj` and its analogues) its
restriction to the localizing closures `Loc(Dᵇc(Z)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` has a right adjoint `p^!`;
this is where `k` finite or separably closed is used, for the compact generation. By the restriction
theorems (blueprints `theorem-f-shriek-ell-adic-coefficients` and `sk-thm-int-restriction`), `p^!`
maps `Dᵇc(Y)⟦Λ⟧` into `Dᵇc(Z)⟦Λ⟧`. The adjunction `Rp_* ⊣ p^!` then restricts to the full
subcategories `Dᵇc ⊆ Loc(Dᵇc)` (`CategoryTheory.Adjunction.isLeftAdjoint_of_essImage`,
`isLeftAdjoint_lift_rightDerivedLowerStar_of_localizing`).

## The restriction theorems

The restriction theorems (blueprints `theorem-f-shriek-ell-adic-coefficients` and
`sk-thm-int-restriction`:
`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj`,
`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj` and
`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj`) are proved
from the existence of the right adjoint of `Rp_*` on `Dᵇc` for proper `p` over any field
(`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj` and its analogues, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint`): for a
compactification `c = (X ⟶[i] X̄ ⟶[p] Y)`, the restriction of `Rf_!(c)` to `Dᵇc` is `i_! ⋙ Rp_*`, a
left adjoint, and the objects of `Dᵇc` detect isomorphisms of `Loc(Dᵇc)`, so every right adjoint on
`Loc(Dᵇc)` agrees on `Dᵇc` with the right adjoint on `Dᵇc`
(`boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint`).

## Relation to the general case

The theorems above are special cases of the instances
`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj` and its analogues, which hold
over any field. Since the restriction theorems use those instances, the Brown representability
argument here is not an independent proof; it records the route of the blueprint for `k` finite or
separably closed, where `cd_ℓ(k) < ∞` and the bounded constructible complexes are compact in
`Loc(Dᵇc)`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Restricting the adjunction on the localizing closures -/

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]

/-- For a proper `p : Z ⟶ Y`, the inclusions `Dᵇc ⊆ Loc(Dᵇc)` intertwine the restriction of
`Rp_* : D(Z) ⥤ D(Y)` to `Dᵇc` with the lower shriek `Rp_!(c)` on the localizing closures attached
to the trivial compactification `c = (Z ⟶[𝟙] Z ⟶[p] Y)`. -/
noncomputable def ιOfLEcompRightDerivedLowerShriekLocalizingIso
    (hK : ∀ K : (boundedConstructible (condensedRingObj Λ Z)).FullSubcategory,
      boundedConstructible (condensedRingObj Λ Y) (((lowerStar Λ p).rightDerivedFunctor).obj K.obj))
    (hc : LowerShriekLocalizingHypotheses Λ (Compactification.ofIsProper p)) :
    ObjectProperty.ιOfLE (ObjectProperty.le_localizingClosure _) ⋙
        rightDerivedLowerShriekLocalizing hc ≅
      (boundedConstructible (condensedRingObj Λ Y)).lift
          ((boundedConstructible _).ι ⋙ (lowerStar Λ p).rightDerivedFunctor) hK ⋙
        ObjectProperty.ιOfLE (ObjectProperty.le_localizingClosure _) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.localizingClosureLiftCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft (boundedConstructible (condensedRingObj Λ Z)).ι
        (Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ Z) _ ≪≫
          Functor.leftUnitor _) ≪≫
      (ObjectProperty.liftCompιIso _ _ _).symm)

/-- Blueprint `theorem-exceptional-inverse-image--18`, formal part: for a proper `p : Z ⟶ Y`, if
`Rp_*` maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧` and the lower shriek of the trivial compactification on
the localizing closures has a right adjoint `G` mapping `Dᵇc(Y)⟦Λ⟧` into `Dᵇc(Z)⟦Λ⟧`, then the
restriction `Rp_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` is a left adjoint. -/
lemma isLeftAdjoint_lift_rightDerivedLowerStar_of_localizing
    (hK : ∀ K : (boundedConstructible (condensedRingObj Λ Z)).FullSubcategory,
      boundedConstructible (condensedRingObj Λ Y) (((lowerStar Λ p).rightDerivedFunctor).obj K.obj))
    (hc : LowerShriekLocalizingHypotheses Λ (Compactification.ofIsProper p))
    {G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ Z}
    (adj : rightDerivedLowerShriekLocalizing hc ⊣ G)
    (hG : ∀ L : LocalizingBoundedConstructible Λ Y,
      boundedConstructible (condensedRingObj Λ Y) L.obj →
        boundedConstructible (condensedRingObj Λ Z) (G.obj L).obj) :
    ((boundedConstructible (condensedRingObj Λ Y)).lift
      ((boundedConstructible _).ι ⋙ (lowerStar Λ p).rightDerivedFunctor) hK).IsLeftAdjoint :=
  Adjunction.isLeftAdjoint_of_essImage adj (ObjectProperty.fullyFaithfulιOfLE _)
    (ObjectProperty.fullyFaithfulιOfLE _) (ιOfLEcompRightDerivedLowerShriekLocalizingIso Λ p hK hc)
    fun L ↦ ⟨⟨_, hG _ L.2⟩, ⟨Iso.refl _⟩⟩

end General

/-! ### The restriction theorems -/

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)

include aX in
/-- Blueprint `theorem-f-shriek-ell-adic-coefficients` (for `Λ = E`): for the coefficient ring `E̲`
of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a separated finite-type `k`-morphism `f : X ⟶ Y` and a
compactification `c` of `f`, every right adjoint `f^!` of the compact-support direct image
`Rf_! : Loc(Dᵇc(X)⟦E⟧) ⥤ Loc(Dᵇc(Y)⟦E⟧)` (blueprint `theorem-existence-exceptional-inverse-image`)
maps `Dᵇc(Y)⟦E⟧` into `Dᵇc(X)⟦E⟧`.

The restriction of `Rf_!` to `Dᵇc` is `i_! ⋙ Rp_*` for `c = (X ⟶[i] X̄ ⟶[p] Y)`, a left adjoint
since `Rp_*` is one on `Dᵇc` for the proper `p`
(`isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj`); on `Dᵇc(Y)`,
`f^!` is then its right adjoint (`boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint`). -/
theorem boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (hf : f ≫ aY = aX)
    {G : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
      LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X}
    (adj : rightDerivedLowerShriekLocalizing
      (lowerShriek_continuousMapRingObj ℓ E aY c) ⊣ G)
    (L : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y)
    (hL : boundedConstructible _ L.obj) :
    boundedConstructible _ (G.obj L).obj := by
  have : LocallyOfFiniteType (Over.mk aY).hom := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Over.mk aY).hom := ‹QuasiCompact aY›
  have : IsSeparated (Over.mk aY).hom := ‹IsSeparated aY›
  have : LocallyOfFiniteType (Over.mk aX).hom := ‹LocallyOfFiniteType aX›
  have : QuasiCompact (Over.mk aX).hom := ‹QuasiCompact aX›
  have : IsSeparated (Over.mk aX).hom := ‹IsSeparated aX›
  let c' : Compactification (Over.homMk (U := Over.mk aX) (V := Over.mk aY) f hf).left := c
  have := isLeftAdjoint_boundedConstructibleLowerStarOfIsProper_continuousMapRingObj ℓ
    c'.overG E
  have : (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E
      c').IsLeftAdjoint :=
    inferInstanceAs (boundedConstructibleOpenImmersionLowerShriek _ ℓ c'.overI ⋙
      ContinuousMapRingObj.boundedConstructibleLowerStarOfIsProper ℓ E c'.overG).IsLeftAdjoint
  have := isLeftAdjoint_rightDerivedLowerShriekBoundedConstructible_of_iso
    (lowerShriek_continuousMapRingObj ℓ E aY c)
    (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E c')
  exact boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint _ adj L hL

include aX in
/-- Blueprint `theorem-f-shriek-ell-adic-coefficients--1`: for the coefficient ring `𝒪_E` of a
finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a separated finite-type `k`-morphism `f : X ⟶ Y` and a
compactification `c` of `f`, every right adjoint `f^!` of the compact-support direct image
`Rf_! : Loc(Dᵇc(X)⟦𝒪_E⟧) ⥤ Loc(Dᵇc(Y)⟦𝒪_E⟧)` (blueprint `theorem-f-shriek-ell-adic-coefficients--1`)
maps `Dᵇc(Y)⟦𝒪_E⟧` into `Dᵇc(X)⟦𝒪_E⟧`.

The restriction of `Rf_!` to `Dᵇc` is `i_! ⋙ Rp_*` for `c = (X ⟶[i] X̄ ⟶[p] Y)`, a left adjoint
since `Rp_*` is one on `Dᵇc` for the proper `p`
(`isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj`); on `Dᵇc(Y)`,
`f^!` is then its right adjoint (`boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint`). -/
theorem boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (hf : f ≫ aY = aX)
    {G : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
      LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X}
    (adj : rightDerivedLowerShriekLocalizing
      (lowerShriek_padicIntegersRingObj ℓ E aY c) ⊣ G)
    (L : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y)
    (hL : boundedConstructible _ L.obj) :
    boundedConstructible _ (G.obj L).obj := by
  have : LocallyOfFiniteType (Over.mk aY).hom := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Over.mk aY).hom := ‹QuasiCompact aY›
  have : IsSeparated (Over.mk aY).hom := ‹IsSeparated aY›
  have : LocallyOfFiniteType (Over.mk aX).hom := ‹LocallyOfFiniteType aX›
  have : QuasiCompact (Over.mk aX).hom := ‹QuasiCompact aX›
  have : IsSeparated (Over.mk aX).hom := ‹IsSeparated aX›
  let c' : Compactification (Over.homMk (U := Over.mk aX) (V := Over.mk aY) f hf).left := c
  have := isLeftAdjoint_boundedConstructibleLowerStarOfIsProper_padicIntegersRingObj ℓ
    c'.overG E
  have : (PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E
      c').IsLeftAdjoint :=
    inferInstanceAs (boundedConstructibleOpenImmersionLowerShriek _ ℓ c'.overI ⋙
      PadicIntegersRingObj.boundedConstructibleLowerStarOfIsProper ℓ E c'.overG).IsLeftAdjoint
  have := isLeftAdjoint_rightDerivedLowerShriekBoundedConstructible_of_iso
    (lowerShriek_padicIntegersRingObj ℓ E aY c)
    (PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E c')
  exact boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint _ adj L hL

include aX in
/-- Blueprint `theorem-f-shriek-ell-adic-coefficients` (for `Λ = ℚ̄_ℓ`): for the coefficient ring
`ℚ̄_ℓ`, a separated finite-type `k`-morphism `f : X ⟶ Y` and a compactification `c` of `f`, every
right adjoint `f^!` of the compact-support direct image
`Rf_! : Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧) ⥤ Loc(Dᵇc(Y)⟦ℚ̄_ℓ⟧)` (blueprint
`theorem-existence-exceptional-inverse-image`) maps `Dᵇc(Y)⟦ℚ̄_ℓ⟧` into `Dᵇc(X)⟦ℚ̄_ℓ⟧`.

The restriction of `Rf_!` to `Dᵇc` is `i_! ⋙ Rp_*` for `c = (X ⟶[i] X̄ ⟶[p] Y)`, a left adjoint
since `Rp_*` is one on `Dᵇc` for the proper `p`
(`isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`); on `Dᵇc(Y)`,
`f^!` is then its right adjoint (`boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint`). -/
theorem boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj
    (hf : f ≫ aY = aX)
    {G : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
      LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X}
    (adj : rightDerivedLowerShriekLocalizing
      (lowerShriek_padicAlgClRingObj ℓ aY c) ⊣ G)
    (L : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y)
    (hL : boundedConstructible _ L.obj) :
    boundedConstructible _ (G.obj L).obj := by
  have : LocallyOfFiniteType (Over.mk aY).hom := ‹LocallyOfFiniteType aY›
  have : QuasiCompact (Over.mk aY).hom := ‹QuasiCompact aY›
  have : IsSeparated (Over.mk aY).hom := ‹IsSeparated aY›
  have : LocallyOfFiniteType (Over.mk aX).hom := ‹LocallyOfFiniteType aX›
  have : QuasiCompact (Over.mk aX).hom := ‹QuasiCompact aX›
  have : IsSeparated (Over.mk aX).hom := ‹IsSeparated aX›
  let c' : Compactification (Over.homMk (U := Over.mk aX) (V := Over.mk aY) f hf).left := c
  have := isLeftAdjoint_boundedConstructibleLowerStarOfIsProper_padicAlgClRingObj ℓ c'.overG
  have : (boundedConstructibleLowerShriekOfCompactification ℓ c').IsLeftAdjoint :=
    inferInstanceAs (boundedConstructibleOpenImmersionLowerShriek _ ℓ c'.overI ⋙
      boundedConstructibleLowerStarOfIsProper ℓ c'.overG).IsLeftAdjoint
  have := isLeftAdjoint_rightDerivedLowerShriekBoundedConstructible_of_iso
    (lowerShriek_padicAlgClRingObj ℓ aY c)
    (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c')
  exact boundedConstructible_rightAdjoint_obj_of_isLeftAdjoint _ adj L hL

end EllAdic

/-! ### The proper direct image on `Dᵇc` is a left adjoint -/

section ProperLowerStar

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- Blueprint `theorem-exceptional-inverse-image--16`, for `k` finite or separably closed:
for a proper morphism `g : Z ⟶ Y` and a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` is a left adjoint. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj_of_finite_or_isSepClosed
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (hk : Finite k ∨ IsSepClosed k) :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint := by
  have hc := lowerShriek_continuousMapRingObj ℓ E Y.hom
    (Compactification.ofIsProper g.left)
  obtain ⟨G, adj, -⟩ := exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj
    ℓ Z.hom Y.hom (Compactification.ofIsProper g.left) hk E
  exact isLeftAdjoint_lift_rightDerivedLowerStar_of_localizing _ g.left _ hc adj
    fun L hL ↦
      boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj
        ℓ Z.hom Y.hom _ E (Over.w g) adj L hL

/-- Blueprint `theorem-exceptional-inverse-image--15`, for `k` finite or separably closed:
for a proper morphism `g : Z ⟶ Y` and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived
pushforward `Rg_* : Dᵇc(Z)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` is a left adjoint. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj_of_finite_or_isSepClosed
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (hk : Finite k ∨ IsSepClosed k) :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint := by
  have hc := lowerShriek_padicIntegersRingObj ℓ E Y.hom
    (Compactification.ofIsProper g.left)
  obtain ⟨G, adj, -⟩ := exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj
    ℓ Z.hom Y.hom (Compactification.ofIsProper g.left) hk E
  exact isLeftAdjoint_lift_rightDerivedLowerStar_of_localizing _ g.left _ hc adj
    fun L hL ↦
      boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj
        ℓ Z.hom Y.hom _ E (Over.w g) adj L hL

/-- Blueprint `theorem-exceptional-inverse-image--17`, for `k` finite or separably
closed: for a proper morphism `g : Z ⟶ Y`, the derived pushforward
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` is a left adjoint. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_finite_or_isSepClosed
    (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructibleLowerStar ℓ g).IsLeftAdjoint := by
  have hc := lowerShriek_padicAlgClRingObj ℓ Y.hom
    (Compactification.ofIsProper g.left)
  obtain ⟨G, adj, -⟩ := exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj
    ℓ Z.hom Y.hom (Compactification.ofIsProper g.left) hk
  exact isLeftAdjoint_lift_rightDerivedLowerStar_of_localizing _ g.left _ hc adj
    fun L hL ↦
      boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj
        ℓ Z.hom Y.hom _ (Over.w g) adj L hL

end ProperLowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
