/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# Coherence of the mixed-support cup product

Let `a : X ⟶ Y` be a morphism admitting a compactification. The *mixed-support cup product*
(`AlgebraicGeometry.Etale.mixedSupportCupProduct`, blueprint `theorem-poincare-duality--6`)
```
⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)
```
is the projection map of `Ra_!` followed by the counit of `La^* ⊣ Ra_*`. We prove its coherence
(blueprint `theorem-poincare-duality--7`): it is natural in `K` and `L`, associative with
respect to the cup product `∪ : Ra_* L ⊗ᴸ Ra_* M ⟶ Ra_*(L ⊗ᴸ M)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarCupProduct`), unital for the unit section
`1 : Λ_Y ⟶ Ra_* Λ_X` (`AlgebraicGeometry.Etale.rightDerivedLowerStarUnit`), and compatible with
`∪` through the forget-supports map `Ra_! ⟶ Ra_*`, in particular through `Ra_! ≅ Ra_*` for proper
`a`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStarCupProduct`: the cup product
  `Ra_* L ⊗ᴸ Ra_* M ⟶ Ra_*(L ⊗ᴸ M)`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarUnit`: the unit section `1 : Λ_Y ⟶ Ra_* Λ_X`.

## Main statements

- `AlgebraicGeometry.Etale.mixedSupportCupProduct_naturality`: naturality in `K` and `L`.
- `AlgebraicGeometry.Etale.mixedSupportCupProduct_associativity`: associativity.
- `AlgebraicGeometry.Etale.mixedSupportCupProduct_rightUnitality`: the unit acts as the identity.
- `AlgebraicGeometry.Etale.mixedSupportCupProduct_comp_lowerShriekIsoLowerStar`:
  for proper `a`, the mixed-support cup product is the cup product `∪` read through
  `Ra_! ≅ Ra_*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarCupProduct_associativity`: associativity of `∪`.

## Implementation notes

All statements are deduced from the abstract coherence results of
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct`. The kernel is sensitive to
how the objects of the derived categories are written: the proofs only rewrite with lemmas whose
two sides agree syntactically up to unfolding of `AlgebraicGeometry.Etale.derivedTensor`, and they
never introduce `let`-bound names for the chosen compactification, whose unfolding makes the kernel
time out.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

section CupProduct

variable {X Y : Scheme.{u}} (a : X ⟶ Y)

/-- Blueprint `theorem-poincare-duality--7`: the *cup product*
`∪ : Ra_* K ⊗ᴸ Ra_* L ⟶ Ra_*(K ⊗ᴸ L)`, that is `RΓ(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ(X, K ⊗ᴸ L)` read in
`D(Y_ét)`: the projection map of `Ra_*` followed by `Ra_*(K ⊗ᴸ ε_L)`, for the counit
`ε_L : La^* Ra_* L ⟶ L` of `La^* ⊣ Ra_*`. -/
noncomputable def rightDerivedLowerStarCupProduct [Etale.UpperStarPreservesFlat A]
    (K L : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R((a)_*[A])).obj K)).obj ((R((a)_*[A])).obj L) ⟶
      (R((a)_*[A])).obj (((derivedTensor A X).obj K).obj L) :=
  (derivedUpperStarLowerStarAdjunction A a).rightAdjointCupProduct
    (leftDerivedUpperStarTensorComparison A a) K L

/-- Blueprint `theorem-poincare-duality--7`: the *unit section* `1 : Λ_Y ⟶ Ra_* Λ_X`, the unit
`1 ∈ H⁰(X, Λ)` read in `D(Y_ét)`: the transpose along `La^* ⊣ Ra_*` of the identification
`La^* Λ_Y ≅ Λ_X`. -/
noncomputable def rightDerivedLowerStarUnit [Etale.UpperStarPreservesFlat A] :
    (𝟙_ 𝐃(Y, A)) ⟶ (R((a)_*[A])).obj (𝟙_ 𝐃(X, A)) :=
  (derivedUpperStarLowerStarAdjunction A a).homEquiv _ _ (leftDerivedUpperStarUnitIso A a).hom

end CupProduct

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

section Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/- The projection map of `Rf_!(c) = Rg_* ∘ i_!`, in the form of
`CategoryTheory.Adjunction.compProjectionMap`. -/
set_option quotPrecheck false in
local notation "𝚷" =>
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap
    (leftDerivedUpperStarTensorComparison A c.g) D((c.i)_!open[A])
    (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
    (fun L ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app L)

/-- The projection map of `Rf_!(c)` is natural in its first variable. -/
lemma compactificationProjectionMap_naturality_left {K K' : 𝐃(X, A)} (x : K ⟶ K')
    (L : 𝐃(Y, A)) :
    (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map x ▷ L ≫ 𝚷 K' L =
      𝚷 K L ≫ (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map (x ▷ L((f)^*[A]).obj L) :=
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_naturality_left _
    (fun x N ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_left A c.i x N) x L

/-- The projection map of `Rf_!(c)` is natural in its second variable. -/
lemma compactificationProjectionMap_naturality_right (K : 𝐃(X, A)) {L L' : 𝐃(Y, A)}
    (y : L ⟶ L') :
    (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).obj K ◁ y ≫ 𝚷 K L' =
      𝚷 K L ≫ (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map (K ◁ L((f)^*[A]).map y) :=
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_naturality_right _
    (fun K _ _ y ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right A c.i K y)
    (fun y ↦ (leftDerivedUpperStarCompactificationIso A c).hom.naturality y) K y

/-- Associativity of the projection map of `Rf_!(c)`. -/
lemma compactificationProjectionMap_associativity (K : 𝐃(X, A)) (L L' : 𝐃(Y, A)) :
    𝚷 K L ▷ L' ≫ 𝚷 (K ⊗ L((f)^*[A]).obj L) L' ≫
        (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ 𝚷 K (L ⊗ L') ≫
        (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map
          (K ◁ ((leftDerivedUpperStarTensorComparison A f).app L).app L') :=
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_associativity _
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app N).app N')
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A f).app L).app L')
    (leftDerivedUpperStarTensorComparison_associativity A c.g)
    (fun x N ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_left A c.i x N)
    (fun K _ _ y ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right A c.i K y)
    (derivedOpenImmersionLowerShriekProjectionIso_inv_associativity A c.i)
    (leftDerivedUpperStarCompactificationIso_hom_app_tensor A c) K L L'

/-- Right unitality of the projection map of `Rf_!(c)`. -/
lemma compactificationProjectionMap_rightUnitality (K : 𝐃(X, A)) :
    𝚷 K (𝟙_ _) ≫ (D((c.i)_!open[A]) ⋙ R((c.g)_*[A])).map
        (K ◁ (leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ K).hom) =
      (ρ_ _).hom :=
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_rightUnitality _
    (leftDerivedUpperStarUnitIso A c.g).hom (leftDerivedUpperStarUnitIso A c.i).hom
    (leftDerivedUpperStarUnitIso A f).hom
    (leftDerivedUpperStarTensorComparison_rightUnitor_hom A c.g)
    (fun K _ _ y ↦ derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right A c.i K y)
    (derivedOpenImmersionLowerShriekProjectionIso_inv_rightUnitality A c.i)
    (leftDerivedUpperStarCompactificationIso_hom_app_unit A c) K

/-- The forget-supports map `Rf_!(c) ⟶ Ri_* ⋙ Rg_* ⟶ Rf_*` of a compactification is compatible
with the projection maps. -/
lemma compactificationProjectionMap_comp_forgetSupports (K : 𝐃(X, A)) (L : 𝐃(Y, A)) :
    𝚷 K L ≫ (Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A c.i)
        (R((c.g)_*[A])) ≫ rightDerivedLowerStarCompHom A c.i c.g f c.comm).app
          (K ⊗ L((f)^*[A]).obj L) =
      (Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A c.i) (R((c.g)_*[A])) ≫
          rightDerivedLowerStarCompHom A c.i c.g f c.comm).app K ▷ L ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app L := by
  refine (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_comp _
    (derivedUpperStarLowerStarAdjunction A c.i) (derivedUpperStarLowerStarAdjunction A f)
    (leftDerivedUpperStarTensorComparison A c.i) (leftDerivedUpperStarTensorComparison A f) _ _
    (derivedOpenImmersionLowerShriekProjectionIso_inv_comp_toLowerStar A c.i)
    (fun M L ↦ ?_) K L
  have h := rightDerivedLowerStarProjectionMap_comp' A c.i c.g f c.comm M L
  rw [← Iso.symm_hom, ← leftDerivedUpperStarCompactificationIso_eq] at h
  simp only [derivedTensor_map_app, derivedTensor_obj_map] at h
  exact h

end Compactification

section Composition

omit [Etale.UpperStarPreservesFlat A] [ConcreteCategory A FA]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*`, transported along
`g₁₂ = g₁ ≫ g₂`, is the conjugate of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` under the
adjunctions `Lg^* ⊣ Rg_*`. -/
lemma rightDerivedLowerStarComp_hom_comp_congr_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) :
    (rightDerivedLowerStarComp A g₁ g₂).hom ≫ (rightDerivedLowerStarCongr A hg.symm).hom =
      rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg := by
  subst hg
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, Category.comp_id,
    rightDerivedLowerStarCompHom, conjugateEquiv_leftDerivedUpperStarComp_hom]
  rfl

end Composition

section MixedSupport

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

/-- The projection map of `Ra_!` is the `compProjectionMap` of the chosen compactification. -/
lemma projectionMap_app_app_eq (K : 𝐃(X, A)) (L : 𝐃(Y, A)) :
    ((projectionMap A a).app K).app L =
      (derivedUpperStarLowerStarAdjunction A
          (HasCompactification.compactification a).g).compProjectionMap
          (leftDerivedUpperStarTensorComparison A (HasCompactification.compactification a).g)
          D(((HasCompactification.compactification a).i)_!open[A])
          (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A
            (HasCompactification.compactification a).i).inv.app K).app N)
          (fun L ↦ (leftDerivedUpperStarCompactificationIso A
            (HasCompactification.compactification a)).hom.app L) K L :=
  rfl

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A] in
/-- `Ra_!` acts on morphisms as `j_! ⋙ Rg_*` for the chosen compactification `a = g ∘ j`. -/
lemma rightDerivedLowerShriek_map_eq {K K' : 𝐃(X, A)} (x : K ⟶ K') :
    (R(a)_![A]).map x =
      (D(((HasCompactification.compactification a).i)_!open[A]) ⋙
        R(((HasCompactification.compactification a).g)_*[A])).map x :=
  rfl

/-- The mixed-support cup product is the cup product attached to the projection map of the
chosen compactification (`CategoryTheory.Adjunction.cupProductOfProjection`). -/
lemma mixedSupportCupProduct_eq (K L : 𝐃(X, A)) :
    mixedSupportCupProduct A a K L =
      (derivedUpperStarLowerStarAdjunction A a).cupProductOfProjection
        (D(((HasCompactification.compactification a).i)_!open[A]) ⋙
          R(((HasCompactification.compactification a).g)_*[A]))
        ((derivedUpperStarLowerStarAdjunction A
          (HasCompactification.compactification a).g).compProjectionMap
          (leftDerivedUpperStarTensorComparison A (HasCompactification.compactification a).g)
          D(((HasCompactification.compactification a).i)_!open[A])
          (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A
            (HasCompactification.compactification a).i).inv.app K).app N)
          (fun L ↦ (leftDerivedUpperStarCompactificationIso A
            (HasCompactification.compactification a)).hom.app L)) K L := by
  rw [mixedSupportCupProduct, projectionMap_app_app_eq, derivedTensor_obj_map,
    rightDerivedLowerShriek_map_eq, Adjunction.cupProductOfProjection]

/-- Blueprint `theorem-poincare-duality--7`: the mixed-support cup product is natural in its
first variable. -/
lemma mixedSupportCupProduct_naturality_left {K K' : 𝐃(X, A)} (x : K ⟶ K') (L : 𝐃(X, A)) :
    ((derivedTensor A Y).map ((R(a)_![A]).map x)).app ((R((a)_*[A])).obj L) ≫
        mixedSupportCupProduct A a K' L =
      mixedSupportCupProduct A a K L ≫ (R(a)_![A]).map (((derivedTensor A X).map x).app L) := by
  simp only [mixedSupportCupProduct_eq, derivedTensor_map_app, rightDerivedLowerShriek_map_eq]
  exact (derivedUpperStarLowerStarAdjunction A a).cupProductOfProjection_naturality_left
    (fun x L ↦ compactificationProjectionMap_naturality_left A
      (HasCompactification.compactification a) x L) x L

/-- Blueprint `theorem-poincare-duality--7`: the mixed-support cup product is natural in its
second variable. -/
lemma mixedSupportCupProduct_naturality_right (K : 𝐃(X, A)) {L L' : 𝐃(X, A)} (y : L ⟶ L') :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map ((R((a)_*[A])).map y) ≫
        mixedSupportCupProduct A a K L' =
      mixedSupportCupProduct A a K L ≫ (R(a)_![A]).map (((derivedTensor A X).obj K).map y) := by
  simp only [mixedSupportCupProduct_eq, derivedTensor_obj_map, rightDerivedLowerShriek_map_eq]
  exact (derivedUpperStarLowerStarAdjunction A a).cupProductOfProjection_naturality_right
    (fun K _ _ y ↦ compactificationProjectionMap_naturality_right A
      (HasCompactification.compactification a) K y) K y

/-- Blueprint `theorem-poincare-duality--7`: Coherence of the mixed-support cup product.

The mixed-support cup product `⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)` is natural in `K` and
`L`. -/
theorem mixedSupportCupProduct_naturality {K K' L L' : 𝐃(X, A)} (x : K ⟶ K') (y : L ⟶ L') :
    ((derivedTensor A Y).map ((R(a)_![A]).map x)).app ((R((a)_*[A])).obj L) ≫
        ((derivedTensor A Y).obj ((R(a)_![A]).obj K')).map ((R((a)_*[A])).map y) ≫
        mixedSupportCupProduct A a K' L' =
      mixedSupportCupProduct A a K L ≫
        (R(a)_![A]).map (((derivedTensor A X).map x).app L ≫
          ((derivedTensor A X).obj K').map y) := by
  rw [mixedSupportCupProduct_naturality_right, reassoc_of% mixedSupportCupProduct_naturality_left,
    Functor.map_comp]

/-- Blueprint `theorem-poincare-duality--7`: Coherence of the mixed-support cup product.

**Associativity**: on `RΓ_c(X, K) ⊗ RΓ(X, L) ⊗ RΓ(X, M)`, cupping first with `L` and then with
`M` is cupping with the cup product `L ∪ M`:
```
(Ra_! K ⊗ᴸ Ra_* L) ⊗ᴸ Ra_* M --⌣_c ⊗ 1--> Ra_!(K ⊗ᴸ L) ⊗ᴸ Ra_* M --⌣_c--> Ra_!((K ⊗ᴸ L) ⊗ᴸ M)
          | α                                                                 | Ra_!(α)
          v                                                                   v
Ra_! K ⊗ᴸ (Ra_* L ⊗ᴸ Ra_* M) --1 ⊗ ∪--> Ra_! K ⊗ᴸ Ra_*(L ⊗ᴸ M) --⌣_c--> Ra_!(K ⊗ᴸ (L ⊗ᴸ M))
```
-/
theorem mixedSupportCupProduct_associativity (K L M : 𝐃(X, A)) :
    ((derivedTensor A Y).map (mixedSupportCupProduct A a K L)).app ((R((a)_*[A])).obj M) ≫
        mixedSupportCupProduct A a (((derivedTensor A X).obj K).obj L) M ≫
        (R(a)_![A]).map (derivedTensorAssociator A X K L M).hom =
      (derivedTensorAssociator A Y _ _ _).hom ≫
        ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
          (rightDerivedLowerStarCupProduct A a L M) ≫
        mixedSupportCupProduct A a K (((derivedTensor A X).obj L).obj M) := by
  simp only [mixedSupportCupProduct_eq, derivedTensor_map_app, derivedTensor_obj_map,
    derivedTensorAssociator_eq, rightDerivedLowerStarCupProduct, rightDerivedLowerShriek_map_eq]
  exact (derivedUpperStarLowerStarAdjunction A a).cupProductOfProjection_associativity
    (leftDerivedUpperStarTensorComparison A a)
    (fun x L ↦ compactificationProjectionMap_naturality_left A
      (HasCompactification.compactification a) x L)
    (fun K _ _ y ↦ compactificationProjectionMap_naturality_right A
      (HasCompactification.compactification a) K y)
    (compactificationProjectionMap_associativity A (HasCompactification.compactification a))
    K L M

/-- Blueprint `theorem-poincare-duality--7`: Coherence of the mixed-support cup product.

**Unitality**: the unit `1 ∈ H⁰(X, Λ)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarUnit`)
acts as the identity: `Ra_! K ⊗ᴸ Λ_Y ⟶ Ra_! K ⊗ᴸ Ra_* Λ_X ⟶ Ra_!(K ⊗ᴸ Λ_X) ≅ Ra_! K` is the
right unitor. -/
theorem mixedSupportCupProduct_rightUnitality (K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map (rightDerivedLowerStarUnit A a) ≫
        mixedSupportCupProduct A a K (𝟙_ _) ≫
        (R(a)_![A]).map (derivedTensorRightUnitor A X K).hom =
      (derivedTensorRightUnitor A Y _).hom := by
  simp only [mixedSupportCupProduct_eq, derivedTensor_obj_map, derivedTensorRightUnitor_eq,
    rightDerivedLowerStarUnit, rightDerivedLowerShriek_map_eq]
  exact (derivedUpperStarLowerStarAdjunction A a).cupProductOfProjection_rightUnitality
    (leftDerivedUpperStarUnitIso A a).hom
    (fun K _ _ y ↦ compactificationProjectionMap_naturality_right A
      (HasCompactification.compactification a) K y)
    (compactificationProjectionMap_rightUnitality A (HasCompactification.compactification a)) K

omit [Etale.UpperStarPreservesFlat A]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- The forget-supports map `Ra_! ⟶ Ra_*` of the chosen compactification `(i, g)`, written as
`Rg_*` of `i_! ⟶ Ri_*` followed by the composition isomorphism `Ri_* ⋙ Rg_* ⟶ Ra_*` conjugate to
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`. -/
lemma rightDerivedLowerShriekToLowerStarComp_comp_eq :
    rightDerivedLowerShriekToLowerStarComp A a ≫ (rightDerivedLowerStarComp A _ _).hom ≫
        (rightDerivedLowerStarCongr A (HasCompactification.compactification a).comm.symm).hom =
      Functor.whiskerRight
          (derivedOpenImmersionLowerShriekToLowerStar A (HasCompactification.compactification a).i)
          (R(((HasCompactification.compactification a).g)_*[A])) ≫
        rightDerivedLowerStarCompHom A (HasCompactification.compactification a).i
          (HasCompactification.compactification a).g a
          (HasCompactification.compactification a).comm := by
  rw [rightDerivedLowerStarComp_hom_comp_congr_hom]
  rfl

/-- Blueprint `theorem-poincare-duality--7`: Coherence of the mixed-support cup product.

The mixed-support cup product is compatible with the cup product
`∪ : Ra_* K ⊗ᴸ Ra_* L ⟶ Ra_*(K ⊗ᴸ L)` through the forget-supports map `s : Ra_! ⟶ Ra_*`:
`⌣_c ≫ s = (s ⊗ 1) ≫ ∪`. -/
theorem mixedSupportCupProduct_comp_forgetSupports (K L : 𝐃(X, A)) :
    mixedSupportCupProduct A a K L ≫
        (rightDerivedLowerShriekToLowerStarComp A a ≫ (rightDerivedLowerStarComp A _ _).hom ≫
          (rightDerivedLowerStarCongr A
            (HasCompactification.compactification a).comm.symm).hom).app _ =
      ((derivedTensor A Y).map ((rightDerivedLowerShriekToLowerStarComp A a ≫
          (rightDerivedLowerStarComp A _ _).hom ≫ (rightDerivedLowerStarCongr A
            (HasCompactification.compactification a).comm.symm).hom).app K)).app _ ≫
        rightDerivedLowerStarCupProduct A a K L := by
  simp only [rightDerivedLowerShriekToLowerStarComp_comp_eq, mixedSupportCupProduct_eq,
    derivedTensor_map_app, rightDerivedLowerStarCupProduct]
  exact (derivedUpperStarLowerStarAdjunction A a).cupProductOfProjection_comp
    (leftDerivedUpperStarTensorComparison A a) _
    (compactificationProjectionMap_comp_forgetSupports A (HasCompactification.compactification a))
    K L

/-- Blueprint `theorem-poincare-duality--7`: Coherence of the mixed-support cup product.

For a proper morphism `a`, the mixed-support cup product is the cup product
`∪ : Ra_* K ⊗ᴸ Ra_* L ⟶ Ra_*(K ⊗ᴸ L)` read through the identification `Ra_! ≅ Ra_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), i.e. through
`RΓ_c(X, -) ≅ RΓ(X, -)`. -/
theorem mixedSupportCupProduct_comp_lowerShriekIsoLowerStar [IsProper a]
    (K L : 𝐃(X, A)) :
    mixedSupportCupProduct A a K L ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar A a).hom.app _ =
      ((derivedTensor A Y).map ((rightDerivedLowerShriekIsoRightDerivedLowerStar A a).hom.app
          K)).app _ ≫
        rightDerivedLowerStarCupProduct A a K L := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom]
  exact mixedSupportCupProduct_comp_forgetSupports A a K L

end MixedSupport

/-- Blueprint `theorem-poincare-duality--7`: Coherence of the mixed-support cup product.

**Associativity of the cup product** `∪ : Ra_* K ⊗ᴸ Ra_* L ⟶ Ra_*(K ⊗ᴸ L)`, the compatibility
with the iterate of the cup product. -/
theorem rightDerivedLowerStarCupProduct_associativity {X Y : Scheme.{u}} (a : X ⟶ Y)
    (K L M : 𝐃(X, A)) :
    ((derivedTensor A Y).map (rightDerivedLowerStarCupProduct A a K L)).app
          ((R((a)_*[A])).obj M) ≫
        rightDerivedLowerStarCupProduct A a (((derivedTensor A X).obj K).obj L) M ≫
        (R((a)_*[A])).map (derivedTensorAssociator A X K L M).hom =
      (derivedTensorAssociator A Y _ _ _).hom ≫
        ((derivedTensor A Y).obj ((R((a)_*[A])).obj K)).map
          (rightDerivedLowerStarCupProduct A a L M) ≫
        rightDerivedLowerStarCupProduct A a K (((derivedTensor A X).obj L).obj M) := by
  simp only [derivedTensor_map_app, derivedTensor_obj_map, derivedTensorAssociator_eq,
    rightDerivedLowerStarCupProduct]
  exact (derivedUpperStarLowerStarAdjunction A a).rightAdjointCupProduct_associativity _
    (leftDerivedUpperStarTensorComparison_associativity A a) K L M

end Etale

end AlgebraicGeometry
