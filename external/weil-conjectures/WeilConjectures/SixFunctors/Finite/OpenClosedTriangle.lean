/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Finite direct images: stalks, higher direct images and the open–closed triangle

Let `f : X ⟶ Y` be a finite morphism.

* For a geometric point `y` of `Y` with algebraically closed residue field, the stalk of `f_* G`
  at `y` is the direct sum of the stalks of `G` at the finitely many geometric points over `y`
  (`AlgebraicGeometry.Etale.stalkIsoBiproduct`), the finite product of
  `AlgebraicGeometry.Etale.stalkIsoPi` being a biproduct.
* The higher direct images `Rᑫf_* G` vanish for `q ≠ 0`
  (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedFunctor_lowerStar_of_isFinite`), since
  `f_*` is exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`).
* For complementary open and closed immersions `j : U ⟶ X`, `i : Z ⟶ X`, the open–closed
  triangle `j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ (j_! j^* M)[1]` holds with the *exact* direct image
  `i_*` applied levelwise (`AlgebraicGeometry.Etale.exists_distTriang_openClosed_of_isFinite`),
  the second map being the unit of `i^* ⊣ i_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

attribute [local instance] Abelian.hasFiniteBiproducts

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) [HasSmallSiteSheafify A]

/-- Blueprint `lemma-finite-direct-images--1`: for a finite morphism `f : X ⟶ Y` and a
geometric point `y` of `Y` with algebraically closed residue field, the restrictions of stalks
`AlgebraicGeometry.Etale.stalkRestrict` give an isomorphism from the stalk of `f_* G` at `y` to the
direct sum of the stalks of `G` at the finitely many geometric points of `X` over `y`. This is the
product formula `AlgebraicGeometry.Etale.stalkIsoPi` (natural in `G`:
`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), the finite product being a biproduct. -/
def Etale.stalkIsoBiproduct (G : Sheaf X.smallEtaleTopology A) :
    (pointSmallEtale y).sheafFiber.obj ((f)_*[A].obj G) ≅
      ⨁ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber.obj G :=
  Etale.stalkIsoPi A f y G ≪≫ (biproduct.isoProduct _).symm

omit [HasSmallSiteSheafify A] in
@[reassoc (attr := simp)]
lemma Etale.stalkIsoBiproduct_hom_π (G : Sheaf X.smallEtaleTopology A)
    (t : GeometricFiber f y) :
    (Etale.stalkIsoBiproduct A f y G).hom ≫ biproduct.π _ t = Etale.stalkRestrict A f y t G := by
  simp [Etale.stalkIsoBiproduct, biproduct.isoProduct_inv]

end Stalk

section Concrete

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

section HigherDirectImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  [hJ : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- Blueprint `lemma-finite-direct-images--2`, the vanishing of the higher direct
images: for a finite morphism `f`, `Rᑫf_* G = 0` for every sheaf `G` and `q ≠ 0`. Since `f_*` is
exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`), `Rf_*` is `f_*`
applied levelwise (`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`),
and `f_*` of a sheaf placed in degree `0` is again concentrated in degree `0`. -/
theorem Etale.isZero_homology_rightDerivedFunctor_lowerStar_of_isFinite
    (G : Sheaf X.smallEtaleTopology A) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((f)_*[A].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  let e := (Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory A f).app
      ((DerivedCategory.singleFunctor _ 0).obj G) ≪≫
    ((f)_*[A].mapDerivedCategorySingleFunctor 0).app G
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso e)
  obtain hq | hq := hq.lt_or_gt
  · exact DerivedCategory.isZero_of_isGE
      ((DerivedCategory.singleFunctor _ 0).obj ((f)_*[A].obj G)) 0 q hq
  · exact DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor _ 0).obj ((f)_*[A].obj G)) 0 q hq

end HigherDirectImage

section Triangle

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--8`: for a closed immersion
`i : Z ⟶ X` with complementary open immersion `j : U ⟶ X` and every `M ∈ D(X_ét, A)`, the counit
`j_! j^* M ⟶ M` of `j_! ⊣ j^*` and the unit `M ⟶ i_* i^* M` of `i^* ⊣ Ri_*`, followed by the
identification `Ri_* ≅ i_*` of the derived direct image with the exact direct image `i_*`
applied levelwise (`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`,
`i` being finite), extend to a distinguished triangle

`j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ (j_! j^* M)[1]`.

This is `AlgebraicGeometry.Etale.exists_distTriang_openClosed`, transported along the
identification; it is functorial in `M`, its first two maps being natural transformations. -/
theorem Etale.exists_distTriang_openClosed_of_isFinite
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃ w, Triangle.mk ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app M)
      ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app M ≫
        (Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory A i).hom.app
          (D((i)^*[A]).obj M)) w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed A j i hij M
  let e := (Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory A i).app (D((i)^*[A]).obj M)
  refine ⟨e.inv ≫ w, isomorphic_distinguished _ hw _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp [e]) (by simp [e])

end Triangle

end Concrete

end AlgebraicGeometry

end
