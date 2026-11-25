/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.RecollementIsoAlgebra
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational

/-!
# Frobenius-equivariance of the closed-support triangle on `Dᵇc(-, E)`

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` the complementary quasi-compact open
immersion, `X` being of finite type over a field `k`, and let `τX : X ⟶ X`, `τZ : Z ⟶ Z`,
`τU : U ⟶ U` be endomorphisms commuting with `i` and `j`. The intended instance is
`τ = Fr⁻¹` for the geometric Frobenius `Fr` of the geometric fibres `X̄`, `Z̄`, `Ū` of
`k₀`-schemes: the direct image `R(Fr⁻¹)_*` is the pullback `Fr^*`, so that an object of the
rational stage `Dᵇc(X̄, E)` with a Frobenius structure is a pair `(K, θ : R(τX)_* K ≅ K)`, an
object of `CategoryTheory.Endofunctor.IsoAlgebra`.

This file proves the Weil clause of blueprint `lemma-local-cohomology-right-adjoint--2` at the stage
`E`, in this form: the direct images along `τX`, `τZ`, `τU` on `Dᵇc(-, E)` commute with `i_*` and
`Rj_*` (`AlgebraicGeometry.Etale.boundedConstructibleRationalRightDerivedLowerStarCommIso`), so
the general results of `WeilConjectures.CategoryTheory.Triangulated.RecollementIsoAlgebra` apply:

1. `Ri^!` carries Frobenius structures and the adjunction `i_* ⊣ Ri^!` lifts to objects with
   Frobenius structure, with the original unit and counit
   (`AlgebraicGeometry.Etale.boundedConstructibleRationalClosedUpperShriekIsoAlgebraAdjunction`);
   the same holds for `j^* ⊣ Rj_*`
   (`AlgebraicGeometry.Etale.boundedConstructibleRationalUpperStarIsoAlgebraAdjunction`);
2. for `(K, θ)` the three arrows of the closed-support triangle
   `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1]` are Frobenius-equivariant
   (`AlgebraicGeometry.Etale.boundedConstructibleRationalClosedSupportTriangleIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Endofunctor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] (M : Submonoid Λ) {I : Ideal Λ}

set_option hygiene false in
/-- The rational stage `Dᵇc(X, E) = Dᵇc(X, 𝒪_E)[M⁻¹]`. -/
local notation "𝐃ᵇc(" X ")" =>
  Rationalization M (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory

variable {X Y : Scheme.{u}} [IsNoetherianRing Λ]
  [Fact (∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})]
  [Finite (Λ ⧸ I)] {k : Type u} [Field k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  (f : Y ⟶ X) [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
  (τX : X ⟶ X) [IsSeparated τX] [QuasiCompact τX] [LocallyOfFiniteType τX]
  (τY : Y ⟶ Y) [IsSeparated τY] [QuasiCompact τY] [LocallyOfFiniteType τY]

variable (I) in
/-- For `f ≫ τX = τY ≫ f`, the isomorphism `Rf_* ⋙ RτX_* ≅ RτY_* ⋙ Rf_*` on `Dᵇc(-, 𝒪_E)`,
the composition isomorphisms of the derived direct images. -/
noncomputable def boundedConstructibleIntegralRightDerivedLowerStarCommIso
    (h : f ≫ τX = τY ≫ f) :
    boundedConstructibleIntegralRightDerivedLowerStar I aX f ⋙
        boundedConstructibleIntegralRightDerivedLowerStar I aX τX ≅
      boundedConstructibleIntegralRightDerivedLowerStar I aY τY ⋙
        boundedConstructibleIntegralRightDerivedLowerStar I aX f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) f τX ≪≫
        rightDerivedLowerStarCongr _ h ≪≫ (rightDerivedLowerStarComp _ τY f).symm))

variable (I) in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): for
`f ≫ τX = τY ≫ f`, the isomorphism `Rf_* ⋙ RτX_* ≅ RτY_* ⋙ Rf_*` on `Dᵇc(-, E)`, induced by
`AlgebraicGeometry.Etale.boundedConstructibleIntegralRightDerivedLowerStarCommIso`. -/
noncomputable def boundedConstructibleRationalRightDerivedLowerStarCommIso
    (h : f ≫ τX = τY ≫ f) :
    boundedConstructibleRationalRightDerivedLowerStar M I aX f ⋙
        boundedConstructibleRationalRightDerivedLowerStar M I aX τX ≅
      boundedConstructibleRationalRightDerivedLowerStar M I aY τY ⋙
        boundedConstructibleRationalRightDerivedLowerStar M I aX f :=
  (Rationalization.mapComp M _ _).symm ≪≫
    Rationalization.mapNatIso M
      (boundedConstructibleIntegralRightDerivedLowerStarCommIso I aX aY f τX τY h) ≪≫
    Rationalization.mapComp M _ _

section ClosedSupport

variable {U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
  (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
  (aU : U ⟶ Spec (.of k)) [LocallyOfFiniteType aU] [QuasiCompact aU]
  (τZ : Z ⟶ Z) [IsSeparated τZ] [QuasiCompact τZ] [LocallyOfFiniteType τZ]
  (τU : U ⟶ U) [IsSeparated τU] [QuasiCompact τU] [LocallyOfFiniteType τU]
  (hi : i ≫ τX = τZ ≫ i) (hj : j ≫ τX = τU ≫ j)

variable (I)

/-- The isomorphism `j^* ⋙ RτU_* ≅ RτX_* ⋙ j^*` on `Dᵇc(-, E)`, whose inverse is the mate of
`Rj_* ⋙ RτX_* ≅ RτU_* ⋙ Rj_*` along `j^* ⊣ Rj_*`
(`CategoryTheory.Pretriangulated.Recollement.leftAdjointIso`).
Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`). -/
noncomputable def boundedConstructibleRationalUpperStarCommIso :
    boundedConstructibleRationalUpperStar M I j ⋙
        boundedConstructibleRationalRightDerivedLowerStar M I aU τU ≅
      boundedConstructibleRationalRightDerivedLowerStar M I aX τX ⋙
        boundedConstructibleRationalUpperStar M I j :=
  Recollement.leftAdjointIso (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aZ i τX τZ hi)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aU j τX τU hj)
    (isZero_boundedConstructibleRationalUpperStar_obj_rightDerivedLowerStar_obj M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStar_essImage_of_isZero M aX i j hij)

/-- The Frobenius structure `Rj_* ⋙ RτX_* ≅ RτU_* ⋙ Rj_*` is the mate of the inverse of the
Frobenius structure `AlgebraicGeometry.Etale.boundedConstructibleRationalUpperStarCommIso` of
`j^*` along `j^* ⊣ Rj_*`. -/
lemma mateEquiv_boundedConstructibleRationalUpperStarCommIso_inv :
    mateEquiv (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
        (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
        (boundedConstructibleRationalUpperStarCommIso M I aX τX i j hij aZ aU τZ τU hi hj).inv =
      (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aU j τX τU hj).hom :=
  Recollement.mateEquiv_leftAdjointIso_inv _ _ _ _ _

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): the adjunction
`j^* ⊣ Rj_*` on `Dᵇc(-, E)` lifts to objects with Frobenius structure (pairs
`(K, θ : RτX_* K ≅ K)`), with the original unit and counit: the unit `K ⟶ Rj_* j^* K` is
Frobenius-equivariant. -/
noncomputable def boundedConstructibleRationalUpperStarIsoAlgebraAdjunction :
    IsoAlgebra.mapOfNatIso
        (boundedConstructibleRationalUpperStarCommIso M I aX τX i j hij aZ aU τZ τU hi hj) ⊣
      IsoAlgebra.mapOfNatIso
        (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aU j τX τU hj) :=
  IsoAlgebra.mapOfNatIsoAdjunction (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
    _ _
    (mateEquiv_boundedConstructibleRationalUpperStarCommIso_inv M I aX τX i j hij aZ aU τZ τU hi hj)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): the Frobenius
structure `Ri^! ⋙ RτZ_* ≅ RτX_* ⋙ Ri^!` of the exceptional inverse image on `Dᵇc(-, E)`, the
mate of the Frobenius structure of `i_*` along `i_* ⊣ Ri^!`
(`CategoryTheory.Pretriangulated.Recollement.rightAdjointIso`). -/
noncomputable def boundedConstructibleRationalClosedUpperShriekCommIso :
    boundedConstructibleRationalClosedUpperShriek M I aX i j hij ⋙
        boundedConstructibleRationalRightDerivedLowerStar M I aZ τZ ≅
      boundedConstructibleRationalRightDerivedLowerStar M I aX τX ⋙
        boundedConstructibleRationalClosedUpperShriek M I aX i j hij :=
  Recollement.rightAdjointIso (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
    (boundedConstructibleRationalClosedUpperShriekAdjunction M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aZ i τX τZ hi)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aU j τX τU hj)
    (fullyFaithfulBoundedConstructibleRationalRightDerivedLowerStar M aX i)
    (isZero_boundedConstructibleRationalUpperStar_obj_rightDerivedLowerStar_obj M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStar_essImage_of_isZero M aX i j hij)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): `Ri^!` carries
Frobenius structures, and the adjunction `i_* ⊣ Ri^!` on `Dᵇc(-, E)` lifts to objects with
Frobenius structure, with the original unit and counit: the adjunction, its unit and its counit
are Frobenius-equivariant. -/
noncomputable def boundedConstructibleRationalClosedUpperShriekIsoAlgebraAdjunction :
    IsoAlgebra.mapOfNatIso
        (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aZ i τX τZ hi) ⊣
      IsoAlgebra.mapOfNatIso (boundedConstructibleRationalClosedUpperShriekCommIso M I aX τX i j
        hij aZ aU τZ τU hi hj) :=
  Recollement.isoAlgebraAdjunction (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
    (boundedConstructibleRationalClosedUpperShriekAdjunction M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aZ i τX τZ hi)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aU j τX τU hj)
    (fullyFaithfulBoundedConstructibleRationalRightDerivedLowerStar M aX i)
    (isZero_boundedConstructibleRationalUpperStar_obj_rightDerivedLowerStar_obj M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStar_essImage_of_isZero M aX i j hij)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2` (Weil clause, stage `E`): for an object
`(K, θ : RτX_* K ≅ K)` of `Dᵇc(X, E)` with Frobenius structure, the closed-support triangle
`i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1]` is Frobenius-equivariant: the Frobenius
structures of its vertices (that of `K`, and those of `i_* Ri^! K` and `Rj_* j^* K` transported
along the lifted functors) form an isomorphism of triangles from its image under `RτX_*`. In
particular its third arrow is equivariant
(`CategoryTheory.Pretriangulated.Recollement.map_mor₃_comp_str`), by uniqueness of the third
arrow. -/
noncomputable def boundedConstructibleRationalClosedSupportTriangleIso
    (K : IsoAlgebra (boundedConstructibleRationalRightDerivedLowerStar M I aX τX)) {w}
    (hw : boundedConstructibleRationalClosedSupportTriangle M aX i j hij K.carrier w ∈
      distTriang _) :
    (boundedConstructibleRationalRightDerivedLowerStar M I aX τX).mapTriangle.obj
        (boundedConstructibleRationalClosedSupportTriangle M aX i j hij K.carrier w) ≅
      boundedConstructibleRationalClosedSupportTriangle M aX i j hij K.carrier w :=
  Recollement.mapTriangleIso (boundedConstructibleRationalUpperStarLowerStarAdjunction M aX j)
    (boundedConstructibleRationalClosedUpperShriekAdjunction M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStarCommIso M I aX aZ i τX τZ hi)
    (fullyFaithfulBoundedConstructibleRationalRightDerivedLowerStar M aX i)
    (isZero_boundedConstructibleRationalUpperStar_obj_rightDerivedLowerStar_obj M aX i j hij)
    (boundedConstructibleRationalRightDerivedLowerStar_essImage_of_isZero M aX i j hij)
    (mateEquiv_boundedConstructibleRationalUpperStarCommIso_inv M I aX τX i j hij aZ aU τZ τU hi hj)
    K hw

end ClosedSupport

end Etale

end AlgebraicGeometry
