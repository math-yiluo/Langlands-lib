/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap

/-!
# Finite-coefficient étale categories and functors for the ordinary Künneth formula

The definitions of the blueprint subsection `proposition-ordinary-external-kunneth--1` (section
`chap-Smooth-purity`) which only name categories and functors of the étale six-functor formalism
at a finite coefficient ring. The blueprint fixes the coefficient ring `𝒪_E/ϖⁿ` (a finite local
ring), or a finite field `𝔽_{ℓ^r}`; as in the rest of the repository the definitions are stated
for an arbitrary commutative coefficient ring `Λ : Type (u + 1)`, respectively an arbitrary
finite field `F : Type (u + 1)`, and are the existing functors of the repository specialised to
the coefficient category `ModuleCat Λ`, respectively `ModuleCat F`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryFiniteField` (`pur7710-def-finite-field-category`).
- `AlgebraicGeometry.Etale.leftDerivedUpperStarFiniteField`,
  `AlgebraicGeometry.Etale.derivedTensorFiniteField` (`pur7710-def-finite-field-functors`).
- `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsModule` (`pur7710-def-derived-sections`,
  étale case) and `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsFiniteField`
  (`pur7710-def-derived-sections-field`).
- `AlgebraicGeometry.Etale.constantComplexFunctor` (`pur7710-def-constant-complex`) and
  `AlgebraicGeometry.Etale.constantComplexFunctorFiniteField`
  (`pur7710-def-constant-complex-field`).
- `AlgebraicGeometry.Etale.exteriorProduct` (`prose-08-18`) and
  `AlgebraicGeometry.Etale.exteriorProductFiniteField` (`prose-08-18`).
- `AlgebraicGeometry.Etale.rightDerivedLowerStarModule` (`pur7710-def-unbounded-etale-push`).
- `AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_iff`
(`definition-cohomological-dimension--1`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme

/-- Blueprint `definition-cohomological-dimension--1`: torsion étale cohomological dimension.

The assertion `cd_tor(W) ≤ d` is the repository's
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE W d`: the étale cohomology
`H^q(W_ét, F)` vanishes for every torsion abelian sheaf `F` on `W_ét` (every local section
killed by a nonzero integer, `CategoryTheory.Sheaf.IsTorsion`) and every `q > d`. For a field
`K`, `cd_tor(K) ≤ d` is this assertion for `Spec K`. -/
theorem hasTorsionCohomologicalDimensionLE_iff (W : Scheme.{u}) (d : ℕ) :
    W.HasTorsionCohomologicalDimensionLE d ↔
      ∀ F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
        ∀ q : ℕ, d < q → Subsingleton (Sheaf.H F q) :=
  Iff.rfl

end Scheme

namespace Etale

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The constant complex functor `D(A) ⥤ D(W_ét, A)` for a coefficient category `A`: the functor
induced on derived categories by the exact constant sheaf functor `M ↦ M_W`. The constructions
of the ordinary Künneth morphism are carried out for such an `A` and then specialised to
`A = ModuleCat Λ`. -/
noncomputable abbrev derivedConstantSheaf (W : Scheme.{u}) :
    DerivedCategory A ⥤ DerivedCategory (Sheaf W.smallEtaleTopology A) :=
  (constantSheaf W.smallEtaleTopology A).mapDerivedCategory

/-- The tensor product `Lp^* K ⊗ᴸ Lq^* L ∈ D(Z_ét, A)` of the inverse images of
`K ∈ D(X_ét, A)` and `L ∈ D(Y_ét, A)` along morphisms `p : Z ⟶ X` and `q : Z ⟶ Y`, for a
coefficient category `A`; here `⊗ᴸ` is the tensor product of the monoidal category `D(Z_ét, A)`,
that is `AlgebraicGeometry.Etale.derivedTensor`. -/
noncomputable def derivedExteriorTensor {X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (L((p)^*[A])).obj K ⊗ (L((q)^*[A])).obj L

/-- The derived exterior product `K ⊠ᴸ L := Lp_X^* K ⊗ᴸ Lp_Y^* L ∈ D((X ×_S Y)_ét, A)` of
`K ∈ D(X_ét, A)` and `L ∈ D(Y_ét, A)`, for a coefficient category `A`, where `p_X`, `p_Y` are
the projections of `X ×_S Y` (`AlgebraicGeometry.Etale.derivedExteriorTensor`). -/
noncomputable abbrev derivedExteriorProduct {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    DerivedCategory (Sheaf (pullback f g).smallEtaleTopology A) :=
  derivedExteriorTensor A (pullback.fst f g) (pullback.snd f g) K L


end Coefficients

section Ring

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `pur7710-def-derived-sections` (étale case): derived sections at finite level.

For a scheme `W`, `RΓ_{W,ét,Λ} : D(W_ét, Λ) ⥤ D(Mod_Λ)` is the total right derived functor,
computed on K-injective resolutions, of the global sections functor `Γ(W_ét, -)` on étale sheaves
of `Λ`-modules (`AlgebraicGeometry.Etale.rightDerivedGlobalSections` for `A = ModuleCat Λ`);
its values keep their `Λ`-module structure. The blueprint takes `Λ = 𝒪_E/ϖⁿ`; the pro-étale
case is `AlgebraicGeometry.ProEtale.rightDerivedGlobalSectionsModule`. -/
noncomputable abbrev rightDerivedGlobalSectionsModule (W : Scheme.{u}) :
    DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W

/-- Blueprint `pur7710-def-constant-complex`: constant complexes of `Λ`-modules.

For a scheme `W`, `c_{W,Λ} = D((-)_W) : D(Mod_Λ) ⥤ D(W_ét, Λ)` is the functor induced on derived
categories by the exact constant sheaf functor `M ↦ M_W` (the sheafification of the constant
presheaf), `AlgebraicGeometry.Etale.derivedConstantSheaf` for `A = ModuleCat Λ` (it is also
the repository's `AlgebraicGeometry.Etale.constantFunctor`). The blueprint takes
`Λ = 𝒪_E/ϖⁿ`. -/
noncomputable abbrev constantComplexFunctor (W : Scheme.{u}) :
    DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
      DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  derivedConstantSheaf (ModuleCat.{u + 1} Λ) W

/-- `c_{W,Λ}` is the repository's constant complex functor. -/
lemma constantComplexFunctor_eq_constantFunctor (W : Scheme.{u}) :
    constantComplexFunctor Λ W = constantFunctor Λ W :=
  rfl

/-- Blueprint `pur7710-def-unbounded-etale-push`: unbounded étale direct image.

For a morphism `f : X ⟶ Y`, `Rf_{*,ét,Λ} : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` is the total right derived
functor, computed on K-injective resolutions, of the direct image `f_*` of étale sheaves of
`Λ`-modules, on the unbounded derived categories. The blueprint takes `Λ = 𝒪_E/ϖⁿ`. -/
noncomputable abbrev rightDerivedLowerStarModule {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  R((f)_*[ModuleCat.{u + 1} Λ])

/-- Blueprint `prose-08-18`: the derived exterior product at finite level.

For schemes `X`, `Y` over a base `S` (in the blueprint `S = Spec k`), with `Z = X ×_S Y` and
projections `p_X`, `p_Y`, and for `K ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`,
`K ⊠ᴸ_Λ L := Lp_X^* K ⊗ᴸ_Λ Lp_Y^* L ∈ D(Z_ét, Λ)`, with the derived inverse images of étale
sheaves of `Λ`-modules and their derived tensor product: the exterior product
`AlgebraicGeometry.Etale.derivedExteriorProduct` for `A = ModuleCat Λ`. -/
noncomputable abbrev exteriorProduct {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  derivedExteriorProduct (ModuleCat.{u + 1} Λ) f g K L

end Ring

section FiniteField

variable (F : Type (u + 1)) [Field F] [Finite F]

/-- Blueprint `pur7710-def-finite-field-category`: auxiliary finite-field categories.

For a finite field `F = 𝔽_{ℓ^r}` and a scheme `W`, `D(W_ét, F)` is the (unbounded) derived
category of the abelian category of étale sheaves of `F`-modules on `W`. The residue field
`𝒪_E/ϖ` is a particular case. -/
abbrev DerivedCategoryFiniteField (W : Scheme.{u}) : Type (u + 2) :=
  DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} F))

/-- Blueprint `pur7710-def-finite-field-functors`: functors with finite-field coefficients
(inverse image).

For a morphism `g : W ⟶ V`, `Lg^*_{ét,F} : D(V_ét, F) ⥤ D(W_ét, F)` is the left derived functor
of the (exact) inverse image of étale sheaves of `F`-modules. The derived tensor product is
`AlgebraicGeometry.Etale.derivedTensorFiniteField`. -/
noncomputable abbrev leftDerivedUpperStarFiniteField {W V : Scheme.{u}} (g : W ⟶ V) :
    DerivedCategoryFiniteField F V ⥤ DerivedCategoryFiniteField F W :=
  L((g)^*[ModuleCat.{u + 1} F])

/-- Blueprint `pur7710-def-finite-field-functors`: functors with finite-field coefficients
(derived tensor product).

For a scheme `W`, `- ⊗ᴸ_F - : D(W_ét, F) ⥤ D(W_ét, F) ⥤ D(W_ét, F)` is the two-variable total left
derived functor of the tensor product of étale sheaves of `F`-modules, computed on K-flat
resolutions. The inverse image is `AlgebraicGeometry.Etale.leftDerivedUpperStarFiniteField`. -/
noncomputable abbrev derivedTensorFiniteField (W : Scheme.{u}) :
    DerivedCategoryFiniteField F W ⥤ DerivedCategoryFiniteField F W ⥤
      DerivedCategoryFiniteField F W :=
  -⊗ᴸ-(W)[ModuleCat.{u + 1} F]

/-- Blueprint `pur7710-def-derived-sections-field`: derived sections with finite-field
coefficients.

For a scheme `W`, `RΓ_{W,ét,F} : D(W_ét, F) ⥤ D(Mod_F)` is the total right derived functor,
computed on K-injective resolutions, of the global sections of étale sheaves of `F`-modules, as
in `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsModule`. -/
noncomputable abbrev rightDerivedGlobalSectionsFiniteField (W : Scheme.{u}) :
    DerivedCategoryFiniteField F W ⥤ DerivedCategory (ModuleCat.{u + 1} F) :=
  rightDerivedGlobalSectionsModule F W

/-- Blueprint `pur7710-def-constant-complex-field`: constant complexes of `F`-vector spaces.

For a scheme `W`, `c_{W,F} : D(Mod_F) ⥤ D(W_ét, F)` is the levelwise functor of the exact
constant sheaf functor `M ↦ M_W` on `F`-modules, as in
`AlgebraicGeometry.Etale.constantComplexFunctor`. -/
noncomputable abbrev constantComplexFunctorFiniteField (W : Scheme.{u}) :
    DerivedCategory (ModuleCat.{u + 1} F) ⥤ DerivedCategoryFiniteField F W :=
  constantComplexFunctor F W

/-- Blueprint `prose-08-18`: the derived exterior product with
finite-field coefficients.

For `X`, `Y` over `S`, `Z = X ×_S Y`, `K ∈ D(X_ét, F)` and `L ∈ D(Y_ét, F)`,
`K ⊠ᴸ_F L := Lp_X^* K ⊗ᴸ_F Lp_Y^* L ∈ D(Z_ét, F)`, with the functors
`AlgebraicGeometry.Etale.leftDerivedUpperStarFiniteField` and
`AlgebraicGeometry.Etale.derivedTensorFiniteField`: the exterior product
`AlgebraicGeometry.Etale.exteriorProduct` at the coefficient ring `F`. -/
noncomputable abbrev exteriorProductFiniteField {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategoryFiniteField F X) (L : DerivedCategoryFiniteField F Y) :
    DerivedCategoryFiniteField F (pullback f g) :=
  exteriorProduct F f g K L

end FiniteField

end Etale

end AlgebraicGeometry
