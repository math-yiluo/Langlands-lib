/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Defs

/-!
# Constant complexes, the constant-tensor comparison and the Künneth morphism

For a commutative ring `Λ` (in the blueprint `Λ = 𝒪_E/ϖⁿ` or a finite field `𝔽_{ℓ^r}`) and a
scheme `W`, the constant complex functor `c_W : D(Mod_Λ) ⥤ D(W_ét, Λ)` is left adjoint to the
derived sections `RΓ_W` (`AlgebraicGeometry.Etale.constantComplexAdjunction`), and comes with a
monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N`
(`AlgebraicGeometry.Etale.constantComplexTensorComparison`), the derived comonoidal structure of
the exact monoidal constant sheaf functor. With these we define

- `AlgebraicGeometry.Etale.constantProjectionMap` (`pur7710-def-constant-projection`):
  `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)`;
- `AlgebraicGeometry.Etale.globalSectionsKunnethMap` (`definition-kunneth-map--1`) and
  `AlgebraicGeometry.Etale.globalSectionsKunnethMapFiniteField`
  (`definition-kunneth-map--1`): `RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ L)`.

## Implementation notes

All constructions are carried out for a general coefficient category `A` (with the hypotheses
under which the étale derived tensor product exists) and then specialised to `A = ModuleCat Λ`.
Building them directly at `ModuleCat Λ` makes the kernel compare instances of the monoidal
structure of the derived category found along different paths, which exhausts its time and
memory. For the same reason the constructions are split into small definitions with explicit
types, the composite morphisms only ever being composed along syntactically equal objects.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The inverse image of a constant étale sheaf is the constant sheaf, `g^* M_Y ≅ M_Z`, for
`A`-valued sheaves: both functors are left adjoint to taking global sections, since
`Γ(Y, g_* G) = G(Y ×_Y Z) = Γ(Z, G)`. -/
noncomputable def constantSheafCompUpperStarNatIso {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    constantSheaf Y.smallEtaleTopology A ⋙ (g)^*[A] ≅ constantSheaf Z.smallEtaleTopology A :=
  (((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).comp
    (upperStarLowerStarAdjunction _ g)).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))).leftAdjointUniq
    (constantSheafAdj _ _ (isTerminalOverPullbackObjMkId g))

/-- The inverse image of a constant complex is the constant complex, `Lg^* c_Y ≅ c_Z`: the
derived inverse image of the exact functor `g^*` is its levelwise functor, and the levelwise
functors compose. -/
noncomputable def derivedConstantSheafCompLeftDerivedUpperStarIso {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) :
    (constantSheaf Y.smallEtaleTopology A).mapDerivedCategory ⋙ L((g)^*[A]) ≅
      (constantSheaf Z.smallEtaleTopology A).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (constantSheafCompUpperStarNatIso A g)

/-- The adjunction `c_W ⊣ RΓ_W` between constant complexes and derived sections (blueprint
`pur7710-lem-constant-adjunction`) for `A`-valued sheaves: the derived adjunction of
`constantSheaf ⊣ Γ`, the total left derived functor of the exact constant sheaf functor being
identified with the levelwise functor. -/
noncomputable def derivedConstantSheafAdjunction (W : Scheme.{u}) :
    (constantSheaf W.smallEtaleTopology A).mapDerivedCategory ⊣
      rightDerivedGlobalSections A W :=
  (constantSheafΓAdj W.smallEtaleTopology A).derivedAdjunction.ofNatIsoLeft
    (constantSheaf W.smallEtaleTopology A).leftDerivedFunctorIsoMapDerivedCategory

/-- The counit `c_W RΓ_W K ⟶ K` of `c_W ⊣ RΓ_W`. -/
noncomputable def derivedConstantSheafCounit (W : Scheme.{u})
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj
        ((rightDerivedGlobalSections A W).obj K) ⟶ K :=
  (derivedConstantSheafAdjunction A W).counit.app K

/-- The transpose `M ⟶ RΓ_W K` under `c_W ⊣ RΓ_W` of a morphism `c_W M ⟶ K`. -/
noncomputable def derivedConstantSheafHomEquiv {W : Scheme.{u}} (M : DerivedCategory A)
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A))
    (φ : (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M ⟶ K) :
    M ⟶ (rightDerivedGlobalSections A W).obj K :=
  (derivedConstantSheafAdjunction A W).homEquiv M K φ

variable (W : Scheme.{u}) [(constantSheaf W.smallEtaleTopology A).PreservesFlat]

/-- The derived comonoidal structure `L((-)_W)(M ⊗ᴸ N) ⟶ L((-)_W) M ⊗ᴸ L((-)_W) N` of the
exact monoidal constant sheaf functor. -/
noncomputable def leftDerivedConstantSheafTensorComparison (M N : DerivedCategory A) :
    (constantSheaf W.smallEtaleTopology A).leftDerivedFunctor.obj (M ⊗ N) ⟶
      (constantSheaf W.smallEtaleTopology A).leftDerivedFunctor.obj M ⊗
        (constantSheaf W.smallEtaleTopology A).leftDerivedFunctor.obj N :=
  ((constantSheaf W.smallEtaleTopology A).leftDerivedTensorComparison.app M).app N

/-- The tensor product of the identifications `L((-)_W) ≅ c_W` at `M` and `N`. -/
noncomputable def leftDerivedConstantSheafTensorHom (M N : DerivedCategory A) :
    (constantSheaf W.smallEtaleTopology A).leftDerivedFunctor.obj M ⊗
        (constantSheaf W.smallEtaleTopology A).leftDerivedFunctor.obj N ⟶
      (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M ⊗
        (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj N :=
  (constantSheaf W.smallEtaleTopology A).leftDerivedFunctorIsoMapDerivedCategory.hom.app M ⊗ₘ
    (constantSheaf W.smallEtaleTopology A).leftDerivedFunctorIsoMapDerivedCategory.hom.app N

/-- The monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N` of constant complexes of objects of
`A` (blueprint `pur7710-lem-constant-monoidal`): the derived comonoidal structure
`CategoryTheory.Functor.leftDerivedTensorComparison` of the exact monoidal constant sheaf
functor, transported along `L((-)_W) ≅ c_W`. -/
noncomputable def derivedConstantSheafTensorComparison (M N : DerivedCategory A) :
    (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj (M ⊗ N) ⟶
      (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M ⊗
        (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj N :=
  (constantSheaf W.smallEtaleTopology A).leftDerivedFunctorIsoMapDerivedCategory.inv.app
      (M ⊗ N) ≫
    leftDerivedConstantSheafTensorComparison A W M N ≫ leftDerivedConstantSheafTensorHom A W M N

/-- The composite `c_W(RΓ_W K ⊗ᴸ M) ⟶ c_W RΓ_W K ⊗ᴸ c_W M ⟶ K ⊗ᴸ c_W M` of the monoidal
comparison and of `ε_K ⊗ 1`, the transpose of the constant-tensor comparison. -/
noncomputable def derivedConstantSheafProjectionMapTranspose
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A)) (M : DerivedCategory A) :
    (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj
        ((rightDerivedGlobalSections A W).obj K ⊗ M) ⟶
      K ⊗ (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M :=
  derivedConstantSheafTensorComparison A W ((rightDerivedGlobalSections A W).obj K) M ≫
    (derivedConstantSheafCounit A W K ▷
      (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M)

/-- The constant-tensor comparison `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` for `A`-valued sheaves:
the transpose under `c_W ⊣ RΓ_W` of
`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMapTranspose`. -/
noncomputable def derivedConstantSheafProjectionMap
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A)) (M : DerivedCategory A) :
    (rightDerivedGlobalSections A W).obj K ⊗ M ⟶
      (rightDerivedGlobalSections A W).obj
        (K ⊗ (constantSheaf W.smallEtaleTopology A).mapDerivedCategory.obj M) :=
  derivedConstantSheafHomEquiv A _ _ (derivedConstantSheafProjectionMapTranspose A W K M)

end Coefficients

section Kunneth

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [∀ W : Scheme.{u}, (constantSheaf W.smallEtaleTopology A).PreservesFlat]

/-- For `p : Z ⟶ X` and `K ∈ D(X_ét, A)`, the composite
`c_Z RΓ_X K ≅ Lp^* c_X RΓ_X K ⟶ Lp^* K` of the identification `Lp^* c_X ≅ c_Z` and of
`Lp^* ε_K`. -/
noncomputable def derivedConstantSheafCounitLeftDerivedUpperStar {X Z : Scheme.{u}}
    (p : Z ⟶ X) (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantSheaf Z.smallEtaleTopology A).mapDerivedCategory.obj
        ((rightDerivedGlobalSections A X).obj K) ⟶
      L((p)^*[A]).obj K :=
  (derivedConstantSheafCompLeftDerivedUpperStarIso A p).inv.app _ ≫
    L((p)^*[A]).map (derivedConstantSheafCounit A X K)

/-- For `p : Z ⟶ X`, `q : Z ⟶ Y`, `K ∈ D(X_ét, A)` and `L ∈ D(Y_ét, A)`, the composite
`c_Z(RΓ_X K ⊗ᴸ RΓ_Y L) ⟶ c_Z RΓ_X K ⊗ᴸ c_Z RΓ_Y L ⟶ Lp^* K ⊗ᴸ Lq^* L` of the monoidal
comparison of `c_Z` and of the tensor product of the morphisms
`AlgebraicGeometry.Etale.derivedConstantSheafCounitLeftDerivedUpperStar`. -/
noncomputable def derivedConstantSheafKunnethMapTranspose {X Y Z : Scheme.{u}} (p : Z ⟶ X)
    (q : Z ⟶ Y) (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (constantSheaf Z.smallEtaleTopology A).mapDerivedCategory.obj
        ((rightDerivedGlobalSections A X).obj K ⊗ (rightDerivedGlobalSections A Y).obj L) ⟶
      derivedExteriorTensor A p q K L :=
  derivedConstantSheafTensorComparison A Z ((rightDerivedGlobalSections A X).obj K)
      ((rightDerivedGlobalSections A Y).obj L) ≫
    (derivedConstantSheafCounitLeftDerivedUpperStar A p K ⊗ₘ
      derivedConstantSheafCounitLeftDerivedUpperStar A q L)

/-- The Künneth morphism `RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (Lp^* K ⊗ᴸ Lq^* L)` for `A`-valued sheaves,
`p : Z ⟶ X` and `q : Z ⟶ Y`: the transpose under `c_Z ⊣ RΓ_Z` of
`AlgebraicGeometry.Etale.derivedConstantSheafKunnethMapTranspose`. -/
noncomputable def derivedConstantSheafKunnethMap {X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗ (rightDerivedGlobalSections A Y).obj L ⟶
      (rightDerivedGlobalSections A Z).obj (derivedExteriorTensor A p q K L) :=
  derivedConstantSheafHomEquiv A _ _ (derivedConstantSheafKunnethMapTranspose A p q K L)

end Kunneth

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The constant sheaf functor on étale sheaves of `Λ`-modules preserves flat objects: the stalk
of `M_W` at every geometric point is `M`. -/
instance preservesFlat_constantSheaf (W : Scheme.{u}) :
    (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesFlat where
  flat_obj {M} hM := (flat_iff_forall_flat_sheafFiber_obj _).2 fun s ↦
    ObjectProperty.prop_of_iso _
      ((pointSmallEtale s).ulift.{u + 1}.sheafFiberConstantSheafIso M).symm hM

/-- The adjunction `c_W ⊣ RΓ_W` between constant complexes and derived sections (blueprint
`pur7710-lem-constant-adjunction`): the derived adjunction of `constantSheaf ⊣ Γ`, the total
left derived functor of the exact constant sheaf functor being identified with the levelwise
functor (`AlgebraicGeometry.Etale.derivedConstantSheafAdjunction` for `A = ModuleCat Λ`). -/
noncomputable def constantComplexAdjunction (W : Scheme.{u}) :
    constantComplexFunctor Λ W ⊣ rightDerivedGlobalSectionsModule Λ W :=
  derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) W

/-- The monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N` of constant complexes (blueprint
`pur7710-lem-constant-monoidal`): the derived comonoidal structure
`CategoryTheory.Functor.leftDerivedTensorComparison` of the exact monoidal constant sheaf
functor, transported along `L(constantSheaf) ≅ D(constantSheaf)`. It is an isomorphism. -/
noncomputable def constantComplexTensorComparison (W : Scheme.{u})
    (M N : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    (constantComplexFunctor Λ W).obj (M ⊗ N) ⟶
      ((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj ((constantComplexFunctor Λ W).obj M)).obj
        ((constantComplexFunctor Λ W).obj N) :=
  derivedConstantSheafTensorComparison (ModuleCat.{u + 1} Λ) W M N

/-- Blueprint `pur7710-def-constant-projection`: the constant-tensor comparison.

For a scheme `W`, `K ∈ D(W_ét, Λ)` and `M ∈ D(Mod_Λ)`, the morphism
`P_{W,K,M} : RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` corresponding under `c_W ⊣ RΓ_W`
(`AlgebraicGeometry.Etale.constantComplexAdjunction`) to the composite
`c_W(RΓ_W K ⊗ᴸ M) ⟶ c_W RΓ_W K ⊗ᴸ c_W M ⟶ K ⊗ᴸ c_W M` of the monoidal comparison
(`AlgebraicGeometry.Etale.constantComplexTensorComparison`) and of `ε_K ⊗ 1`
(`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMap` for `A = ModuleCat Λ`). Here `⊗ᴸ`
is the tensor product of the monoidal category `D(W_ét, Λ)`, that is
`AlgebraicGeometry.Etale.derivedTensor`. -/
noncomputable def constantProjectionMap (W : Scheme.{u})
    (K : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    (rightDerivedGlobalSectionsModule Λ W).obj K ⊗ M ⟶
      (rightDerivedGlobalSectionsModule Λ W).obj
        (((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj K).obj ((constantComplexFunctor Λ W).obj M)) :=
  derivedConstantSheafProjectionMap (ModuleCat.{u + 1} Λ) W K M

/-- Blueprint `definition-kunneth-map--1`: the ordinary Künneth morphism at finite level.

For schemes `X`, `Y` over `S` (in the blueprint `S = Spec k`), `Z = X ×_S Y` with projections
`p_X`, `p_Y`, and `K ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`, the morphism
`Kun_{K,L} : RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ L)` corresponding under `c_Z ⊣ RΓ_Z` to the composite
```
c_Z(RΓ_X K ⊗ᴸ RΓ_Y L) ⟶ c_Z RΓ_X K ⊗ᴸ c_Z RΓ_Y L
  ≅ Lp_X^* c_X RΓ_X K ⊗ᴸ Lp_Y^* c_Y RΓ_Y L ⟶ Lp_X^* K ⊗ᴸ Lp_Y^* L
```
of the monoidal comparison of `c_Z`, of the identifications `Lp^* c ≅ c`
(`AlgebraicGeometry.Etale.derivedConstantSheafCompLeftDerivedUpperStarIso`) and of
`Lp_X^* ε_K ⊗ Lp_Y^* ε_L` (`AlgebraicGeometry.Etale.derivedConstantSheafKunnethMap` for
`A = ModuleCat Λ` and the two projections). -/
noncomputable def globalSectionsKunnethMap {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSectionsModule Λ X).obj K ⊗ (rightDerivedGlobalSectionsModule Λ Y).obj L ⟶
      (rightDerivedGlobalSectionsModule Λ (pullback f g)).obj (exteriorProduct Λ f g K L) :=
  derivedConstantSheafKunnethMap (ModuleCat.{u + 1} Λ) (pullback.fst f g) (pullback.snd f g) K L

/-- Blueprint `definition-kunneth-map--1`: the ordinary Künneth morphism with finite-field
coefficients `F = 𝔽_{ℓ^r}`: the construction of
`AlgebraicGeometry.Etale.globalSectionsKunnethMap` with `F` in place of `Λ`,
`RΓ_X K ⊗ᴸ_F RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ_F L)`. -/
noncomputable abbrev globalSectionsKunnethMapFiniteField (F : Type (u + 1)) [Field F] [Finite F]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategoryFiniteField F X) (L : DerivedCategoryFiniteField F Y) :
    (rightDerivedGlobalSectionsFiniteField F X).obj K ⊗
        (rightDerivedGlobalSectionsFiniteField F Y).obj L ⟶
      (rightDerivedGlobalSectionsFiniteField F (pullback f g)).obj
        (exteriorProductFiniteField F f g K L) :=
  globalSectionsKunnethMap F f g K L

end Etale

end AlgebraicGeometry
