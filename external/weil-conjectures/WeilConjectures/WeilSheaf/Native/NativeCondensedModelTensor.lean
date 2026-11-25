/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficients
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.WeilSheaf.Native.NativeMapModLaxTensor

/-!
# The condensed model of `ℓ`-adic sheaves is monoidal

The equivalence `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod` between `ℓ`-adic sheaves
on `X` (module objects over `ℚ̄_ℓ,X` in sheaves of `ℚ̄_ℓ`-modules) and module objects over the
condensed coefficient ring `p_X^* ℚ̄_ℓ` in abelian sheaves is compatible with the relative
tensor products. The comparison
```
Φ M ⊗_{p_X^* ℚ̄_ℓ} Φ N ≅ Φ (M ⊗_{ℚ̄_ℓ,X} N)
```
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModTensorIso`) is explicit: on the projection
`M ⊗ N ⟶ M ⊗_{ℚ̄_ℓ,X} N` it is the lax monoidal structure of the forgetful functor from sheaves of
`ℚ̄_ℓ`-modules to abelian sheaves followed by the image of the projection
(`AlgebraicGeometry.ProEtale.tensorObjπ_adicSheafEquivCondensedModTensorIso_hom_hom`).

It is the comparison `CategoryTheory.Functor.mapModLaxTensorHom` of the forgetful functor, an
isomorphism since forgetting is right adjoint to the free functor by a monoidal adjunction and
induces an equivalence on module objects (`CategoryTheory.Functor.isIso_mapModLaxTensorHom`),
followed by restriction of scalars along the coefficient ring isomorphism (`Mod.comapTensorIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The tensor comparison of the forgetful functor from `ℓ`-adic sheaves to module objects in
abelian sheaves is an isomorphism. -/
instance isIso_forgetAb_mapModLaxTensorHom (M N : AdicSheaf l X) :
    IsIso ((weilCoefficientsForgetAb l X).mapModLaxTensorHom M N) :=
  let a := Sheaf.extendScalarsAbAdjunction (Scheme.ProEt.topology X)
    (ULift.{u + 1} (PadicAlgCl l))
  have := a.isLeftAdjoint
  Functor.isIso_mapModLaxTensorHom (adicConstantSheaf l X) a M N

/-- The monoidal comparison `Φ M ⊗ Φ N ≅ Φ (M ⊗ N)` of the condensed model
`Φ = adicSheafEquivCondensedMod l X` of `ℓ`-adic sheaves. -/
noncomputable def adicSheafEquivCondensedModTensorIso (M N : AdicSheaf l X) :
    (adicSheafEquivCondensedMod l X).functor.obj M ⊗
        (adicSheafEquivCondensedMod l X).functor.obj N ≅
      (adicSheafEquivCondensedMod l X).functor.obj (M ⊗ N) :=
  (weilCoefficientsForgetAb l X).mapModComapTensorIso (condensedRingObjIsoForgetAb l X).hom M N

/-- On the projection onto the relative tensor product, the monoidal comparison of the condensed
model is the lax monoidal structure of the forgetful functor followed by the image of the
projection `M ⊗ N ⟶ M ⊗_{ℚ̄_ℓ,X} N`. -/
@[reassoc (attr := simp)]
lemma tensorObjπ_adicSheafEquivCondensedModTensorIso_hom_hom (M N : AdicSheaf l X) :
    Mod.tensorObjπ ((adicSheafEquivCondensedMod l X).functor.obj M)
        ((adicSheafEquivCondensedMod l X).functor.obj N) ≫
      (adicSheafEquivCondensedModTensorIso l X M N).hom.hom =
    Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l X) M.X N.X ≫
      (weilCoefficientsForgetAb l X).map (Mod.tensorObjπ M N) :=
  (weilCoefficientsForgetAb l X).tensorObjπ_mapModComapTensorIso_hom_hom _ M N

/-- The monoidal comparison of the condensed model is natural in both factors. -/
@[reassoc]
lemma adicSheafEquivCondensedModTensorIso_hom_natural {M M' N N' : AdicSheaf l X}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((adicSheafEquivCondensedMod l X).functor.map f ⊗ₘ
        (adicSheafEquivCondensedMod l X).functor.map g) ≫
      (adicSheafEquivCondensedModTensorIso l X M' N').hom =
    (adicSheafEquivCondensedModTensorIso l X M N).hom ≫
      (adicSheafEquivCondensedMod l X).functor.map (f ⊗ₘ g) :=
  (weilCoefficientsForgetAb l X).mapModComapTensorIso_hom_natural _ f g

end AlgebraicGeometry.ProEtale
