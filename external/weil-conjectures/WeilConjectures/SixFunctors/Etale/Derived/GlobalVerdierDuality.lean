/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# Global Verdier duality

Let `a_X : X ⟶ S` admit a compactification and satisfy the projection formula (for instance at
a finite coefficient ring). Global Verdier duality is the canonical isomorphism

`RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`,

natural in `K`: the inverse of the tensor–Hom exchange
`Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)` at `N = Λ_S`. This is blueprint
`theorem-global-verdier-duality--1` (in the étale setting, written in `D(S_ét)` with `Ra_{X!}` and
`Ra_{X*}`; over `S = Spec k` applying `RΓ(S, -)` gives the displayed form).

## Main definitions

- `AlgebraicGeometry.Etale.globalVerdierDualityNatIso`: `(Ra_{X!} -)^∨ ≅ Ra_{X*} 𝔻_X(-)`.
- `AlgebraicGeometry.Etale.globalVerdierDualityIso`: its component at `K`.
- `AlgebraicGeometry.Etale.globalVerdierDualityUnitIso`: the case `K = Λ_X`,
  `RΓ_c(X, Λ_X)^∨ ≅ RΓ(X, ω_X)`.

## Main statements

- `AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction_hom_naturality`: naturality in
  `K`.
- `AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction_inv_comp_mateEquiv`:
  compatibility with changes of coefficients (finite reduction, scalar extension) compatible
  with the projection map.

The construction uses only the tensor–Hom adjunction, the projection formula and the
adjunctions `La^* ⊣ Ra_*`, `Ra_! ⊣ Ra^!`; no properness and no global Poincaré duality.
-/

@[expose] public section

universe u' u'' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Adjunction

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X S : Scheme.{u}} {aX : X ⟶ S} [HasCompactification aX] [IsIso (projectionMap A aX)]
  {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : R(aX)_![A] ⊣ G)

/-- Global Verdier duality for an arbitrary right adjoint `G` of `Ra_{X!}` (for a finite
coefficient ring, `G = Ra_X^!`: `AlgebraicGeometry.Etale.globalVerdierDualityIso`): the inverse
`(Ra_{X!} K)^∨ ≅ Ra_{X*} RHom(K, G Λ_S)` of the tensor–Hom exchange
(`AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction`) at `N = Λ_S`. -/
noncomputable def globalVerdierDualityIsoOfAdjunction
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj K)) ≅
      (R((aX)_*[A])).obj (((RHom(X)[A]).flip.obj (G.obj (𝟙_ _))).obj (op K)) :=
  (((derivedHomLowerShriekIsoOfAdjunction A aX adj).app (op K)).app (𝟙_ _)).symm

omit [HasSmallSiteSheafify A] in
lemma globalVerdierDualityIsoOfAdjunction_eq
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    globalVerdierDualityIsoOfAdjunction A adj K =
      (((derivedHomLowerShriekIsoOfAdjunction A aX adj).app (op K)).app (𝟙_ _)).symm :=
  rfl

-- A proof by `rfl` (or by `simp`/`rw` closing with `rfl`) makes the kernel reduce the
-- projections of `derivedHomLowerShriekIsoOfAdjunction`, which times out.
omit [HasSmallSiteSheafify A] in
lemma globalVerdierDualityIsoOfAdjunction_inv
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (globalVerdierDualityIsoOfAdjunction A adj K).inv =
      ((derivedHomLowerShriekIsoOfAdjunction A aX adj).app (op K)).hom.app (𝟙_ _) :=
  (congrArg Iso.inv (globalVerdierDualityIsoOfAdjunction_eq A adj K)).trans
    ((Iso.symm_inv _).trans (Iso.app_hom _ _))

omit [HasSmallSiteSheafify A] in
lemma globalVerdierDualityIsoOfAdjunction_hom_naturality
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : K ⟶ K') :
    (DerivedCategory.coefficientDual A S).map ((R(aX)_![A]).map g).op ≫
        (globalVerdierDualityIsoOfAdjunction A adj K).hom =
      (globalVerdierDualityIsoOfAdjunction A adj K').hom ≫
        (R((aX)_*[A])).map (((RHom(X)[A]).flip.obj (G.obj (𝟙_ _))).map g.op) :=
  NatTrans.congr_app ((derivedHomLowerShriekIsoOfAdjunction A aX adj).inv.naturality g.op) (𝟙_ _)


/-- Global Verdier duality for an arbitrary right adjoint `G` of `Ra_{X!}`, natural form:
`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction` as a natural isomorphism
`(Ra_{X!} -)^∨ ≅ Ra_{X*} RHom(-, G Λ_S)` of functors `D(X_ét)ᵒᵖ ⥤ D(S_ét)`. -/
noncomputable def globalVerdierDualityNatIsoOfAdjunction :
    (R(aX)_![A]).op ⋙ DerivedCategory.coefficientDual A S ≅
      (RHom(X)[A]).flip.obj (G.obj (𝟙_ _)) ⋙ R((aX)_*[A]) :=
  NatIso.ofComponents (fun K ↦ globalVerdierDualityIsoOfAdjunction A adj K.unop)
    (fun g ↦ globalVerdierDualityIsoOfAdjunction_hom_naturality A adj g.unop)

/-- Global Verdier duality for an arbitrary right adjoint `G` of `Ra_{X!}`, the case
`K = Λ_X`: `RΓ_c(X, Λ_X)^∨ ≅ RΓ(X, G Λ_S)`, through `RHom(Λ_X, G Λ_S) ≅ G Λ_S`. -/
noncomputable def globalVerdierDualityUnitIsoOfAdjunction :
    (DerivedCategory.coefficientDual A S).obj (op ((R(aX)_![A]).obj (𝟙_ _))) ≅
      (R((aX)_*[A])).obj (G.obj (𝟙_ _)) :=
  globalVerdierDualityIsoOfAdjunction A adj (𝟙_ _) ≪≫
    (R((aX)_*[A])).mapIso (MonoidalClosed.unitNatIso.app (G.obj (𝟙_ _))).symm

section CoefficientChange

open TwoSquare

variable (A' : Type u'') [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]
  [IsIso (projectionMap A' aX)]

omit [HasSmallSiteSheafify A] in
/-- Blueprint `theorem-global-verdier-duality--1`: Global Verdier duality at the point,
compatibility with finite coefficient reduction and scalar extension.

A change of coefficients `A → A'` (the finite reduction `A_{E,n} → A_{E,m}`, or a scalar
extension) is given by functors `T_X`, `T_S` on the derived categories and comparison maps
`σ`, `μ`, `ρ`, `ν` for the left adjoints `La_X^*`, `K ⊗ᴸ -`, `Ra_{X!}` and `Ra_{X!} K ⊗ᴸ -`, as
in `AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv`; the
comparison maps of the right adjoints `Ra_{X*}`, `RHom(K, -)`, `G`, `G'` (right adjoints of
`Ra_{X!}` over `A` and `A'`, for finite coefficients `Ra_X^!`) and of the dual are their mates.
If the change of coefficients is compatible with the projection map, then the inverse of the
global Verdier-duality isomorphism is compatible with it: the square
```
T_S Ra_{X*} 𝔻_X K ------ T_S(iso⁻¹) -----> T_S (Ra_{X!} K)^∨
       |                                         |
       | comparison                              | comparison
       v                                         v
Ra_{X*} RHom(K', G' T_S Λ) ---- iso⁻¹ ----> RHom(Ra_{X!} K', T_S Λ)
```
commutes. Composing with a comparison `T_S Λ_S ⟶ Λ'_S` of the units (and the compatibility of
the dualizing complexes `T_X ω_X ≅ ω'_X` with the smooth orientation, blueprint
`proposition-compatibility-purity-change-coefficients`) gives the comparison with the duality over
`A'`. -/
theorem globalVerdierDualityIsoOfAdjunction_inv_comp_mateEquiv
    {G' : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A') ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A')}
    (adj' : R(aX)_![A'] ⊣ G')
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (TS : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S.smallEtaleTopology A'))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (σ : TwoSquare TS L((aX)^*[A]) L((aX)^*[A']) TX)
    (μ : TwoSquare TX ((-⊗ᴸ-(X)[A]).obj K) ((-⊗ᴸ-(X)[A']).obj K') TX)
    (ρ : TwoSquare TX R(aX)_![A] R(aX)_![A'] TS)
    (ν : TwoSquare TS ((-⊗ᴸ-(S)[A]).obj ((R(aX)_![A]).obj K))
      ((-⊗ᴸ-(S)[A']).obj ((R(aX)_![A']).obj K')) TS)
    (h : ν.whiskerLeft ((projectionMap A aX).app K) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A' aX).app K')) :
    TS.map (globalVerdierDualityIsoOfAdjunction A adj K).inv ≫
        (mateEquiv (derivedTensorHomAdjunction A ((R(aX)_![A]).obj K))
          (derivedTensorHomAdjunction A' ((R(aX)_![A']).obj K')) ν).app (𝟙_ _) =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A aX)
          (derivedUpperStarLowerStarAdjunction A' aX) σ).app _ ≫
        R((aX)_*[A']).map ((mateEquiv (derivedTensorHomAdjunction A K)
          (derivedTensorHomAdjunction A' K') μ).app _) ≫
        R((aX)_*[A']).map (((RHom(X)[A']).obj (op K')).map
          ((mateEquiv adj adj' ρ).app (𝟙_ _))) ≫
        ((derivedHomLowerShriekIsoOfAdjunction A' aX adj').app (op K')).hom.app
          (TS.obj (𝟙_ _)) := by
  rw [globalVerdierDualityIsoOfAdjunction_inv]
  exact derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv A aX A' adj adj' TX TS K K'
    σ μ ρ ν h (𝟙_ _)

end CoefficientChange

end Adjunction

section General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S : Scheme.{u}} (aX : X ⟶ S) [HasCompactification aX]
  [IsIso (projectionMap (ModuleCat.{u + 1} Λ) aX)]

/-- Blueprint `theorem-global-verdier-duality--1`: Global Verdier duality at the point.

For `a_X : X ⟶ S` admitting a compactification and satisfying the projection formula (which
holds at every finite coefficient ring, `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`),
the canonical isomorphism `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)`, written in `D(S_ét)` as
`(Ra_{X!} K)^∨ ≅ Ra_{X*}(𝔻_X K)`. It is the inverse of the tensor–Hom exchange
`Ra_{X*} RHom(K, Ra_X^! N) ≅ RHom(Ra_{X!} K, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`, built from the adjunctions and
the projection formula only) at `N = Λ_S`. Its inverse, its naturality in `K` and its
compatibility with changes of coefficients are those of
`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction` for `Ra_{X!} ⊣ Ra_X^!`
(`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction_inv`,
`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction_hom_naturality`,
`AlgebraicGeometry.Etale.globalVerdierDualityIsoOfAdjunction_inv_comp_mateEquiv`); restating
these at `ModuleCat Λ` makes the kernel compare the two elaborations of the monoidal structures,
which does not finish in reasonable time. -/
noncomputable def globalVerdierDualityIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aX).obj (op K)) :=
  globalVerdierDualityIsoOfAdjunction (ModuleCat.{u + 1} Λ)
    (rightDerivedUpperShriekAdjunction Λ aX) K

lemma globalVerdierDualityIso_eq
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    globalVerdierDualityIso Λ aX K =
      (((derivedHomRightDerivedLowerShriekIso Λ aX).app (op K)).app (𝟙_ _)).symm :=
  rfl

/-- Blueprint `theorem-global-verdier-duality--1`: Global Verdier duality at the point, natural
form: `AlgebraicGeometry.Etale.globalVerdierDualityIso` as a natural isomorphism
`(Ra_{X!} -)^∨ ≅ Ra_{X*} 𝔻_X(-)` of functors `D(X_ét)ᵒᵖ ⥤ D(S_ét)`. -/
noncomputable def globalVerdierDualityNatIso :
    (R(aX)_![ModuleCat.{u + 1} Λ]).op ⋙ DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S ≅
      verdierDual Λ aX ⋙ R((aX)_*[ModuleCat.{u + 1} Λ]) :=
  globalVerdierDualityNatIsoOfAdjunction (ModuleCat.{u + 1} Λ)
    (rightDerivedUpperShriekAdjunction Λ aX)

/-- Blueprint `theorem-global-verdier-duality--1`: Global Verdier duality at the point, the case
`K = Λ_X`.

At `K = Λ_X` global Verdier duality identifies `RΓ_c(X, Λ_X)^∨` with `RΓ(X, ω_X)`: it is
`AlgebraicGeometry.Etale.globalVerdierDualityIso` followed by `𝔻_X Λ_X = RHom(Λ_X, ω_X) ≅ ω_X`,
the evaluation at the unit object. -/
noncomputable def globalVerdierDualityUnitIso :
    (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) S).obj
        (op ((R(aX)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) ≅
      (R((aX)_*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ aX) :=
  globalVerdierDualityUnitIsoOfAdjunction (ModuleCat.{u + 1} Λ)
    (rightDerivedUpperShriekAdjunction Λ aX)

end General

end Etale

end AlgebraicGeometry
