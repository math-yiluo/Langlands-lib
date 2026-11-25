/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFiberFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.PullbackComparison
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex

/-!
# Comparison of the scheme and the Galois Frobenius pullbacks

Let `k = 𝔽_q` be a finite field, `X₀` a scheme over `k` with structure morphism
`f : X₀ ⟶ Spec k` and `X = X₀ ×_k k̄` its geometric fibre. The scheme Frobenius
`Φ_X = Φ₀ × 𝟙` (`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius`) and the geometric Galois
Frobenius `g_X = 𝟙 × Spec γ` (`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`) differ by
the absolute `q`-power Frobenius: `Fr_X^{(q)} = Φ_X ≫ g_X⁻¹`
(`AlgebraicGeometry.Scheme.Hom.iterateFrobenius_geometricFiber_eq`). Since the absolute
Frobenius acts as the identity on the étale topos
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`), the derived pullbacks along
`Φ_X` and `g_X` are canonically isomorphic,
```
κ_X : LΦ_X^* ≅ Lg_X^*
```
(`AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIso`, blueprints
`lemma-scheme-frobenius-geometric-frobenius--1` and `sec-Weil-complexes`), and the
comparison isomorphisms are compatible with pullback along the base change `f : X ⟶ Y` of a
morphism `f₀ : X₀ ⟶ Y₀` over `k`: `Lf^* κ_Y = κ_X Lf^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_leftDerivedUpperStarGeometricFiberFrobeniusIso`).

The *scheme-Frobenius form* of a strict geometric-Weil datum `φ_K : Lg_Y^* K ≅ K` is
`u_K = φ_K ∘ κ_{Y,K} : LΦ_Y^* K ⟶ K` (`AlgebraicGeometry.Etale.schemeFrobeniusForm`, blueprint
`definition-weil-structure--1`).
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

namespace Etale

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The absolute `q`-power Frobenius of the geometric fibre, followed by the geometric Galois
Frobenius, is the scheme Frobenius: `Fr_X^{(q)} ≫ g_X = Φ_X`. -/
lemma iterateFrobenius_geometricFiber_comp_geometricGaloisFrobenius_hom :
    f.geometricFiber.iterateFrobenius (FiniteField.ringChar_prime k)
        f.isOfCharacteristic_geometricFiber (FiniteField.frobeniusExponent k) ≫
      f.geometricGaloisFrobenius.asIso.hom = f.geometricFiberFrobenius := by
  rw [Scheme.Hom.iterateFrobenius_geometricFiber_eq, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Blueprint `sec-Weil-complexes`: Scheme and geometric Frobenius of the purity
datum (the comparison isomorphism `κ_X`, blueprint `lemma-scheme-frobenius-geometric-frobenius--1`).

The comparison `κ_X : LΦ_X^* ≅ Lg_X^*` between the derived pullbacks along the scheme Frobenius
`Φ_X` and along the geometric Galois Frobenius `g_X = g_{X,γ}` of the geometric fibre `X`: the
two differ by the absolute `q`-power Frobenius, `Φ_X = Fr_X^{(q)} ≫ g_X`, which acts as the
identity on the étale topos (`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`),
and `κ_X` is the composite
`LΦ_X^* ≅ Lg_X^* ⋙ L(Fr_X^{(q)})^* ≅ Lg_X^* ⋙ L(𝟙)^* ≅ Lg_X^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoOfFactor`). -/
noncomputable def leftDerivedUpperStarGeometricFiberFrobeniusIso :
    L((f.geometricFiberFrobenius)^*[A]) ≅ L((f.geometricGaloisFrobenius.asIso.hom)^*[A]) :=
  leftDerivedUpperStarIsoOfFactor A
    (iterateFrobenius_geometricFiber_comp_geometricGaloisFrobenius_hom f)
    (leftDerivedUpperStarIterateFrobeniusIso A (FiniteField.ringChar_prime k)
      f.isOfCharacteristic_geometricFiber (FiniteField.frobeniusExponent k))

variable {Y₀ : Scheme.{u}} {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- Blueprint `sec-Weil-complexes`: Scheme and geometric Frobenius of the purity
datum (compatibility `Lf^* κ_Y = κ_X Lf^*`).

The comparison isomorphisms `κ` are compatible with pullback along the base change
`φ̄ = φ × 𝟙 : X ⟶ Y` of a morphism `φ : X₀ ⟶ Y₀` over `k`: the square
```
Lφ̄^* LΦ_Y^* K ──Lφ̄^* κ_Y──▶ Lφ̄^* Lg_Y^* K
      │ ≅                         │ ≅
      ▼                           ▼
LΦ_X^* Lφ̄^* K ─────κ_X─────▶ Lg_X^* Lφ̄^* K
```
commutes, the vertical arrows being the identifications of the derived pullbacks along
`Φ_X ≫ φ̄ = φ̄ ≫ Φ_Y` and `g_X ≫ φ̄ = φ̄ ≫ g_Y`. -/
theorem leftDerivedUpperStar_map_leftDerivedUpperStarGeometricFiberFrobeniusIso
    (K : _root_.DerivedCategory (Sheaf g.geometricFiber.smallEtaleTopology A)) :
    L((Hom.geometricFiberMap φ h)^*[A]).map
        ((leftDerivedUpperStarGeometricFiberFrobeniusIso A g).hom.app K) ≫
        (leftDerivedUpperStarComp A (Hom.geometricFiberMap φ h) g.geometricGaloisFrobenius.asIso.hom
          (f.geometricGaloisFrobenius.asIso.hom ≫ Hom.geometricFiberMap φ h)
          (Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).inv.app K ≫
          (leftDerivedUpperStarComp A f.geometricGaloisFrobenius.asIso.hom
            (Hom.geometricFiberMap φ h) _ rfl).hom.app K =
      (leftDerivedUpperStarComp A (Hom.geometricFiberMap φ h) g.geometricFiberFrobenius
          (f.geometricFiberFrobenius ≫ Hom.geometricFiberMap φ h)
          (Hom.geometricFiberMap_comp_geometricFiberFrobenius φ h).symm).inv.app K ≫
        (leftDerivedUpperStarComp A f.geometricFiberFrobenius (Hom.geometricFiberMap φ h) _
          rfl).hom.app K ≫
          (leftDerivedUpperStarGeometricFiberFrobeniusIso A f).hom.app
            (L((Hom.geometricFiberMap φ h)^*[A]).obj K) :=
  leftDerivedUpperStar_map_leftDerivedUpperStarIsoOfFactor A (Hom.geometricFiberMap φ h)
    (iterateFrobenius_geometricFiber_comp_geometricGaloisFrobenius_hom f) _
    (iterateFrobenius_geometricFiber_comp_geometricGaloisFrobenius_hom g) _
    (Hom.geometricFiberMap_comp_geometricFiberFrobenius φ h).symm
    (Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm
    (comp_iterateFrobenius _ _ _ _ _).symm
    (leftDerivedUpperStarIterateFrobeniusIso_naturality_app A _ _ _ _ _ _) K

section SchemeFrobeniusForm

/-- Blueprint `definition-weil-structure--1`: Strict Weil data and the Tate datum (scheme-Frobenius
form).

The *scheme-Frobenius form* `u_K = φ_K ∘ κ_{Y,K} : LΦ_Y^* K ≅ K` of a strict geometric-Weil datum
`φ_K : Lg_Y^* K ≅ K` on the geometric fibre `Y` of `g : Y₀ ⟶ Spec k`, `κ_Y` being the comparison
`LΦ_Y^* ≅ Lg_Y^*` of the scheme Frobenius with the geometric Galois Frobenius
(`AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIso`). -/
noncomputable def schemeFrobeniusForm
    {K : _root_.DerivedCategory (Sheaf g.geometricFiber.smallEtaleTopology A)}
    (φK : L((g.geometricGaloisFrobenius.asIso.hom)^*[A]).obj K ≅ K) :
    L((g.geometricFiberFrobenius)^*[A]).obj K ≅ K :=
  (leftDerivedUpperStarGeometricFiberFrobeniusIso A g).app K ≪≫ φK

lemma schemeFrobeniusForm_hom
    {K : _root_.DerivedCategory (Sheaf g.geometricFiber.smallEtaleTopology A)}
    (φK : L((g.geometricGaloisFrobenius.asIso.hom)^*[A]).obj K ≅ K) :
    (schemeFrobeniusForm A φK).hom =
      (leftDerivedUpperStarGeometricFiberFrobeniusIso A g).hom.app K ≫ φK.hom :=
  rfl

/-- The scheme-Frobenius forms are natural: a morphism `h : K ⟶ L` compatible with strict
geometric-Weil data `φ_K`, `φ_L` is compatible with their scheme-Frobenius forms `u_K`, `u_L`. -/
lemma map_comp_schemeFrobeniusForm_hom
    {K L : _root_.DerivedCategory (Sheaf g.geometricFiber.smallEtaleTopology A)}
    (φK : L((g.geometricGaloisFrobenius.asIso.hom)^*[A]).obj K ≅ K)
    (φL : L((g.geometricGaloisFrobenius.asIso.hom)^*[A]).obj L ≅ L) (h : K ⟶ L)
    (hh : L((g.geometricGaloisFrobenius.asIso.hom)^*[A]).map h ≫ φL.hom = φK.hom ≫ h) :
    L((g.geometricFiberFrobenius)^*[A]).map h ≫ (schemeFrobeniusForm A φL).hom =
      (schemeFrobeniusForm A φK).hom ≫ h := by
  rw [schemeFrobeniusForm_hom, schemeFrobeniusForm_hom, Category.assoc, ← hh,
    NatTrans.naturality_assoc]

end SchemeFrobeniusForm

end Etale

end AlgebraicGeometry
