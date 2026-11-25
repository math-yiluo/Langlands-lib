/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusOpenSquare
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural

/-!
# Coefficient independent scheme Frobenius geometry

Source: latest blueprint, sec-Weil-complexes, the explicit factorization
and the two commuting squares (blueprint: sec-Weil-complexes).
The original finite coefficient comparison remains publicly imported. These interfaces
expose its scheme data without requiring an unrelated finite coefficient setting.

## Main definitions

- `purityFrobeniusFiber`, `purityFrobeniusMap`: the existing geometric base change.
- `purityGaloisMap`, `puritySchemeFrobenius`, `purityAbsoluteFrobenius`: its scheme maps.

## Main statements

- `purityFrobenius_geometry`: factorization and both commuting squares.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteFieldDatum

/-- The existing scalar extension, for an arbitrary model over the finite base.
Source: explicit base change (blueprint: sec-Weil-complexes). -/
abbrev purityFrobeniusFiber (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀

/-- The existing base change on model morphisms, without a coefficient parameter.
Source: the two squares (blueprint: sec-Weil-complexes). -/
abbrev purityFrobeniusMap (D : FiniteFieldDatum.{u})
    {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))} (h₀ : S₀ ⟶ T₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left

/-- The existing semilinear geometric Galois map, independently of coefficients.
Source: geometric Galois automorphisms (blueprint: sec-Weil-complexes). -/
abbrev purityGaloisMap (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :=
  D.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
      (Fintype.ofFinite D.k₀) _ _ _)

/-- The base change of the model's absolute q-power Frobenius.
Source: definition of Phi (blueprint: sec-Weil-complexes). -/
def puritySchemeFrobenius (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    (D.purityFrobeniusFiber T₀).left ⟶ (D.purityFrobeniusFiber T₀).left :=
  D.purityFrobeniusMap (Over.homMk
    (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
    (D.model_frobenius_over T₀.hom))

/-- Absolute q-power Frobenius on the geometric fibre, with its canonical characteristic
proof from the model structure map. Source: absolute factor
(blueprint: sec-Weil-complexes). -/
def purityAbsoluteFrobenius (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    (D.purityFrobeniusFiber T₀).left ⟶ (D.purityFrobeniusFiber T₀).left :=
  (D.purityFrobeniusFiber T₀).left.iterateFrobenius D.prime
    (D.model_characteristic (pullback.fst T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ T₀.hom)) D.a

/-- The coefficient independent factorization and the two commuting scheme squares.
There is no Cartesian hypothesis on the scheme Frobenius square.
Source: explicit factorization and the displayed squares
(blueprint: sec-Weil-complexes).

Proof: on a base changed affine chart, absolute Frobenius sends b tensor c to
b^q tensor c^q. The arithmetic Galois map sends b tensor c to b tensor c^q,
and Phi sends it to b^q tensor c. Their two composites are equal to absolute
Frobenius. Cancel the inverse arithmetic action to obtain the geometric
factorization. Projection uniqueness glues the calculation on arbitrary models.
For a model morphism, preservation of qth powers gives the Phi square, and
projection uniqueness gives the Galois square. These are the identical geometric
calculations of schemeGeometricFrobenius_factorization and its square theorem;
no finite coefficient ring, absolute finite type or smoothness enters them. -/
theorem purityFrobenius_geometry (D : FiniteFieldDatum.{u}) :
    (∀ T₀ : Over (Spec (CommRingCat.of D.k₀)),
      D.puritySchemeFrobenius T₀ =
        D.purityAbsoluteFrobenius T₀ ≫ D.purityGaloisMap T₀) ∧
    (∀ {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))} (h₀ : S₀ ⟶ T₀),
      D.purityFrobeniusMap h₀ ≫ D.puritySchemeFrobenius T₀ =
          D.puritySchemeFrobenius S₀ ≫ D.purityFrobeniusMap h₀ ∧
      D.purityFrobeniusMap h₀ ≫ D.purityGaloisMap T₀ =
          D.purityGaloisMap S₀ ≫ D.purityFrobeniusMap h₀) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have absolute_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
      {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
      (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
      X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
    apply Scheme.Hom.ext (by ext x; rfl)
    intro U
    simp only [Scheme.Hom.comp_app]
    change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
      X.presheaf.map (𝟙 _) =
        (Y.iterateFrobenius hp hY n).app U ≫ f.app U
    rw [X.presheaf.map_id, Category.comp_id]
    ext s
    exact (map_pow (f.app U).hom s _).symm
  constructor
  · intro T₀
    let π := pullback.fst T₀.hom b
    let ρ := pullback.snd T₀.hom b
    have hA := D.galoisMap_projections T₀.hom σ.symm
    have hS₁ : D.puritySchemeFrobenius T₀ ≫ π = π ≫
        T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a := by
      simp [puritySchemeFrobenius, purityFrobeniusMap, π, b, Over.pullback_map_left]
    have hS₂ : D.puritySchemeFrobenius T₀ ≫ ρ = ρ := by
      simp [puritySchemeFrobenius, purityFrobeniusMap, ρ, b, Over.pullback_map_left]
    have hF₁ : D.purityAbsoluteFrobenius T₀ ≫ π = π ≫
        T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a :=
      absolute_naturality π _ _ _ _
    have hF₂ : D.purityAbsoluteFrobenius T₀ ≫ ρ =
        ρ ≫ Spec.map (CommRingCat.ofHom σ.symm.toRingHom) := by
      apply AlgebraicGeometry.ext_to_Spec
      change (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
          (D.purityAbsoluteFrobenius T₀ ≫ ρ).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
          (ρ ≫ Spec.map (CommRingCat.ofHom σ.symm.toRingHom)).appTop
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      conv_rhs => rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
      ext x
      change (ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv x)) ^
          D.p ^ D.a =
        ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv (σ.symm x))
      have hx : σ.symm x = x ^ (D.p ^ D.a) := by
        change x ^ Fintype.card D.k₀ = _
        rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq]
      rw [hx, map_pow, map_pow]
    have h₂ : D.purityAbsoluteFrobenius T₀ =
        D.puritySchemeFrobenius T₀ ≫ D.galoisMap T₀.hom σ.symm := by
      apply pullback.hom_ext
      · change _ ≫ π = (_ ≫ _) ≫ π
        rw [hF₁, Category.assoc, hA.1, hS₁]
      · change _ ≫ ρ = (_ ≫ _) ≫ ρ
        rw [hF₂, Category.assoc, hA.2, ← Category.assoc, hS₂]
    rw [h₂, Category.assoc, (D.galoisMap_inverse T₀.hom σ).2]
    exact (Category.comp_id (D.puritySchemeFrobenius T₀)).symm
  · intro S₀ T₀ h₀
    constructor
    · have h :
          Over.homMk
            (S₀.left.iterateFrobenius D.prime (D.model_characteristic S₀.hom) D.a)
            (D.model_frobenius_over S₀.hom) ≫ h₀ =
          h₀ ≫ Over.homMk
            (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
            (D.model_frobenius_over T₀.hom) := by
        apply Over.OverMorphism.ext
        exact absolute_naturality h₀.left D.prime
          (D.model_characteristic S₀.hom) (D.model_characteristic T₀.hom) D.a
      have h' := congrArg (fun g ↦ ((Over.pullback b).map g).left) h
      change (((Over.pullback b).map h₀).left ≫
          ((Over.pullback b).map (Over.homMk
            (T₀.left.iterateFrobenius D.prime (D.model_characteristic T₀.hom) D.a)
            (D.model_frobenius_over T₀.hom))).left) =
        (((Over.pullback b).map (Over.homMk
            (S₀.left.iterateFrobenius D.prime (D.model_characteristic S₀.hom) D.a)
            (D.model_frobenius_over S₀.hom))).left ≫
          ((Over.pullback b).map h₀).left)
      simpa only [Functor.map_comp, Over.comp_left] using h'.symm
    · exact (D.frobenius_square_cartesian S₀ T₀ h₀).2.2.2.2.1.symm

end WeilConjectures.FiniteFieldDatum
