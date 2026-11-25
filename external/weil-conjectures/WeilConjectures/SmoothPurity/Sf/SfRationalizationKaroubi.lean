/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated

public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
/-! # Rationalization of the intrinsic integral constructible category

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460; current main snapshot, sec-proetale-coefficients/sk-def-sf-operations,
order 1819 (blueprint: def-weil-rationalization-karoubi).

Specialize the existing raw scalar localization to `sfIntegralConstructibleCategory`.
Its objects are unchanged and its Hom groups are tensor products with the localized
coefficient ring, canonically identified with E. No idempotents are adjoined.
The global finite-field datum only restricts the coefficient prime: it imposes no
structure morphism or finite-type condition on Y. The intrinsic category therefore
omits that unused datum; the scalar transition accepts its characteristic p and l ≠ p.
The legacy declarations are preserved by the public import.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d u

open CategoryTheory TensorProduct

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The raw rationalized category, without idempotent completion.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable abbrev sfRationalConstructibleCategory (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  ScalarLocalization (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E Y)
    (Padic.coefficientExtensionUniformizer l E)

set_option linter.defProp false in
/-- The recorded raw scalar-localization theorem supplies precisely the induced shift
and image triangles, with exact localization and no new objects.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def sfRationalTriangulationDatum :=
  ScalarLocalization.exists_triangulated_scalarLocalization
    (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E Y)
    (Padic.coefficientExtensionUniformizer l E)

/-- The zero object in raw rationalization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalConstructibleZero :
    CategoryTheory.Limits.HasZeroObject (sfRationalConstructibleCategory l E Y) :=
  (sfRationalTriangulationDatum l E Y).choose

/-- The induced shift, with the tensor-Hom shift specified by the triangulation datum.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalConstructibleShift :
    HasShift (sfRationalConstructibleCategory l E Y) ℤ :=
  (sfRationalTriangulationDatum l E Y).choose_spec.choose

/-- Additivity of every induced rational shift.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalConstructibleShiftAdditive (n : ℤ) :
    (shiftFunctor (sfRationalConstructibleCategory l E Y) n).Additive :=
  (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2.choose n

/-- The canonical integral-to-rational functor is the identity on objects and tensors
morphisms with one. Source: blueprint order 1460
(blueprint: def-weil-rationalization-karoubi). -/
noncomputable def sfRationalConstructibleLocalization :
    sfIntegralConstructibleCategory l E Y ⥤
      sfRationalConstructibleCategory l E Y :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E Y)
    (Padic.coefficientExtensionUniformizer l E)

/-- The canonical shift comparison for localization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalLocalizationCommShift :
    (sfRationalConstructibleLocalization l E Y).CommShift ℤ :=
  (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2.choose_spec.choose

/-- The image-triangle pretriangulation of the raw localized category.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalConstructiblePretriangulated :
    Pretriangulated (sfRationalConstructibleCategory l E Y) :=
  (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2.choose

/-- Triangulation for exactly the image triangles.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalConstructibleTriangulated :
    IsTriangulated (sfRationalConstructibleCategory l E Y) :=
  (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
    |>.choose_spec.1

/-- Exactness of the integral-to-rational functor for the specified image triangles.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalLocalizationTriangulated :
    (sfRationalConstructibleLocalization l E Y).IsTriangulated :=
  (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
    |>.choose_spec.2.1

/-- The canonical localized coefficient field identification, fixed on fractions.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def sfRationalCoefficientEquiv :
    Localization.Away (Padic.coefficientExtensionUniformizer l E) ≃ₐ[
      Padic.coefficientExtensionIntegers l E] E :=
  (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose

/-- The actual Hom group in the intrinsic rational stage, in the source's Hom-first
coordinates. Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: commute the tensor factors and apply the canonical coefficient-field equivalence
`sfRationalCoefficientEquiv` to the localized scalar factor. Its inverse uses the inverse
coefficient equivalence. The tensor universal property makes both maps well defined;
their composites fix pure tensors. Pure tensors generate, proving uniqueness. -/
theorem sfRationalHomCoordinates_existsUnique
    (K M : sfRationalConstructibleCategory l E Y) :
    ∃! e : (K ⟶ M) ≃+
        ((K.obj ⟶ M.obj) ⊗[Padic.coefficientExtensionIntegers l E] E),
      ∀ (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (f : K.obj ⟶ M.obj), e (a ⊗ₜ f) = f ⊗ₜ sfRationalCoefficientEquiv l E a := by
  let e := ((TensorProduct.congr (sfRationalCoefficientEquiv l E).toLinearEquiv
    (LinearEquiv.refl (Padic.coefficientExtensionIntegers l E) (K.obj ⟶ M.obj))).trans
      (TensorProduct.comm (Padic.coefficientExtensionIntegers l E) E (K.obj ⟶ M.obj))).toAddEquiv
  refine ⟨e, ?_, ?_⟩
  · intro a f
    simp [e]
  · intro e' he'
    apply AddEquiv.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a f => simp [he', e]
    | add x y hx hy => simp [hx, hy]

/-- Canonical Hom tensor E coordinates, uniquely fixed on every pure tensor.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def sfRationalHomCoordinates
    (K M : sfRationalConstructibleCategory l E Y) :=
  (sfRationalHomCoordinates_existsUnique l E Y K M).exists.choose

variable (p : ℕ) (hl : l ≠ p)
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The unique rational scalar extension on the current integral predicate.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: `sfConstructibleIntegralScalarExtension` is the actual completed integral
extension, restricted by `lem-weil-integral-scalar-extension-constructible`. Its scalar
identity `sfConstructibleIntegralScalarExtension_smul`, together with the canonical
constant-section Hom action in `sfIntegralConstructible_linear`, supplies balancing.
On each tensor Hom group extend f and a to the integral image of f and the image of a
under the canonical field inclusion. This is additive by the tensor universal property.
The integral functor laws and the scalar ring-map laws give identity and composition
on pure tensors; bilinearity gives them on all morphisms. The object map is prescribed
literally, and pure tensors generate the Hom groups, proving uniqueness of the functor.
The same construction applies to the identity coefficient embedding. -/
theorem sfRationalScalarExtension_existsUnique :
    ∃! F : sfRationalConstructibleCategory l E Y ⥤
        sfRationalConstructibleCategory l L Y,
      F.Additive ∧
      (∀ K : sfRationalConstructibleCategory l E Y,
        F.obj K = ⟨(sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj⟩) ∧
      (∀ (K K' : sfIntegralConstructibleCategory l E Y)
        (f : K ⟶ K') (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E Y).obj K ⟶
            (sfRationalConstructibleLocalization l E Y).obj K'))
          ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a))
            ⊗ₜ[Padic.coefficientExtensionIntegers l L]
              (sfConstructibleIntegralScalarExtension p l hl E L ι Y).map f :
                (sfRationalConstructibleLocalization l L Y).obj
                  ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) ⟶
                (sfRationalConstructibleLocalization l L Y).obj
                  ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K'))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let b := Padic.coefficientExtensionUniformizer l L
  let φ := integralScalarIntegerInclusion l E L ι
  let F := sfConstructibleIntegralScalarExtension p l hl E L ι Y
  have : F.Additive := ⟨fun {K M f g} ↦ by
    apply ObjectProperty.hom_ext
    change (integralScalarExtension l E L ι Y).map (f.hom + g.hom) = _
    exact (integralScalarExtension l E L ι Y).map_add⟩
  have hF : ScalarLocalization.IsSemilinear φ F := by
    intro K M a f
    apply ObjectProperty.hom_ext
    change (integralScalarExtension l E L ι Y).map (a • f.hom) =
      φ a • (F.map f).hom
    rw [(sfIntegralConstructible_linear l E Y).1,
      (sfIntegralConstructible_linear l L Y).1]
    exact sfConstructibleIntegralScalarExtension_smul p l hl E L ι Y K M f a
  have hu : IsUnit (algebraMap S (Localization.Away b) (φ t)) := by
    apply (MulEquiv.isUnit_map (sfRationalCoefficientEquiv l L).toMulEquiv).mp
    change IsUnit (sfRationalCoefficientEquiv l L (algebraMap S (Localization.Away b) (φ t)))
    rw [AlgEquiv.commutes]
    change IsUnit (ι (t : E))
    have ht := (IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)).map
      (sfRationalCoefficientEquiv l E).toRingHom
    have ht' := ht.map ι.toRingHom
    change IsUnit (ι (sfRationalCoefficientEquiv l E
      (algebraMap R (Localization.Away t) t))) at ht'
    rw [AlgEquiv.commutes] at ht'
    exact ht'
  let J := ScalarLocalization.extension t b φ hu F hF
  have hc : ScalarLocalization.coefficientMap t b φ hu =
      (sfRationalCoefficientEquiv l L).symm.toRingHom.comp
        (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom) := by
    symm
    apply (ScalarLocalization.coefficientMap_unique t b φ hu _).mp
    ext a
    apply (sfRationalCoefficientEquiv l L).injective
    change sfRationalCoefficientEquiv l L
        ((sfRationalCoefficientEquiv l L).symm
          (ι (sfRationalCoefficientEquiv l E (algebraMap R (Localization.Away t) a)))) =
      sfRationalCoefficientEquiv l L (algebraMap S (Localization.Away b) (φ a))
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
    rfl
  have hJ (K M : sfIntegralConstructibleCategory l E Y) (f : K ⟶ M)
      (a : Localization.Away t) :
      J.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk M) =
        (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a))
          ⊗ₜ[S] F.map f := by
    change ScalarLocalization.extensionHom t b φ hu F hF K M (a ⊗ₜ[R] f) = _
    have hmap := Classical.choose_spec
      (ScalarLocalization.existsUnique_semilinearHom t b φ hu F hF K M).exists a f
    change ScalarLocalization.extensionHom t b φ hu F hF K M (a ⊗ₜ[R] f) = _ at hmap
    rw [hmap, hc]
    rfl
  refine ⟨J, ⟨inferInstance, fun _ ↦ rfl, fun K M f a ↦ heq_of_eq (hJ K M f a)⟩, ?_⟩
  intro J' hJ'
  have : J'.Additive := hJ'.1
  refine CategoryTheory.Functor.ext hJ'.2.1 ?_
  intro K M f
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    apply (conj_eqToHom_iff_heq _ _ (hJ'.2.1 K) (hJ'.2.1 M)).2
    exact (hJ'.2.2 K.obj M.obj f a).trans (heq_of_eq (hJ K.obj M.obj f a).symm)
  | add x y hx hy =>
    rw [J'.map_add, J.map_add]
    erw [Preadditive.add_comp, Preadditive.comp_add]
    exact congrArg₂ (· + ·) hx hy

/-- The completed integral scalar transition followed by raw rationalization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def sfRationalScalarExtension :
    sfRationalConstructibleCategory l E Y ⥤ sfRationalConstructibleCategory l L Y :=
  (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose

/-- The object equation for rational scalar extension.
Source: def-weil-rationalization-karoubi
(blueprint: def-weil-rationalization-karoubi).
Proof: the uniquely specified extension has the prescribed integral object. -/
theorem sfRationalScalarExtension_obj (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E Y p hl L ι).obj K =
      ⟨(sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K.obj⟩ := by
  exact (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec.2.1 K

/-- The pure-tensor map equation for rational scalar extension.
Source: def-weil-rationalization-karoubi
(blueprint: def-weil-rationalization-karoubi).
Proof: this is the defining map equation of the uniquely specified extension. -/
theorem sfRationalScalarExtension_map_tmul
    (K K' : sfIntegralConstructibleCategory l E Y)
    (f : K ⟶ K') (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((sfRationalScalarExtension l E Y p hl L ι).map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E Y).obj K ⟶
            (sfRationalConstructibleLocalization l E Y).obj K'))
          ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a))
            ⊗ₜ[Padic.coefficientExtensionIntegers l L]
              (sfConstructibleIntegralScalarExtension p l hl E L ι Y).map f :
                (sfRationalConstructibleLocalization l L Y).obj
                  ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) ⟶
                (sfRationalConstructibleLocalization l L Y).obj
                  ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K')) := by
  exact (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec.2.2 K K' f a

/-- Additivity of the specified rational scalar transition.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance sfRationalScalarExtension_additive :
    (sfRationalScalarExtension l E Y p hl L ι).Additive :=
  (sfRationalScalarExtension_existsUnique l E Y p hl L ι).exists.choose_spec.1

/-- The source's global finite-field convention, with arbitrary Y and no relation
between Y and the fixed finite field. The intrinsic category is definitionally the
same category, independent of the unused global data.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable abbrev FiniteFieldDatum.sfRationalCategory
    (_D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ _D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  sfRationalConstructibleCategory l E Y

end WeilConjectures
