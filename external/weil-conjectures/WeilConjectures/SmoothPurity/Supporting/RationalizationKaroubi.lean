/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated

public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
/-! # Rationalized constructible integral categories and coefficient extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: def-weil-rationalization-karoubi).

This is raw Hom scalar localization, with the same integral objects. The canonical
localization isomorphism identifies its Hom modules with Hom tensor E. No retracts
are adjoined. The coefficient functor is fixed uniquely on objects and pure tensors.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d u

open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The raw rationalized category, without idempotent completion.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable abbrev rationalConstructibleCategory :=
  ScalarLocalization (Padic.coefficientExtensionIntegers l E)
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (Padic.coefficientExtensionUniformizer l E)

set_option linter.defProp false in
/-- The recorded raw scalar-localization theorem supplies precisely the induced shift
and image triangles, with exact localization and no new objects.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalTriangulationDatum :=
  letI := integralConstructibleShift_linear l E Y D hl (1 : ℤ)
  ScalarLocalization.exists_triangulated_scalarLocalization
    (Padic.coefficientExtensionIntegers l E)
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (Padic.coefficientExtensionUniformizer l E)

/-- The zero object in raw rationalization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleZero :
    CategoryTheory.Limits.HasZeroObject (rationalConstructibleCategory D l hl E Y) :=
  (rationalTriangulationDatum D l hl E Y).choose

/-- The induced shift, with the tensor-Hom shift specified by the triangulation datum.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleShift :
    HasShift (rationalConstructibleCategory D l hl E Y) ℤ :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose

/-- Additivity of every induced rational shift.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleShiftAdditive (n : ℤ) :
    (shiftFunctor (rationalConstructibleCategory D l hl E Y) n).Additive :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose n

/-- The canonical integral-to-rational functor is the identity on objects and tensors
morphisms with one. Source: blueprint order 1460
(blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalConstructibleLocalization :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      rationalConstructibleCategory D l hl E Y :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
    (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (Padic.coefficientExtensionUniformizer l E)

/-- The canonical shift comparison for localization.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalLocalizationCommShift :
    (rationalConstructibleLocalization D l hl E Y).CommShift ℤ :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose

/-- The image-triangle pretriangulation of the raw localized category.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructiblePretriangulated :
    Pretriangulated (rationalConstructibleCategory D l hl E Y) :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2.choose

/-- Triangulation for exactly the image triangles.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalConstructibleTriangulated :
    IsTriangulated (rationalConstructibleCategory D l hl E Y) :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
    |>.choose_spec.1

/-- The canonical localized coefficient field identification, fixed on fractions.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalCoefficientEquiv :
    Localization.Away (Padic.coefficientExtensionUniformizer l E) ≃ₐ[
      Padic.coefficientExtensionIntegers l E] E :=
  (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Rational scalar extension is uniquely specified by integral extension and the
field inclusion on scalar factors. This is the well-definedness needed by its definition.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: integral scalar extension is additive and linear for the integer inclusion.
Transport localized scalars through rationalCoefficientEquiv, the inclusion ι and
its target inverse. The tensor universal property therefore gives the stated map
on each Hom group. The integral functor laws and the multiplication law for scalar
factors show that it preserves identities and composition, first on pure tensors
and then on finite sums. Pure tensors generate every Hom module, proving uniqueness.
The object map is the actual restricted completed extension. -/
theorem rationalScalarExtension_existsUnique :
    ∃! F : rationalConstructibleCategory D l hl E Y ⥤
        rationalConstructibleCategory D l hl L Y,
      F.Additive ∧
      (∀ K : rationalConstructibleCategory D l hl E Y,
        F.obj K = ⟨(constructibleIntegralScalarExtension D l hl E L ι Y).obj K.obj⟩) ∧
      (∀ (K K' : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
        (f : K ⟶ K') (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (rationalConstructibleLocalization D l hl E Y).obj K ⟶
            (rationalConstructibleLocalization D l hl E Y).obj K'))
          ((rationalCoefficientEquiv l L).symm (ι (rationalCoefficientEquiv l E a))
            ⊗ₜ[Padic.coefficientExtensionIntegers l L]
              (constructibleIntegralScalarExtension D l hl E L ι Y).map f :
                (rationalConstructibleLocalization D l hl L Y).obj
                  ((constructibleIntegralScalarExtension D l hl E L ι Y).obj K) ⟶
                (rationalConstructibleLocalization D l hl L Y).obj
                  ((constructibleIntegralScalarExtension D l hl E L ι Y).obj K'))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let b := Padic.coefficientExtensionUniformizer l L
  let φ := integralScalarIntegerInclusion l E L ι
  let F := constructibleIntegralScalarExtension D l hl E L ι Y
  have : F.Additive := ⟨fun {K M f g} ↦ by
    apply ObjectProperty.hom_ext
    change (integralScalarExtension l E L ι Y).map (f.hom + g.hom) = _
    exact (integralScalarExtension l E L ι Y).map_add⟩
  have hF : ScalarLocalization.IsSemilinear φ F := by
    intro K M a f
    exact constructibleIntegralScalarExtension_smul D l hl E L ι Y K M f a
  have hu : IsUnit (algebraMap S (Localization.Away b) (φ t)) := by
    apply (MulEquiv.isUnit_map (rationalCoefficientEquiv l L).toMulEquiv).mp
    change IsUnit (rationalCoefficientEquiv l L (algebraMap S (Localization.Away b) (φ t)))
    rw [AlgEquiv.commutes]
    change IsUnit (ι (t : E))
    have ht := (IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)).map
      (rationalCoefficientEquiv l E).toRingHom
    have ht' := ht.map ι.toRingHom
    change IsUnit (ι (rationalCoefficientEquiv l E
      (algebraMap R (Localization.Away t) t))) at ht'
    rw [AlgEquiv.commutes] at ht'
    exact ht'
  let J := ScalarLocalization.extension t b φ hu F hF
  have hc : ScalarLocalization.coefficientMap t b φ hu =
      (rationalCoefficientEquiv l L).symm.toRingHom.comp
        (ι.toRingHom.comp (rationalCoefficientEquiv l E).toRingHom) := by
    symm
    apply (ScalarLocalization.coefficientMap_unique t b φ hu _).mp
    ext a
    apply (rationalCoefficientEquiv l L).injective
    change rationalCoefficientEquiv l L
        ((rationalCoefficientEquiv l L).symm
          (ι (rationalCoefficientEquiv l E (algebraMap R (Localization.Away t) a)))) =
      rationalCoefficientEquiv l L (algebraMap S (Localization.Away b) (φ a))
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
    rfl
  have hJ (K M : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) (f : K ⟶ M)
      (a : Localization.Away t) :
      J.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk M) =
        (rationalCoefficientEquiv l L).symm (ι (rationalCoefficientEquiv l E a))
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

/-- The specified scalar-extension functor on the raw rationalized categories.
Its defining theorem uniquely determines the whole functor, rather than merely
asserting existence of an unspecified comparison.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalScalarExtension :
    rationalConstructibleCategory D l hl E Y ⥤ rationalConstructibleCategory D l hl L Y :=
  (rationalScalarExtension_existsUnique D l hl E Y L ι).exists.choose

/-- Rational coefficient extension is additive, as specified in its defining property.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable instance rationalScalarExtension_additive :
    (rationalScalarExtension D l hl E Y L ι).Additive :=
  (rationalScalarExtension_existsUnique D l hl E Y L ι).exists.choose_spec.1

end WeilConjectures

namespace WeilConjectures

open CategoryTheory TensorProduct

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The induced map on localized scalar rings, through their canonical field coordinates.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalCoefficientMap :
    Localization.Away (Padic.coefficientExtensionUniformizer l E) →+*
      Localization.Away (Padic.coefficientExtensionUniformizer l L) :=
  (rationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (rationalCoefficientEquiv l E).toRingHom)

private instance completedScalar_additive :
    (constructibleIntegralScalarExtension D l hl E L ι Y).Additive where
  map_add := by
    intro K M f g
    apply ObjectProperty.hom_ext
    exact (integralScalarExtension l E L ι Y).map_add

private instance ordinaryIntegralScalar_additive :
    (integralConstructibleScalarExtension D l hl E L ι Y).Additive :=
  Functor.additive_of_iso (integralConstructibleScalarComparison D l hl E L ι Y).symm

private theorem ordinaryIntegralScalar_semilinear :
    ScalarLocalization.IsSemilinear (integralScalarIntegerInclusion l E L ι)
      (integralConstructibleScalarExtension D l hl E L ι Y) := by
  intro K M a f
  let e := integralConstructibleScalarComparison D l hl E L ι Y
  apply (cancel_mono (e.hom.app M)).1
  rw [e.hom.naturality, constructibleIntegralScalarExtension_smul,
    Linear.comp_smul, ← e.hom.naturality, Linear.smul_comp]

private theorem coefficientMap_isUnit :
    IsUnit (algebraMap (Padic.coefficientExtensionIntegers l L)
      (Localization.Away (Padic.coefficientExtensionUniformizer l L))
      (integralScalarIntegerInclusion l E L ι (Padic.coefficientExtensionUniformizer l E))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let b := Padic.coefficientExtensionUniformizer l L
  apply (MulEquiv.isUnit_map (rationalCoefficientEquiv l L).toMulEquiv).mp
  change IsUnit (rationalCoefficientEquiv l L
    (algebraMap S (Localization.Away b) (integralScalarIntegerInclusion l E L ι t)))
  rw [AlgEquiv.commutes]
  change IsUnit (ι (t : E))
  have ht := (IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)).map
    (rationalCoefficientEquiv l E).toRingHom
  have ht' := ht.map ι.toRingHom
  change IsUnit (ι (rationalCoefficientEquiv l E
    (algebraMap R (Localization.Away t) t))) at ht'
  rw [AlgEquiv.commutes] at ht'
  exact ht'

private theorem coefficientMap_eq :
    ScalarLocalization.coefficientMap
      (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
      (integralScalarIntegerInclusion l E L ι) (coefficientMap_isUnit l E L ι) =
        rationalCoefficientMap l E L ι := by
  symm
  apply (ScalarLocalization.coefficientMap_unique _ _ _ _ _).mp
  ext a
  apply (rationalCoefficientEquiv l L).injective
  change rationalCoefficientEquiv l L
      ((rationalCoefficientEquiv l L).symm (ι (rationalCoefficientEquiv l E
        (algebraMap _ (Localization.Away (Padic.coefficientExtensionUniformizer l E)) a)))) =
    rationalCoefficientEquiv l L (algebraMap _ _ (integralScalarIntegerInclusion l E L ι a))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

/-- The unique additive map induced by scalar extension on the tensor Hom module.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: ordinary sheaf tensor is additive, and its balanced relations respect the
constant-section action through the completed coefficient inclusion. The fraction-field
coordinate maps respect the
integer inclusion. Thus the stated formula is additive and balanced over O_E. The tensor
universal property gives the map; pure tensors generate, proving uniqueness. -/
theorem rationalScalarHom_existsUnique
    (K M : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    ∃! f : (Localization.Away (Padic.coefficientExtensionUniformizer l E) ⊗[
        Padic.coefficientExtensionIntegers l E] (K ⟶ M)) →+
      (Localization.Away (Padic.coefficientExtensionUniformizer l L) ⊗[
        Padic.coefficientExtensionIntegers l L]
        ((integralConstructibleScalarExtension D l hl E L ι Y).obj K ⟶
          (integralConstructibleScalarExtension D l hl E L ι Y).obj M)),
      ∀ (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (g : K ⟶ M),
        f (a ⊗ₜ g) = rationalCoefficientMap l E L ι a ⊗ₜ
          (integralConstructibleScalarExtension D l hl E L ι Y).map g := by
  have h := ScalarLocalization.existsUnique_semilinearHom
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
    (integralScalarIntegerInclusion l E L ι) (coefficientMap_isUnit l E L ι)
    (integralConstructibleScalarExtension D l hl E L ι Y)
    (ordinaryIntegralScalar_semilinear D l hl E Y L ι) K M
  simpa only [coefficientMap_eq l E L ι] using h

/-- The actual tensor Hom map, selected from its uniquely determining formula.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalScalarHom
    (K M : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  (rationalScalarHom_existsUnique D l hl E Y L ι K M).exists.choose

/-- The tensor Hom maps respect identities and composition.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: on pure tensors, the formulas for the uniquely specified Hom map and for
ScalarLocalization.composition reduce this to functoriality of integral scalar extension
and multiplicativity of rationalCoefficientMap. Bilinearity extends the identities to
all tensor morphisms. -/
theorem rationalScalarHom_laws :
    (∀ K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y,
      rationalScalarHom D l hl E Y L ι K K (1 ⊗ₜ 𝟙 K) =
        1 ⊗ₜ 𝟙 ((integralConstructibleScalarExtension D l hl E L ι Y).obj K)) ∧
    (∀ (K M N : rationalConstructibleCategory D l hl E Y) (f : K ⟶ M) (g : M ⟶ N),
      rationalScalarHom D l hl E Y L ι K.obj N.obj (f ≫ g) =
        ScalarLocalization.composition (Padic.coefficientExtensionIntegers l L)
          (boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y)
          (Padic.coefficientExtensionUniformizer l L) _ _ _
          (rationalScalarHom D l hl E Y L ι M.obj N.obj g)
          (rationalScalarHom D l hl E Y L ι K.obj M.obj f)) := by
  have hm (K M : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (f : K ⟶ M) :
      rationalScalarHom D l hl E Y L ι K M (a ⊗ₜ f) =
        rationalCoefficientMap l E L ι a ⊗ₜ
          (integralConstructibleScalarExtension D l hl E L ι Y).map f :=
    (rationalScalarHom_existsUnique D l hl E Y L ι K M).exists.choose_spec a f
  constructor
  · intro K
    rw [hm]
    simp
  · intro K M N f g
    change rationalScalarHom D l hl E Y L ι _ _
      (ScalarLocalization.composition _ _ _ _ _ _ g f) = _
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp only [ScalarLocalization.composition_tmul, hm, map_mul, Functor.map_comp]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- Scalar extension on raw rational stages: integral scalar extension on objects,
and the specified tensor map on morphisms.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalOrdinaryScalarExtension :
    rationalConstructibleCategory D l hl E Y ⥤ rationalConstructibleCategory D l hl L Y where
  obj K := ⟨(integralConstructibleScalarExtension D l hl E L ι Y).obj K.obj⟩
  map {K M} f := rationalScalarHom D l hl E Y L ι K.obj M.obj f
  map_id K := (rationalScalarHom_laws D l hl E Y L ι).1 K.obj
  map_comp {K M N} f g := (rationalScalarHom_laws D l hl E Y L ι).2 K M N f g

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    simp [c]
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.inductionOn with
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      rw [(conj_eqToHom_iff_heq _ _ (hF ⟨K⟩) (hF ⟨K'⟩)).mpr (mF K K' f a),
        (conj_eqToHom_iff_heq _ _ (hG ⟨K⟩) (hG ⟨K'⟩)).mpr (mG K K' f a)]
      dsimp [c]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      simpa only [ScalarLocalization.localization, Category.assoc] using
        congrArg (fun z :
          (⟨F₀.obj K⟩ : ScalarLocalization S D v) ⟶ ⟨G₀.obj K'⟩ ↦
            eqToHom (hF ⟨K⟩) ≫ z ≫ eqToHom (hG ⟨K'⟩).symm) he'
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

private instance rationalOrdinary_additive :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).Additive where
  map_add := by
    intro K M f g
    exact (rationalScalarHom D l hl E Y L ι K.obj M.obj).map_add f g

/-- The ordinary-model functor identifies with the published completed scalar extension
by tensoring the normalized quotient completion comparison with one.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi).
Proof: use integralConstructibleScalarComparison on every integral object. The published
rationalScalarExtension has the specified integral object map and balanced tensor map.
Integral comparison naturality therefore gives naturality on pure rational tensors and
then on sums. Rationalizing its inverse gives the inverse; the displayed components
uniquely fix the natural isomorphism, including all newly localized morphisms. -/
theorem rationalOrdinaryComparison_existsUnique :
    ∃! c : rationalOrdinaryScalarExtension D l hl E Y L ι ≅
        rationalScalarExtension D l hl E Y L ι,
      ∀ K : rationalConstructibleCategory D l hl E Y,
        HEq (c.hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
              (integralConstructibleScalarComparison D l hl E L ι Y).hom.app K.obj) := by
  exact localizedIso
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
    (rationalCoefficientMap l E L ι)
    (integralConstructibleScalarExtension D l hl E L ι Y)
    (constructibleIntegralScalarExtension D l hl E L ι Y)
    (integralConstructibleScalarComparison D l hl E L ι Y)
    (rationalOrdinaryScalarExtension D l hl E Y L ι)
    (rationalScalarExtension D l hl E Y L ι)
    (fun _ ↦ rfl)
    (rationalScalarExtension_existsUnique D l hl E Y L ι).exists.choose_spec.2.1
    (fun K M f a ↦ heq_of_eq
      ((rationalScalarHom_existsUnique D l hl E Y L ι K M).exists.choose_spec a f))
    (rationalScalarExtension_existsUnique D l hl E Y L ι).exists.choose_spec.2.2

/-- The normalized comparison to the existing completed rational scalar functor.
Source: blueprint order 1460 (blueprint: def-weil-rationalization-karoubi). -/
noncomputable def rationalOrdinaryComparison :=
  (rationalOrdinaryComparison_existsUnique D l hl E Y L ι).exists.choose

end WeilConjectures
