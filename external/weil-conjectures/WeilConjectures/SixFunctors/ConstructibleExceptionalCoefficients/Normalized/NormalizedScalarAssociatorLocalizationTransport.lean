/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedScalarAssociatorIntegralTransport

/-! # Localization transport for a normalized scalar associator -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem map_transport_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} : HEq (F.map f)
      (F.map (eqToHom hX.symm ≫ f ≫ eqToHom hY)) := by
  cases hX
  cases hY
  simp
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The localization of a supplied normalized associator is the localization of the
canonical integral associator.  This is the transport step in the proof of
`lem-sf-normalized-scalar-associator-localization`: identify the supplied functors with
the completed scalar extensions using their realization equalities, use the three
inverse-realization normalizations and the balanced tensor normalization, then apply
the raw localization functor.  The argument is forward transport and does not use
faithfulness of localization.  It also covers identity embeddings and repeated fields.
(blueprint: lem-sf-normalized-scalar-associator-localization-transport).
-/
theorem normalized_scalar_associator_localization_transport
    (E L M : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (T : Scheme.{max u v})
    (A : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T)
    (B : Scalar.{u, v} l Ω (s := .integral L) (t := .integral M)
      (PurCompactSupport.completedChange l L.carrier M.carrier j) T)
    (D : Scalar.{u, v} l Ω (s := .integral E) (t := .integral M)
      (PurCompactSupport.completedChange l E.carrier M.carrier (j.comp i)) T)
    (hA : A.functor ⋙ (finiteTorConstructibleIntegral l L.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T)
    (hB : B.functor ⋙ (finiteTorConstructibleIntegral l M.carrier T).ι =
      (finiteTorConstructibleIntegral l L.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l L.carrier M.carrier j T)
    (hD : D.functor ⋙ (finiteTorConstructibleIntegral l M.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier M.carrier (j.comp i) T)
    (nA : ∀ K, HEq (A.realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i T).app K.obj))
    (nB : ∀ K, HEq (B.realization.inv.app K)
      ((completedScalarComparison l L.carrier M.carrier j T).app K.obj))
    (nD : ∀ K, HEq (D.realization.inv.app K)
      ((completedScalarComparison l E.carrier M.carrier (j.comp i) T).app K.obj))
    (α : ScalarComposition.{u, v} l Ω
      (PurCompactSupport.completedMap_composition l E.carrier L.carrier i M.carrier j)
      T A B D)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((rationalization.{u, v} l Ω M T).map (α.iso.hom.app K))
      ((sfRationalConstructibleLocalization l M.carrier T).map
        ((sfIntegralScalarComp l E.carrier L.carrier i T 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          ⟨K.obj, K.property.1⟩)) := by
  let KI : sfIntegralConstructibleCategory l E.carrier T := ⟨K.obj, K.property.1⟩
  let hsource :
      (⟨(B.functor.obj (A.functor.obj K)).obj,
        (B.functor.obj (A.functor.obj K)).property.1⟩ :
        sfIntegralConstructibleCategory l M.carrier T) =
      (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          E.carrier L.carrier i T ⋙
        sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          L.carrier M.carrier j T).obj KI := by
    have hA' := Functor.congr_obj hA K
    have hB' := Functor.congr_obj hB (A.functor.obj K)
    have hA'' :
        (finiteTorConstructibleIntegral l L.carrier T).ι.obj (A.functor.obj K) =
          (integralScalarExtensionOfUniverses l E.carrier L.carrier i T).obj
            ((finiteTorConstructibleIntegral l E.carrier T).ι.obj K) := by
      simpa only [Functor.comp_obj] using hA'
    have hB0 := hB'
    change (B.functor.obj (A.functor.obj K)).obj = _ at hB0
    have hB'' :
        (B.functor.obj (A.functor.obj K)).obj =
          (integralScalarExtensionOfUniverses l L.carrier M.carrier j T).obj
            ((finiteTorConstructibleIntegral l L.carrier T).ι.obj
              (A.functor.obj K)) := by
      simpa only [Functor.comp_obj] using hB0
    apply ObjectProperty.FullSubcategory.ext
    have h := hB''.trans (congrArg
      (integralScalarExtensionOfUniverses l L.carrier M.carrier j T).obj hA'')
    have hextEL : integralScalarExtensionOfUniverses l E.carrier L.carrier i T =
        integralScalarExtension l E.carrier L.carrier i T := rfl
    have hextLM : integralScalarExtensionOfUniverses l L.carrier M.carrier j T =
        integralScalarExtension l L.carrier M.carrier j T := rfl
    rw [hextEL, hextLM] at h
    change (B.functor.obj (A.functor.obj K)).obj =
      (integralScalarExtensionOfUniverses l L.carrier M.carrier j T).obj
        ((integralScalarExtensionOfUniverses l E.carrier L.carrier i T).obj
          ((finiteTorConstructibleIntegral l E.carrier T).ι.obj K))
    exact h
  let htarget :
      (⟨(D.functor.obj K).obj, (D.functor.obj K).property.1⟩ :
        sfIntegralConstructibleCategory l M.carrier T) =
      (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          E.carrier M.carrier (j.comp i) T).obj KI := by
    have hD' := Functor.congr_obj hD K
    have hD0 := hD'
    change (D.functor.obj K).obj = _ at hD0
    have hD'' :
        (D.functor.obj K).obj =
          (integralScalarExtensionOfUniverses l E.carrier M.carrier (j.comp i) T).obj
            ((finiteTorConstructibleIntegral l E.carrier T).ι.obj K) := by
      simpa only [Functor.comp_obj] using hD0
    apply ObjectProperty.FullSubcategory.ext
    have hextEM : integralScalarExtensionOfUniverses l E.carrier M.carrier (j.comp i) T =
        integralScalarExtension l E.carrier M.carrier (j.comp i) T := rfl
    rw [hextEM] at hD''
    change (D.functor.obj K).obj =
      (integralScalarExtensionOfUniverses l E.carrier M.carrier (j.comp i) T).obj
        ((finiteTorConstructibleIntegral l E.carrier T).ι.obj K)
    exact hD''
  have hInt := normalized_scalar_associator_integral_transport l Ω E L M i j T A B D
    hA hB hD nA nB nD α K hsource htarget
  have hLoc := map_heq (sfRationalConstructibleLocalization l M.carrier T)
    rfl rfl hInt
  have hTransport := map_transport_heq
    (sfRationalConstructibleLocalization l M.carrier T) hsource htarget
      (f := (PurCompactSupport.finiteTorIntegralInclusion l M.carrier T).map
        (α.iso.hom.app K))
  have hLoc' := hTransport.trans hLoc
  simpa only [rationalization, Functor.comp_map, Functor.map_comp,
    eqToHom_map, eqToHom_refl, Category.id_comp, Category.comp_id] using hLoc'

end WeilConjectures.ConstructibleExceptionalCoefficients
