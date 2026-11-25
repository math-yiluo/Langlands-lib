/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedScalarAssociatorIntegralTransportCore

/-! # Integral transport of a normalized scalar associator -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The integral step of localization transport. The supplied associator is first
transported along the object equalities induced by its three realization equalities;
the transported map is then the intrinsic normalized integral associator. This is
strictly the integral part of the localization statement.
Source: Definition 3.4.10 and Lemma 3.4.12, pp. 22-23; Proposition 3.5.1, p. 24.
(blueprint: lem-sf-normalized-scalar-associator-localization-transport-integral).
Proof: apply the three realization equalities and the inverse-realization normalizations
to the normalized scalar-composition equation. The resulting equality is the
unique normalized completed integral associator, by its defining uniqueness.
-/
theorem normalized_scalar_associator_integral_transport
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
    (K : C.{u, v} l Ω T (.integral E))
    (hsource :
      (⟨(B.functor.obj (A.functor.obj K)).obj,
        (B.functor.obj (A.functor.obj K)).property.1⟩ :
        sfIntegralConstructibleCategory l M.carrier T) =
        (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          E.carrier L.carrier i T ⋙
          sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
            L.carrier M.carrier j T).obj
          ((⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T)))
    (htarget :
      (⟨(D.functor.obj K).obj, (D.functor.obj K).property.1⟩ :
        sfIntegralConstructibleCategory l M.carrier T) =
        (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          E.carrier M.carrier (j.comp i) T).obj
          ((⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T))) :
    HEq
      (eqToHom hsource.symm ≫
        (PurCompactSupport.finiteTorIntegralInclusion l M.carrier T).map
          (α.iso.hom.app K) ≫
        eqToHom htarget)
      ((sfIntegralScalarComp l E.carrier L.carrier i T 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
        (⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T)) := by
  have hcore := normalized_scalar_associator_integral_transport_core l Ω E L M i j T A B D
    hA hB hD nA nB nD α K hsource htarget
  apply heq_of_eq
  apply (sfIntegralConstructible l M.carrier T).ι.map_injective
  exact hcore

end WeilConjectures.ConstructibleExceptionalCoefficients
