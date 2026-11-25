/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SixFunctors.Completed.CompletedScalarCanonicalAssociatorFormula

/-! # Ambient core of integral transport for a normalized scalar associator -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedCoefficientMap
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChangeData
attribute [local irreducible] CategoryTheory.sheafCompose CategoryTheory.presheafToSheaf
  CategoryTheory.Functor.leftAdjoint SheafOfModules.changeOfRings
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
private theorem normalized_component
    {D H : Type*} [Category D] [Category H]
    (G : D ⥤ H) (G' : D → H) (χB : ∀ Y, G.obj Y ⟶ G' Y)
    (X Y Y' : D) (Z V W V' : H)
    (a : Y ≅ X) (b : Z ≅ G.obj Y) (d : V ≅ W)
    (χA : X ⟶ Y') (χD : W ⟶ V')
    (f : Z ⟶ V) (t : G.obj X ⟶ W)
    (h : f ≫ d.hom = b.hom ≫ G.map a.hom ≫ t)
    (hY : Y = Y') (hZ : Z = G' Y') (hV : V = V')
    (nA : HEq a.inv χA) (nB : HEq b.inv (χB Y)) (nD : HEq d.inv χD)
    [IsIso χA] [IsIso (χB Y')] :
    eqToHom hZ.symm ≫ f ≫ eqToHom hV =
      inv (χB Y') ≫ G.map (inv χA) ≫ t ≫ χD := by
  subst Y
  subst Z
  subst V
  have na := eq_of_heq nA
  have nb := eq_of_heq nB
  have nd := eq_of_heq nD
  simp only [← na, ← nb, ← nd, eqToHom_refl, Category.id_comp, Category.comp_id]
  apply (cancel_mono d.hom).mp
  simpa using h

end WeilConjectures

namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- The original interface retains hB and hD; the endpoint equalities suffice here.
set_option linter.unusedVariables false in
/-- Ambient equality underlying integral normalized scalar transport.
Source: Definition 3.4.10 and Lemma 3.4.12, pp. 22-23; Proposition 3.5.1, p. 24.
(blueprint: lem-sf-normalized-scalar-associator-localization-transport-integral-core).
Proof: after applying the faithful finite-Tor integral inclusion, expand the normalized
associator equation using the three realization equalities and inverse-realization
normalizations; identify the resulting ordinary balanced tensor map with the unique
normalized completed integral associator.
-/
theorem normalized_scalar_associator_integral_transport_core
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
    (sfIntegralConstructible l M.carrier T).ι.map
      (eqToHom hsource.symm ≫
        (PurCompactSupport.finiteTorIntegralInclusion l M.carrier T).map
          (α.iso.hom.app K) ≫
        eqToHom htarget) =
      (sfIntegralConstructible l M.carrier T).ι.map
        ((sfIntegralScalarComp l E.carrier L.carrier i T 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          (⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T)) := by
  let K₀ : sfIntegralConstructibleCategory l E.carrier T := ⟨K.obj, K.property.1⟩
  have hK := CompletedLineTensor.intrinsic_complete l E.carrier T K₀
  have hAK := CompletedLineTensor.extension_complete l E.carrier T L.carrier i K.obj hK
  have := ((finiteFreeCompletedScalarComparison l E.carrier L.carrier i T).2.1
    K.obj hK).1
  have := ((finiteFreeCompletedScalarComparison l L.carrier M.carrier j T).2.1
    _ hAK).1
  have eA : (A.functor.obj K).obj =
      (integralScalarExtensionOfUniverses l E.carrier L.carrier i T).obj K.obj :=
    congrArg (fun F ↦ F.obj K) hA
  have eS := congrArg (fun Z ↦ Z.obj) hsource
  have eT := congrArg (fun Z ↦ Z.obj) htarget
  have hc := normalized_component
    (pbcDerivedExtend (completedCoefficientMap l L.carrier M.carrier j T))
    (integralScalarExtensionOfUniverses l L.carrier M.carrier j T).obj
    (fun Y ↦ (completedScalarComparison l L.carrier M.carrier j T).app Y)
    _ (A.functor.obj K).obj _ (B.functor.obj (A.functor.obj K)).obj
    (D.functor.obj K).obj _ _
    (A.realization.app K) (B.realization.app (A.functor.obj K)) (D.realization.app K)
    ((completedScalarComparison l E.carrier L.carrier i T).app K.obj)
    ((completedScalarComparison l E.carrier M.carrier (j.comp i) T).app K.obj)
    (α.iso.hom.app K).hom
    ((PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E.carrier L.carrier i M.carrier j
        T)).hom.app K.obj)
    (α.normalized K) eA eS eT (nA K) (nB (A.functor.obj K)) (nD K)
  simp only [Functor.map_comp, eqToHom_map]
  change eqToHom eS.symm ≫ (α.iso.hom.app K).hom ≫ eqToHom eT = _
  rw [hc]
  exact (completedScalarCanonicalAssociatorFormula l E.carrier L.carrier M.carrier i j T K₀).symm

end WeilConjectures.ConstructibleExceptionalCoefficients
