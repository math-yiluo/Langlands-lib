/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import Mathlib.Topology.Instances.ZMod
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-!
# Proper direct-image hypotheses for the recorded admissible coefficients

Source: blueprint main-20261015, proposition-construction-independence-rf-shriek, proper-image
paragraph. (blueprint: det-sf-comp-proper-admissible-hypotheses).

Proof plan: split the admissible coefficient predicate into its six cases. In each
case transport the proper-image hypotheses across the displayed coefficient-ring
isomorphism; the finite, integral, rational, and finite-extension cases invoke
`proper_image_localizing_proper_coefficients`, as does the finite-subextension
algebraic-closure case. The transport argument uses the induced
equivalences of module and derived categories, which preserve
finite Tor amplitude, constant constructibility, localizing closure, and colimits.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] [IsIso a]

private theorem ctf_comap (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)))
    (hK : constantModelBoundedConstructible Λ' X K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible Λ X
        ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj K) := by
  exact constantModelCtf_coefficientIso (Mon.mkIso' (asIso a)).symm X ⟨K, hK⟩

private theorem localizing_comap (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))) (hK : localizingClosureProEtale Λ' X K) :
    localizingClosureProEtale Λ X
      ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj K) := by
  let F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) := (Mod.comap (coefficientMap a X)).mapDerivedCategory
  have : (Mod.comap (coefficientMap a X) :
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap a X)).isEquivalence_functor
  have : F.IsEquivalence := inferInstance
  let Q := localizingClosureProEtale Λ X
  have hQ : IsLocalizingSubcategory Q :=
    (localizingClosure_exists Λ X
      (constantModelBoundedConstructible Λ X ⊓ fun L ↦
        DerivedCategory.finiteTorAmplitude _ L)).2.2.2.1
  let := hQ.1
  let := hQ.2.1
  have hR : IsLocalizingSubcategory (Q.inverseImage F) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I D hD hDR
    let := hD
    have hcol := F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits
    have : PreservesColimit D F := hcol.preservesColimitsOfShape.preservesColimit
    exact Q.prop_of_iso (preservesColimitIso F D).symm
      (hQ.2.2 (D ⋙ F) inferInstance hDR)
  apply hK (Q.inverseImage F) hR
  intro L hL
  have hFL := ctf_comap a X L hL
  exact fun P _ hP ↦ hP _ hFL

include a in
private theorem properHypotheses_comap {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ProperLocalizingHypotheses Λ' p) : ProperLocalizingHypotheses Λ p := by
  let R (Z : Scheme.{u}) : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ' Z) ⥤ Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z) := Mod.comap (coefficientMap a Z)
  let E₀ (Z : Scheme.{u}) :=
    Mod.comapEquivalenceOfIsIso (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap a Z)
  have (Z : Scheme.{u}) : (E₀ Z).functor.Additive := inferInstanceAs (R Z).Additive
  have (Z : Scheme.{u}) : (E₀ Z).inverse.Additive :=
    inferInstanceAs (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (asIso (coefficientMap a Z)).inv).Additive
  let E (Z : Scheme.{u}) := (E₀ Z).mapDerivedCategory
  have (Z : Scheme.{u}) : (R Z).mapDerivedCategory.IsEquivalence :=
    (E Z).isEquivalence_functor
  have (Z : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoComapInv (coefficientMap a Z)).symm
  let F := (lowerStar Λ p).rightDerivedFunctor
  let F' := (lowerStar Λ' p).rightDerivedFunctor
  let e : (E X).inverse ⋙ F' ⋙ (E Y).functor ≅ F :=
    Functor.isoWhiskerLeft (E X).inverse (derivedComapLowerStarIso a p) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E X).counitIso F ≪≫ F.leftUnitor
  have hinv (Z : Scheme.{u}) :
      coefficientMap (asIso a).inv Z = inv (coefficientMap a Z) := by
    simp only [asIso_inv]
    exact Functor.map_inv (upperStarFromPoint Z) a
  refine ⟨?_, ?_⟩
  · intro K
    have hK' := ctf_comap (asIso a).inv X K.obj K.property
    simp only [hinv] at hK'
    have hFK' := h.1 ⟨(E X).inverse.obj K.obj, hK'⟩
    have ht := ctf_comap a Y _ hFK'
    have hi := e.app K.obj
    refine ⟨?_, (DerivedCategory.finiteTorAmplitude _).prop_of_iso hi ht.2⟩
    refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso hi ht.1.1, fun n ↦ ?_⟩
    have := (constantModelConstructibleFiniteTor_wellDefined Λ Y).1
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ Y)
      ((DerivedCategory.homologyFunctor _ n).mapIso hi) (ht.1.2 n)
  · intro I K
    let D := K ⋙ (localizingClosureProEtale Λ X).ι
    let L : Discrete I ⥤ (localizingClosureProEtale Λ' X).FullSubcategory :=
      (localizingClosureProEtale Λ' X).lift (D ⋙ (E X).inverse)
        (fun i ↦ by
          change localizingClosureProEtale Λ' X
            ((Mod.comap (asIso (coefficientMap a X)).inv).mapDerivedCategory.obj
              (K.obj i).obj)
          simpa only [coefficientMap, asIso_inv, Functor.map_inv] using
            localizing_comap (asIso a).inv X _ (K.obj i).property)
    have : PreservesColimit (L ⋙ (localizingClosureProEtale Λ' X).ι) F' := h.2 I L
    have : PreservesColimit (D ⋙ (E X).inverse) F' :=
      preservesColimit_of_iso_diagram F'
        ((localizingClosureProEtale Λ' X).liftCompιIso (D ⋙ (E X).inverse)
          (fun i ↦ by
          change localizingClosureProEtale Λ' X
            ((Mod.comap (asIso (coefficientMap a X)).inv).mapDerivedCategory.obj
              (K.obj i).obj)
          simpa only [coefficientMap, asIso_inv, Functor.map_inv] using
            localizing_comap (asIso a).inv X _ (K.obj i).property))
    have : PreservesColimit D (E X).inverse := by
      have hcol := (E X).symm.toAdjunction.leftAdjoint_preservesColimits
      exact hcol.preservesColimitsOfShape.preservesColimit
    have : PreservesColimit (D ⋙ (E X).inverse ⋙ F') (E Y).functor :=
      (E Y).toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
    have : PreservesColimit D ((E X).inverse ⋙ F') :=
      comp_preservesColimit (E X).inverse F'
    have : PreservesColimit D (((E X).inverse ⋙ F') ⋙ (E Y).functor) :=
      comp_preservesColimit ((E X).inverse ⋙ F') (E Y).functor
    have : PreservesColimit D ((E X).inverse ⋙ F' ⋙ (E Y).functor) :=
      preservesColimit_of_natIso D (Functor.associator _ _ _)
    exact preservesColimit_of_natIso D e

/-- Proper direct image preserves the Dctf generators and ambient coproducts for
every isomorphism class of recorded admissible coefficient.

Source: blueprint proposition-construction-independence-rf-shriek, second proof paragraph, with the
coefficient convention of definition-localizing-subcategory.
(blueprint: det-sf-comp-proper-admissible-hypotheses).

Proof: restriction along a coefficient isomorphism is an exact monoidal equivalence.
It preserves finite presentations, finite constant local models, Tor intervals and
localizing closures. The derived restriction/direct-image comparison conjugates the
pushforwards, so their preservation properties transfer. Split admissibility into its
six representatives and apply the existing coefficient theorem to each. -/
theorem properLocalizingHypotheses_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ProperLocalizingHypotheses Λ p := by
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  have hzero : ∃ n : ℕ, (ℓ ^ n : ZMod 1) = 0 := ⟨0, Subsingleton.elim _ _⟩
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, ⟨n, hn⟩, ⟨e⟩⟩ := h
    have : Finite A := hfin
    have hA : ∃ n : ℕ, (ℓ ^ n : A) = 0 := by
      refine ⟨n, ?_⟩
      simpa using hn (1 : A)
    apply properHypotheses_comap e.hom.hom p
    exact proper_image_localizing_proper_coefficients ℓ E₀ A hA
      (Mon.mk (Profinite.continuousMapRingObj A)) (by simp) k p
  · obtain ⟨e⟩ := h
    apply properHypotheses_comap e.hom.hom p
    exact proper_image_localizing_proper_coefficients ℓ E₀ (ZMod 1) hzero
      (Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) (by simp) k p
  · obtain ⟨e⟩ := h
    apply properHypotheses_comap e.hom.hom p
    exact proper_image_localizing_proper_coefficients ℓ E₀ (ZMod 1) hzero
      (Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) (by simp) k p
  · obtain ⟨E, ⟨e⟩⟩ := h
    apply properHypotheses_comap e.hom.hom p
    exact proper_image_localizing_proper_coefficients ℓ E (ZMod 1) hzero
      (Mon.mk (Profinite.continuousMapRingObj E)) (by simp) k p
  · obtain ⟨E, ⟨e⟩⟩ := h
    apply properHypotheses_comap e.hom.hom p
    exact proper_image_localizing_proper_coefficients ℓ E (ZMod 1) hzero
      (Mon.mk (Profinite.padicIntegersRingObj ℓ E)) (by simp) k p
  · obtain ⟨e⟩ := h
    apply properHypotheses_comap e.hom.hom p
    exact proper_image_localizing_proper_coefficients ℓ E₀ (ZMod 1) hzero
      (Mon.mk (Profinite.padicAlgClRingObj ℓ)) (by simp) k p

end AlgebraicGeometry.ProEtale.CondensedRing
