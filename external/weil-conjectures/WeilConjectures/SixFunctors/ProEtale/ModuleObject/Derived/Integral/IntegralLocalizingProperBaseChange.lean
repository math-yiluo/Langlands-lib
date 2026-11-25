/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.UnboundedBaseChangeExtension
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators

/-!
# Integral proper base change on localizing categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic,
Integral proper base change on localizing categories
(blueprint: proposition-proper-base-change-localizing-categories--1).

Both endpoints belong to the target localizing closure, and the specified ambient
exchange is invertible on every object of the source closure. Since these are full
subcategories, this is precisely the isomorphism of functors between the two
localizing categories. The generators are Dbc, without imposing finite Tor
amplitude or completeness on the ambient closure.
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.CondensedRing.condensedAmbientExchange

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open MonoidalCategory MonObj in
/-- Postcomposition with a topological ring equivalence identifies the continuous-function
condensed ring objects. Source: the coefficient conventions of the integral localizing
base-change statement (blueprint: proposition-proper-base-change-localizing-categories--1). -/
private noncomputable def coefficientMonIso
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let h := Profinite.continuousMapRingSheafMap e.toRingHom he
  let k := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
  let q : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := k
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply (x.down t)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply (x.down t) }
  let F := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have _ : IsMonHom (F.mapIso q).hom :=
    inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat Ab)).map h))
  exact Mon.mkIso' (F.mapIso q)

/-- The embedded finite extension and its field range have isometric integer rings.
Source: the coefficient conventions of the integral localizing base-change statement
(blueprint: proposition-proper-base-change-localizing-categories--1). -/
private theorem integral_coefficient_iso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E) ≅
        Mon.mk (Profinite.padicIntegersRingObj ℓ F)) := by
  let f := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let F : PadicAlgCl.FiniteIntermediateField ℓ :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  let e : E ≃ₐ[ℚ_[ℓ]] F := f.equivFieldRange
  let t : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ F :=
    { toFun := fun x ↦ ⟨e x.val, x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, by
        have h := (PadicAlgCl.mem_integers_iff ℓ F x.val).mp x.property
        change ‖algebraMap E (PadicAlgCl ℓ) (e.symm x.val)‖₊ ≤ 1
        change ‖(e (e.symm x.val)).val‖₊ ≤ 1
        simpa only [e.apply_symm_apply, IntermediateField.algebraMap_apply] using h⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  have ht : Isometry t := by
    apply Isometry.of_dist_eq
    intro x y
    rfl
  have hti : Continuous t.symm :=
    (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  exact ⟨F, ⟨coefficientMonIso t ht.continuous hti⟩⟩

-- Elaborating the inherited derived functors and full-subcategory structures needs this budget.
/-- Integral proper base change on the localizing closure of bounded constructibles.
Source: blueprint main-20261015, sk-thm-sf-pf-adic-base-change
(blueprint: proposition-proper-base-change-localizing-categories--1).

Proof plan:
1. In the standing positive-characteristic scheme setting, integral proper base
   change (proposition-proper-direct-image-constructible-complexes, clauses 1 and 3) gives the
   specified ordinary exchange isomorphism on Dbc. Integral-models clause 3
   preserves its endpoints under inverse image, and proper-fp-permanence makes
   the base-changed vertical arrow proper.
2. The proper-image-localizing-proper and proper-base-change-unbounded-pullback
   nodes give exact sum-preserving restrictions of the four functors. The equality
   Dctf = Dbc in lemma-integral-models identifies their localizing closures.
3. Cartesian condensed coefficients identify pullbacks with the coefficients at
   the other corner. The full module tensor pullback is exact, so its left derived
   functor is its termwise functor (sk-def-sfb-derived-categories).
4. Under the ordinary upper/lower-star Hom bijections, the tensor pullback
   composition comparison is conjugate to the sectionwise direct-image pasting
   comparison (def-sfb-module-upper-star-comp and lower-star-comp).
5. Proetale-derived-pullback-composition identifies the canonical derived
   comparison on K-flat representatives with that termwise comparison. Hence
   condensedAmbientExchange is exactly the unit/comparison/counit exchange of
   the unbounded extension lemma, with the derived adjunctions of the same full
   module pullback and pushforward composites.
6. Apply proposition-proper-base-change-localizing-categories--1 to the integral coefficient
   ring. Step 1 supplies its generator hypothesis; lemma-integral-models gives
   Dctf = Dbc. The exchange is invertible throughout the stated closure, and
   step 2 places both endpoints in the target closure.
-/
theorem integralLocalizing_properBaseChange
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra E (PadicAlgCl ℓ)]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X' X Y' Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    [p.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [p'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    [IsProper p] (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)))
    (hK : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) K) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y')
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor ⋙
          (upperStar (Profinite.padicIntegersRingObj ℓ E) g).leftDerivedFunctor).obj K) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y')
        (((upperStar (Profinite.padicIntegersRingObj ℓ E) g').leftDerivedFunctor ⋙
          (lowerStar (Profinite.padicIntegersRingObj ℓ E) p').rightDerivedFunctor).obj K) ∧
      IsIso ((condensedAmbientExchange (Profinite.padicIntegersRingObj ℓ E) sq).app K) := by
  classical
  obtain ⟨F, ⟨e⟩⟩ := integral_coefficient_iso.{u} ℓ E
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  have hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ F)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj F))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
    Or.inr (Or.inr (Or.inl ⟨F, Or.inl ⟨e⟩⟩))
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, ⟨e⟩⟩))))
  have hclosure (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      localizingClosureProEtale Λ T =
        localizingClosure (constantModelBoundedConstructible Λ T) :=
    (localizingClosure_ctf_equals_bc ℓ T Λ hcoeff).1.2.2.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (X' ↘ Spec (.of k))
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (Y' ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated (X' ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y' :=
    quasiSeparatedSpace_of_quasiSeparated (Y' ↘ Spec (.of k))
  have hp'proper : IsProper p' := by
    rw [← sq.hom_snd]
    infer_instance
  have hp : ProperLocalizingHypotheses Λ p :=
    properHypotheses_coefficientIso e p (properHypotheses_integral ℓ k p F)
  have hp' : ProperLocalizingHypotheses Λ p' :=
    properHypotheses_coefficientIso e p' (properHypotheses_integral ℓ k p' F)
  obtain ⟨hg⟩ := pullback_of_constructible Λ g (pullback_constructible Λ g)
  obtain ⟨hg'⟩ := pullback_of_constructible Λ g' (pullback_constructible Λ g')
  have hK' : localizingClosureProEtale Λ X K := (congrFun (hclosure X) K).mpr hK
  have push := localizingClosure_map _ _ (lowerStar Λ p).rightDerivedFunctor
    (fun M hM ↦ hp.1 ⟨M, hM⟩) (preservesColimit_of_properLocalizingHypotheses Λ p hp) K hK'
  have pull := hg'.localizing ⟨K, hK'⟩
  refine ⟨(congrFun (hclosure Y') _).mp (hg.localizing ⟨_, push⟩),
    (congrFun (hclosure Y') _).mp ?_, ?_⟩
  · exact localizingClosure_map _ _ (lowerStar Λ p').rightDerivedFunctor
      (fun M hM ↦ hp'.1 ⟨M, hM⟩) (preservesColimit_of_properLocalizingHypotheses Λ p' hp') _ pull
  · let := condensedAmbientExchange_isoLocus_triangulated
      (Profinite.padicIntegersRingObj ℓ E) sq
    apply extend_iso _ _ _ _
      (condensedAmbientExchange (Profinite.padicIntegersRingObj ℓ E) sq)
      (composite_sums_small (Profinite.padicIntegersRingObj ℓ E) hp hp' hg hg')
      (fun M hM ↦ properBaseChange_admissible_generators ℓ
        (Profinite.padicIntegersRingObj ℓ E) hadm k p g sq M hM) K hK'
    exact (localizingClosure_exists (Profinite.padicIntegersRingObj ℓ E) X
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X ⊓
        fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M)).2.2.2.1

end AlgebraicGeometry.ProEtale.CondensedRing
