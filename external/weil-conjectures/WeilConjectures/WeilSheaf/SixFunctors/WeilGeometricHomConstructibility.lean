/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Geometric constructibility and internal Hom for native Weil complexes

Source: blueprint prose-10-20, internal-Hom paragraph;
lemma-constructible-sheaves, opening equality Dctf = Dbc; proposition-six-operations-dctf--15.
(blueprint: lem-sf-weil-geometric-hom-constructibility).

The forgetful functor includes the canonical coefficient realization from native modules
into internal modules over the finite-subextension-valued condensed coefficient ring.
All derived categories are ordinary localizations. Internal Hom is the ambient relative
sheaf Hom; its inputs need not be lisse or perfect on the site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

set_option synthInstance.maxSize 2048

/-- Termwise forgetting Frobenius, scalar linearity, and transport along the canonical
coefficient realization theta from R_X to B_X. This uses precisely the internal-module
presentation underlying nativeToOrdinaryModules, before its sectionwise presentation.
Source: prose-10-20, internal-Hom paragraph, and the module comparison
(blueprint: lem-sf-weil-geometric-hom-constructibility). -/
abbrev nativeGeometricForget (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] (X₀ : Scheme.{u})
    [X₀.Over (Spec (CommRingCat.of k₀))] :=
  nativeForget k₀ ℓ X₀ ⋙
    (ProEtale.AdicSheaf.forgetAb ℓ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⋙
      Mod.comap (ProEtale.nativeModuleCoefficientIso ℓ
        (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber).hom).mapDerivedCategory

set_option linter.style.haveILetI false in
/-- The geometric cohomology criterion, with exact support intervals, and finiteness of
relative derived sheaf Hom between arbitrary native Weil complexes.
Source: prose-10-20, internal-Hom paragraph; lemma-constructible-sheaves,
opening equality Dctf = Dbc; proposition-six-operations-dctf--15, finite-subextension Qlbar case.
(blueprint: lem-sf-weil-geometric-hom-constructibility).

Proof:
1. Base change preserves separatedness, local finite type and quasi-compactness
   (lem-pod-separated-finite-type-base-change). The geometric fibre is therefore separated
   of finite type over the algebraic closure, with characteristic different from ell.
2. By lem-sf-weil-native-closed-forgetful, cohomology commutes with forgetting the
   invertible Frobenius structure. The forgetful functor reflects zero, since the zero
   underlying module has a unique structure. The exact module equivalence of
   lem-sf-weil-verdier-module-constructibility-comparison identifies native finite-free
   restrictions with finite scalar models, using the same strata and covers. Thus
   vanishing outside each prescribed interval and constructibility in each degree are
   equivalent. Existence of an interval gives the bounded constructibility criterion.
3. For two Weil complexes the criterion gives geometric bounded constructibility. The
   field-coefficient equality Dctf = Dbc of lemma-constructible-sheaves makes each input
   have finite Tor amplitude, without asserting site-perfectness.
4. Finite type over a field makes the geometric fibre Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Apply
   lem-sfb-adic-constructibility-predicate-comparison to pass to the bounded constructible
   predicate of sk-def-sfb-bounded-constructible. The finite-subextension Qlbar case of
   proposition-six-operations-dctf--15 gives bounded constructibility of the ambient relative
   internal Hom. Return through the predicate comparison and use Dctf = Dbc once more
   to get finite Tor amplitude. This applies to both arbitrary inputs, with no lissity
   hypothesis, and takes no Frobenius invariants of global Hom groups. -/
theorem weil_geometric_hom_constructibility
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u})
    [X₀.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X₀ ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X₀ ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X₀ ↘ Spec (CommRingCat.of k₀))] :
    (∀ M : DerivedCategory (ProEtaleWeilSheaf k₀ ℓ X₀),
      WeilComplex.objectProperty k₀ ℓ X₀ M ↔
        ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
          ((nativeGeometricForget k₀ ℓ X₀).obj M)) ∧
    (∀ (M : DerivedCategory (ProEtaleWeilSheaf k₀ ℓ X₀)) (a b : ℤ),
      (∀ n : ℤ, n < a ∨ b < n →
        IsZero ((DerivedCategory.homologyFunctor _ n).obj M)) ↔
      ∀ n : ℤ, n < a ∨ b < n →
        IsZero ((DerivedCategory.homologyFunctor _ n).obj
          ((nativeGeometricForget k₀ ℓ X₀).obj M))) ∧
    (∀ K L : WeilComplex k₀ ℓ X₀,
      DerivedCategory.finiteTorAmplitude _ ((nativeGeometricForget k₀ ℓ X₀).obj K.obj) ∧
      DerivedCategory.finiteTorAmplitude _ ((nativeGeometricForget k₀ ℓ X₀).obj L.obj) ∧
      (ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⊓
        DerivedCategory.finiteTorAmplitude _)
        (((ProEtale.CondensedRing.derivedHom (Profinite.padicAlgClRingObj ℓ)
          (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          (op ((nativeGeometricForget k₀ ℓ X₀).obj K.obj))).obj
          ((nativeGeometricForget k₀ ℓ X₀).obj L.obj))) := by
  let X := (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let aX := (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  letI : X.Over (Spec (CommRingCat.of (AlgebraicClosure k₀))) := ⟨aX⟩
  letI : LocallyOfFiniteType aX := inferInstance
  letI : QuasiCompact aX := inferInstance
  letI : IsSeparated aX :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  letI : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian aX
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace aX }
  letI : IsSeparated (X ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change IsSeparated aX
    infer_instance
  letI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change LocallyOfFiniteType aX
    infer_instance
  letI : QuasiCompact (X ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change QuasiCompact aX
    infer_instance
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := ProEtale.AdicSheaf.forgetAb ℓ X ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso ℓ X).hom
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ ℓ X₀)
  obtain ⟨E, hE, _, _, _, _, hCons, _⟩ :=
    ProEtale.nativeModuleConstructibilityComparison k₀ (AlgebraicClosure k₀) ℓ
      (Ne.symm (Fact.out : ringChar k₀ ≠ ℓ)) X
  rw [hE] at hCons
  letI : (F ⋙ (ProEtale.nativeOrdinaryPresentation ℓ X).functor).Faithful := by
    change (ProEtale.nativeToOrdinaryModules ℓ X).Faithful
    rw [← hE]
    infer_instance
  letI : F.Faithful := Functor.Faithful.of_comp F
    (ProEtale.nativeOrdinaryPresentation ℓ X).functor
  let H := U ⋙ F
  let e := (U.mapDerivedCategoryCompIso F).symm
  have hPred := ProEtale.adicConstructibilityPredicateComparison ℓ X Λ
    (.algebraicClosure)
  have hIso : ∀ {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}, (M ≅ N) →
      (ProEtale.IsConstantModelConstructible Λ X M ↔
        ProEtale.IsConstantModelConstructible Λ X N) := by
    intro M N i
    rw [← hPred.1 M, ← hPred.1 N]
    exact ⟨fun h ↦ _root_.constructible_of_iso i h,
      fun h ↦ _root_.constructible_of_iso i.symm h⟩
  have hF : ∀ M, ProEtale.IsAdicConstructibleSheaf M ↔
      ProEtale.IsConstantModelConstructible Λ X (F.obj M) := by
    intro M
    exact (hCons M).trans (hIso
      ((ProEtale.nativeOrdinaryPresentation ℓ X).unitIso.symm.app (F.obj M)))
  have hHom (M : DerivedCategory (ProEtaleWeilSheaf k₀ ℓ X₀)) (n : ℤ) :
      H.obj ((DerivedCategory.homologyFunctor _ n).obj M) ≅
        (DerivedCategory.homologyFunctor _ n).obj
          ((nativeGeometricForget k₀ ℓ X₀).obj M) :=
    (H.mapDerivedCategoryHomologyFunctorIso n).app M ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso (e.app M)
  have hBound (M : DerivedCategory (ProEtaleWeilSheaf k₀ ℓ X₀)) :
      DerivedCategory.TStructure.t.bounded M ↔
        DerivedCategory.TStructure.t.bounded
          ((nativeGeometricForget k₀ ℓ X₀).obj M) := by
    constructor
    · intro h
      exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.app M)
        (H.bounded_mapDerivedCategory_obj h)
    · intro h
      exact H.bounded_of_bounded_mapDerivedCategory_obj
        (DerivedCategory.TStructure.t.bounded.prop_of_iso (e.symm.app M) h)
  have hCriterion : ∀ M : DerivedCategory (ProEtaleWeilSheaf k₀ ℓ X₀),
      WeilComplex.objectProperty k₀ ℓ X₀ M ↔
        ProEtale.constantModelBoundedConstructible Λ X
          ((nativeGeometricForget k₀ ℓ X₀).obj M) := by
    intro M
    change (_ ∧ ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      (U.obj ((DerivedCategory.homologyFunctor _ n).obj M))) ↔ (_ ∧ _)
    exact and_congr (hBound M) (forall_congr' fun n ↦
      (hF _).trans (hIso (hHom M n)))
  refine ⟨hCriterion, ?_, ?_⟩
  · intro M a b
    constructor
    · intro h n hn
      exact (H.map_isZero (h n hn)).of_iso (hHom M n).symm
    · intro h n hn
      have hz := (h n hn).of_iso (hHom M n)
      rw [IsZero.iff_id_eq_zero] at hz ⊢
      exact H.map_injective (by simpa using hz)
  · have : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
      ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
          exact CharP.prime_ringChar k₀⟩
    letI : Fact (ringChar (AlgebraicClosure k₀) ≠ ℓ) :=
      ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
          exact Fact.out⟩
    letI : CharP (AlgebraicClosure k₀) (ringChar (AlgebraicClosure k₀)) :=
      ringChar.charP _
    have hHeart := ProEtale.coefficientHeart ℓ (Profinite.padicAlgClCondensedRing ℓ)
      (Or.inr rfl) (AlgebraicClosure k₀) (ringChar (AlgebraicClosure k₀))
      (Fact.out : ringChar (AlgebraicClosure k₀) ≠ ℓ) X
    have hTor : ∀ M, ProEtale.constantModelBoundedConstructible Λ X M →
        DerivedCategory.finiteTorAmplitude _ M := by
      intro M hM
      have hm : (ProEtale.constantModelBoundedConstructible Λ X ⊓
          DerivedCategory.finiteTorAmplitude _) M := by
        rw [hHeart.1]
        exact hM
      exact hm.2
    let Y : Over (Spec (CommRingCat.of (AlgebraicClosure k₀))) := Over.mk aX
    letI : LocallyOfFiniteType Y.hom := by change LocallyOfFiniteType aX; infer_instance
    letI : QuasiCompact Y.hom := by change QuasiCompact aX; infer_instance
    letI : IsSeparated Y.hom := by change IsSeparated aX; infer_instance
    letI : (ProEtale.boundedConstructible (ProEtale.condensedRingObj Λ X)).IsMonoidalClosed :=
      ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible ℓ Y
    intro K L
    have hK := (hCriterion K.obj).mp K.property
    have hL := (hCriterion L.obj).mp L.property
    have hR : ProEtale.constantModelBoundedConstructible Λ X
        (((ProEtale.CondensedRing.derivedHom Λ X).obj
          (op ((nativeGeometricForget k₀ ℓ X₀).obj K.obj))).obj
          ((nativeGeometricForget k₀ ℓ X₀).obj L.obj)) := by
      rw [← hPred.2] at hK hL ⊢
      exact (ProEtale.boundedConstructible (ProEtale.condensedRingObj Λ X)).prop_ihom hK hL
    exact ⟨hTor _ hK, hTor _ hL, hR, hTor _ hR⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
