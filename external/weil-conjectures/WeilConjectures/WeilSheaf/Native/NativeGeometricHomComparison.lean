/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
import WeilConjectures.WeilSheaf.Native.NativeCoefficientTensorComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Internal Hom under the native geometric realization

Source: current blueprint, `lem-fix-weil-operations.proof.md`, internal-Hom paragraph;
the coefficient realization and native closed-forgetful comparison.
(blueprint: lem-sf-native-geometric-hom-comparison).

This is an ambient derived-object comparison. It asserts no constructibility,
boundedness, dualizing-object identification, or biduality.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

private noncomputable def homComparisonOfEquivalence
    {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)
    {T H : C ⥤ C} {T' H' : D ⥤ D} (a : T ⊣ H) (b : T' ⊣ H')
    (τ : T ⋙ E.functor ≅ E.functor ⋙ T') (Q : C) :
    E.functor.obj (H.obj Q) ≅ H'.obj (E.functor.obj Q) := by
  let η := conjugateIsoEquiv (a.comp E.toAdjunction) (E.toAdjunction.comp b) τ.symm
  exact E.functor.mapIso (H.mapIso (E.unitIso.app Q)) ≪≫
    E.functor.mapIso (η.app (E.functor.obj Q)) ≪≫
    E.counitIso.app (H'.obj (E.functor.obj Q))

/-- Native geometric realization carries the actual product-total derived internal Hom
to the internal Hom over the realized condensed coefficient ring.

Source: current blueprint, `lem-fix-weil-operations.proof.md`, internal-Hom paragraph;
`lem-sf-weil-native-closed-forgetful`, comparison of product-total Hom; and
`lem-sf-weil-verdier-module-constructibility-comparison`, coefficient-module equivalence.
(blueprint: lem-sf-native-geometric-hom-comparison).

Proof: Let Y be the geometric fiber. Forget Frobenius first. The exact orbit-sum induction
is left adjoint to this forgetting functor, so forgetting preserves K-injective complexes.
The native closed-forgetful comparison identifies the forgotten native product-Hom with
the ordinary relative derived sheaf Hom, naturally in its derived arguments. This uses
internal sheaf Hom with contragredient action, without taking invariant global Hom groups.
Next apply F = AdicSheaf.forgetAb followed by comap along nativeModuleCoefficientIso.
The coefficient realization identifies the two sheaves of rings on the same site. Scalar
linearity is recovered from the constant coefficient sections, so F is an exact equivalence
of module categories. Its relative tensor comparison identifies pure tensors, hence also
evaluation. The inverse equivalence preserves acyclic complexes, and the tensor comparison
shows that F preserves K-flat resolutions; equivalences also preserve K-injective resolutions
and products. Apply F to the product-Hom complex on these representatives. The closed
adjunction, with the same evaluation, identifies it with the ordinary derived internal Hom
over the condensed coefficient ring: both represent the same relative tensor functor.
Uniqueness of right adjoints gives inverse comparison maps, natural on derived morphisms.
Compose this coefficient comparison with the forgotten native Hom comparison. The resulting
object on the left is exactly nativeGeometricForget applied to derivedHom. No finite rank
or boundedness hypothesis is used, so zero objects, empty fibers, shifts, and arbitrary
unbounded complexes are included. -/
theorem nativeGeometricForget_derivedHomComparison
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (K L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    Nonempty ((nativeGeometricForget k₀ l X).obj
        ((derivedHom k₀ l X L).obj (op K)) ≅
      ((ProEtale.CondensedRing.derivedHom (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
        (op ((nativeGeometricForget k₀ l X).obj K))).obj
        ((nativeGeometricForget k₀ l X).obj L)) := by
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let F := ProEtale.AdicSheaf.forgetAb l Y ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom
  have : (ProEtale.AdicSheaf.forgetAb l Y).IsEquivalence :=
    ProEtale.nativeScalarForgetting_isEquivalence l Y
  have : (Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Y).hom).isEquivalence_functor
  have : F.IsEquivalence := inferInstance
  let E := F.mapDerivedCategory.asEquivalence
  obtain ⟨C, _⟩ := (native_closed_forgetful k₀ l X).2.2.2.2
  let P := (nativeForget k₀ l X).obj K
  let Q := (nativeForget k₀ l X).obj L
  obtain ⟨τ⟩ := nativeCoefficient_tensorComparison l Y C.homModels.ordinaryHom
    C.homModels.ordinaryRepresentatives C.ordinaryClosed C.ordinarySymmetry
    C.ordinaryTensorModels P
  let e := homComparisonOfEquivalence E (C.ordinaryClosed.adjunction P)
    (ProEtale.CondensedRing.derivedTensorHomAdjunction
      (Profinite.padicAlgClRingObj l) (E.functor.obj P)) τ Q
  exact ⟨F.mapDerivedCategory.mapIso
    ((nativeForget k₀ l X).mapIso ((C.homModels.nativeModel L).symm.app (op K)) ≪≫
      C.homComparison.app (op K, L)) ≪≫ e⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
