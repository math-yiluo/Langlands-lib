/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveHom
import WeilConjectures.WeilSheaf.Native.NativeCoefficientTensorComparison
import WeilConjectures.WeilSheaf.Native.NativeGeometricHomComparison
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRowHomComparison

/-!
# The derived internal hom of Weil complexes is a Weil complex

For Weil complexes `K` and `L` on a separated `k₀`-scheme of finite type `X`, the derived internal
hom `RHom(K, L)` of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`) is
again a Weil complex (`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom`), the Weil analogue
of `proposition-six-operations-dctf--15`.

Forget the Weil structure and pass to condensed `ℚ̲̄_ℓ`-modules on the geometric fibre `X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget`). This functor detects Weil complexes
among the objects of the derived category, and it carries `RHom(K, L)` to the derived hom of the
underlying condensed complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_nativeGeometricForget_derivedHom_iso`). That derived
hom is bounded constructible
(`AlgebraicGeometry.ProEtaleWeilSheaf.weil_geometric_hom_constructibility`).

## Implementation notes

`AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison` states the same
comparison, but its proof goes through the whole closed symmetric structure on Weil complexes of
`AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`, whose symmetry rests on a disputed
`sorry` (`native_weil_tensor_ringed_swap_localization`). The comparison of internal homs needs
neither the Weil tensor product nor its symmetry, so it is rebuilt here from the internal-hom
models alone (`native_two_injective_hom_model`, `native_row_hom_comparison`) and the closed
structure of the underlying `ℓ`-adic sheaves (`native_ordinary_closed_tensor_models`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- For an equivalence `E` and adjunctions `T ⊣ H`, `T' ⊣ H'` whose left adjoints are intertwined
by `E`, the right adjoints are intertwined as well: `E (H Q) ≅ H' (E Q)`. -/
private noncomputable def homComparisonOfEquivalence
    {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)
    {T H : C ⥤ C} {T' H' : D ⥤ D} (a : T ⊣ H) (b : T' ⊣ H')
    (τ : T ⋙ E.functor ≅ E.functor ⋙ T') (Q : C) :
    E.functor.obj (H.obj Q) ≅ H'.obj (E.functor.obj Q) :=
  E.functor.mapIso (H.mapIso (E.unitIso.app Q)) ≪≫
    E.functor.mapIso
      ((conjugateIsoEquiv (a.comp E.toAdjunction) (E.toAdjunction.comp b) τ.symm).app
        (E.functor.obj Q)) ≪≫
    E.counitIso.app (H'.obj (E.functor.obj Q))

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Forgetting the Weil structure commutes with the derived internal hom** (blueprint:
`lem-sf-native-geometric-hom-comparison`): the underlying condensed complex on the geometric
fibre `X̄` of `RHom(K, L)` is the derived hom of the underlying complexes of `K` and `L`. This is
`nativeGeometricForget_derivedHomComparison`, proved without the Weil tensor product. -/
theorem nonempty_nativeGeometricForget_derivedHom_iso
    (K L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    Nonempty ((nativeGeometricForget k₀ l X).obj ((derivedHom k₀ l X L).obj (op K)) ≅
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
  obtain ⟨m⟩ := native_two_injective_hom_model (k₀ := k₀) (l := l) (X := X)
  obtain ⟨M, η, -, -, -, -⟩ := native_row_hom_comparison k₀ l X m
  obtain ⟨S, β, -, hS⟩ := native_ordinary_closed_tensor_models l Y M.ordinaryHom
    M.ordinaryRepresentatives
  let P := (nativeForget k₀ l X).obj K
  let Q := (nativeForget k₀ l X).obj L
  obtain ⟨τ⟩ := nativeCoefficient_tensorComparison l Y M.ordinaryHom
    M.ordinaryRepresentatives S β hS P
  let e := homComparisonOfEquivalence E (S.adjunction P)
    (ProEtale.CondensedRing.derivedTensorHomAdjunction
      (Profinite.padicAlgClRingObj l) (E.functor.obj P)) τ Q
  exact ⟨F.mapDerivedCategory.mapIso
    ((nativeForget k₀ l X).mapIso ((M.nativeModel L).symm.app (op K)) ≪≫
      η.app (op K, L)) ≪≫ e⟩

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The derived internal hom preserves Weil complexes** (blueprint: `prose-10-20`,
internal-Hom paragraph, with `proposition-six-operations-dctf--15`): for Weil complexes `K` and `L`,
the derived internal hom `RHom(K, L)` of pro-étale Weil sheaves is a Weil complex. -/
theorem objectProperty_derivedHom (K L : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X L.obj).obj (op K.obj)) := by
  obtain ⟨hcrit, -, hhom⟩ := ProEtaleWeilSheaf.weil_geometric_hom_constructibility k₀ l X
  obtain ⟨e⟩ := ProEtaleWeilSheaf.nonempty_nativeGeometricForget_derivedHom_iso k₀ l X K.obj L.obj
  have := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (Profinite.padicAlgClRingObj l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).2.1
  exact (hcrit _).2 (ObjectProperty.prop_of_iso _ e.symm (hhom K L).2.2.1)

end AlgebraicGeometry.WeilComplex
