/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-!
# Bounded constructibility in the two models of `ℓ`-adic sheaves

The equivalence `D(AdicSheaf ℓ T) ≌ D(Mod_{Λ_T})` between the derived categories of the two
models of `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicSheafDerivedEquivCondensedMod`)
identifies the bounded constructible complexes of the two models, for `T` separated of finite type
over an algebraic closure of a finite field
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_iff_boundedConstructible`). The coefficient
realization used by the native forgetful functors of Weil complexes is this comparison
(`AlgebraicGeometry.ProEtale.forgetAbCompComapNativeModuleCoefficientIso`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The chosen native coefficient isomorphism is the coefficient isomorphism
`condensedRingObjIsoForgetAb` underlying the comparison of the two models of `ℓ`-adic
sheaves. -/
theorem nativeModuleCoefficientIso_eq_condensedRingObjIsoForgetAb (T : Scheme.{u}) :
    nativeModuleCoefficientIso ℓ T = condensedRingObjIsoForgetAb ℓ T :=
  nativeModuleCoefficientIso_eq_nativeEncodingCoefficientIso ℓ T

/-- The native coefficient realization `forgetAb` followed by restriction of scalars along the
native coefficient isomorphism is the comparison functor of the two models of `ℓ`-adic
sheaves. -/
noncomputable def forgetAbCompComapNativeModuleCoefficientIso (T : Scheme.{u}) :
    AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (nativeModuleCoefficientIso ℓ T).hom ≅
      (adicSheafEquivCondensedMod ℓ T).functor :=
  Functor.isoWhiskerLeft _ (Mod.comapCongr
    (congrArg Iso.hom (nativeModuleCoefficientIso_eq_condensedRingObjIsoForgetAb ℓ T)))

/-- Over a separated scheme of finite type over an algebraic closure of a finite field, an
`ℓ`-adic sheaf is constructible if and only if its image in the condensed model is
constructible. -/
theorem isAdicConstructibleSheaf_iff_isConstructibleModuleObject (k₀ k : Type u) [Field k₀]
    [Finite k₀] [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k] [Fact (ringChar k₀ ≠ ℓ)]
    (T : Over (Spec (CommRingCat.of k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (M : AdicSheaf ℓ T.left) :
    IsAdicConstructibleSheaf M ↔
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T.left)
        ((adicSheafEquivCondensedMod ℓ T.left).functor.obj M) := by
  let : T.left.Over (Spec (CommRingCat.of k)) := ⟨T.hom⟩
  have : IsSeparated (T.left ↘ Spec (CommRingCat.of k)) := inferInstanceAs (IsSeparated T.hom)
  have : LocallyOfFiniteType (T.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType T.hom)
  have : QuasiCompact (T.left ↘ Spec (CommRingCat.of k)) := inferInstanceAs (QuasiCompact T.hom)
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  obtain ⟨E, hE, -, -, -, -, hCons, -⟩ :=
    nativeModuleConstructibilityComparison k₀ k ℓ (Ne.symm Fact.out) T.left
  let e := (nativeOrdinaryPresentation ℓ T.left).unitIso.symm.app _ ≪≫
    (forgetAbCompComapNativeModuleCoefficientIso ℓ T.left).app M
  rw [hCons M, hE, ← (adicConstructibilityPredicateComparison ℓ T.left
    (Profinite.padicAlgClRingObj ℓ) .algebraicClosure).1]
  exact ⟨fun h ↦ constructible_of_iso e h, fun h ↦ constructible_of_iso e.symm h⟩

/-- **Bounded constructibility in the two models**: a complex of `ℓ`-adic sheaves on a separated
scheme of finite type `T` over an algebraic closure `k` of a finite field `k₀` is bounded with
constructible cohomology if and only if its image in the condensed model is bounded
constructible. -/
theorem boundedConstructibleAdic_iff_boundedConstructible (k₀ k : Type u) [Field k₀] [Finite k₀]
    [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k] [Fact (ringChar k₀ ≠ ℓ)]
    (T : Over (Spec (CommRingCat.of k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (K : _root_.DerivedCategory (AdicSheaf ℓ T.left)) :
    DerivedCategory.boundedConstructibleAdic ℓ T.left K ↔
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T.left)
        ((adicSheafDerivedEquivCondensedMod ℓ T.left).functor.obj K) := by
  let G := (adicSheafEquivCondensedMod ℓ T.left).functor
  refine and_congr ⟨G.bounded_mapDerivedCategory_obj, G.bounded_of_bounded_mapDerivedCategory_obj⟩
    (forall_congr' fun n ↦ ?_)
  let e := (G.mapDerivedCategoryHomologyFunctorIso n).app K
  exact (isAdicConstructibleSheaf_iff_isConstructibleModuleObject ℓ k₀ k T _).trans
    ⟨fun h ↦ constructible_of_iso e h, fun h ↦ constructible_of_iso e.symm h⟩

end AlgebraicGeometry.ProEtale
