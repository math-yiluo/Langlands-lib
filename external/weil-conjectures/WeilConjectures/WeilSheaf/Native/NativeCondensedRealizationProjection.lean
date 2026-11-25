/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization
public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison

/-!
# Constructibility and the proper projection formula for the condensed realization

For a Weil complex `K` on a separated `k₀`-scheme of finite type `X`, the condensed realization
`(derivedCondensedRealization k₀ l X).obj K` is a bounded constructible complex of
`ℚ̲̄_ℓ`-modules on the geometric fibre `X̄`
(`AlgebraicGeometry.ProEtaleWeilSheaf.boundedConstructible_derivedCondensedRealization`).
Consequently, for a proper morphism `g : Z ⟶ Y` over `k₀`, the projection map of `ḡ` is an
isomorphism on condensed realizations of Weil complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_projectionMap_derivedCondensedRealization`), by the
proper projection formula over `k̄`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Forgetting the `ℚ̄_ℓ`-linear structure of an `ℓ`-adic sheaf and transporting along the
normalized coefficient isomorphism is the condensed model functor. -/
theorem forgetAb_comp_comap_nativeModuleCoefficientIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    AdicSheaf.forgetAb l T ⋙ Mod.comap (nativeModuleCoefficientIso l T).hom =
      (adicSheafEquivCondensedMod l T).functor := by
  simp only [nativeModuleCoefficientIso_eq_condensedRingObjIsoForgetAb]
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- **The proper projection formula** for `ℚ̲̄_ℓ`-coefficients, for schemes `X`, `Y` separated
of finite type over a field `k` given by structure morphisms `a`, `b`, and a proper morphism
`p : X ⟶ Y` over `k`: the projection map `Rp_* K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ Lp^* M)` is an isomorphism
on bounded constructible complexes. This is
`properDirectImage_baseChange_projectionFormula_padicAlgClRingObj` with the schemes over `k`
unbundled. -/
theorem isIso_projectionMap_padicAlgClRingObj_of_isProper (l : ℕ) [Fact l.Prime] {k : Type u}
    [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated a] [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ b = a)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y) M) :
    IsIso (((projectionMap (Profinite.padicAlgClRingObj l) p).app K).app M) := by
  have : LocallyOfFiniteType (Over.mk a).hom := ‹_›
  have : QuasiCompact (Over.mk a).hom := ‹_›
  have : IsSeparated (Over.mk a).hom := ‹_›
  have : LocallyOfFiniteType (Over.mk b).hom := ‹_›
  have : QuasiCompact (Over.mk b).hom := ‹_›
  have : IsSeparated (Over.mk b).hom := ‹_›
  have : IsProper (Over.homMk (U := Over.mk a) (V := Over.mk b) p hp).left := ‹_›
  have e : projectionMap (Profinite.padicAlgClRingObj l)
      (Over.homMk (U := Over.mk a) (V := Over.mk b) p hp).left =
        projectionMap (Profinite.padicAlgClRingObj l) p :=
    rfl
  rw [← e]
  exact (properDirectImage_baseChange_projectionFormula_padicAlgClRingObj l (X := Over.mk a)
    (Y := Over.mk b) (X' := Over.mk a) (Y' := Over.mk b) (Over.homMk p hp)).2.2 K M hK hM

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- The condensed realization of a Weil complex on a separated `k₀`-scheme `X` of finite type is
bounded constructible on the geometric fibre `X̄`. By `weil_geometric_hom_constructibility` the
realization along the normalized coefficient isomorphism satisfies the constant-model
predicate, which agrees with bounded constructibility on the Noetherian scheme `X̄`
(`adicConstructibilityPredicateComparison`); the normalized coefficient isomorphism is the one
underlying the condensed model (`nativeModuleCoefficientIso_eq_condensedRingObjIsoForgetAb`). -/
theorem boundedConstructible_derivedCondensedRealization [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (hK : WeilComplex.objectProperty k₀ l X K) :
    ProEtale.boundedConstructible
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      ((derivedCondensedRealization k₀ l X).obj K) := by
  let aX := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : LocallyOfFiniteType aX := inferInstance
  have : QuasiCompact aX := inferInstance
  have : CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace aX
  have : IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian aX
  have h := ((weil_geometric_hom_constructibility k₀ l X).1 K).1 hK
  rw [← (ProEtale.adicConstructibilityPredicateComparison l _ _ .algebraicClosure).2] at h
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  exact ObjectProperty.prop_of_iso _
    ((Functor.mapDerivedCategoryNatIso (eqToIso
      (ProEtale.forgetAb_comp_comap_nativeModuleCoefficientIso l _))).app
        (U.mapDerivedCategory.obj K) ≪≫
      (U.mapDerivedCategoryCompIso _).app K) h

/-- **The proper projection formula for condensed realizations of Weil complexes**: for a
proper morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type, the projection map
`Rḡ_* A ⊗ᴸ B ⟶ Rḡ_*(A ⊗ᴸ Lḡ^* B)` of the base change `ḡ : Z̄ ⟶ Ȳ` to `k̄` is an isomorphism on
the condensed realizations `A`, `B` of Weil complexes `M` on `Z` and `L` on `Y`. These are
bounded constructible (`boundedConstructible_derivedCondensedRealization`) and `ḡ` is a proper
morphism of separated `k̄`-schemes of finite type, so this is the proper projection formula
(`ProEtale.CondensedRing.isIso_projectionMap_padicAlgClRingObj_of_isProper`). -/
theorem isIso_projectionMap_derivedCondensedRealization [Fact (ringChar k₀ ≠ l)]
    {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]
    (M : WeilComplex k₀ l Z) (L : WeilComplex k₀ l Y) :
    IsIso (((ProEtale.CondensedRing.projectionMap (Profinite.padicAlgClRingObj l)
      (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))).app
        ((derivedCondensedRealization k₀ l Z).obj M.obj)).app
          ((derivedCondensedRealization k₀ l Y).obj L.obj)) := by
  have : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
    ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
        exact CharP.prime_ringChar k₀⟩
  have : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k₀ (AlgebraicClosure k₀)]
        exact Fact.out⟩
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsSeparated (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsProper (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) g
      (comp_over g (Spec (CommRingCat.of k₀))) inferInstance
  exact ProEtale.CondensedRing.isIso_projectionMap_padicAlgClRingObj_of_isProper l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _) _ _
    (boundedConstructible_derivedCondensedRealization k₀ l Z M.obj M.property)
    (boundedConstructible_derivedCondensedRealization k₀ l Y L.obj L.property)

end AlgebraicGeometry.ProEtaleWeilSheaf
