/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ModuleForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FilteredColimit.RightDerivedFunctor

/-!
# Derived pushforward of module objects with finite coefficients commutes with filtered colimits

Let `T` be a finite discrete commutative ring, `Λ = T̲` the condensed ring of continuous maps to
`T` (`Profinite.continuousMapRingObj T`), and `f : X ⟶ Y` a quasi-compact quasi-separated
morphism of schemes. We show that the derived pushforward `R((f)_*⟦Λ⟧)` of module objects over
`Λ_X` commutes with filtered colimits of uniformly bounded below complexes, on cohomology
(`ProEtale.CondensedRing.isColimit_mapCocone_homologyFunctor_rightDerivedFunctor_lowerStar`).

The coefficient ring `Λ_X` is torsion, hence not flat over `ℤ`, so the underlying abelian sheaf of
an injective `Λ_X`-module need not be injective. It is however acyclic for the pushforward of
abelian sheaves (`AlgebraicGeometry.ProEtale.CondensedRing.rightAcyclic_lowerStar_forget_obj`):
through the equivalence `ProEtale.finiteCoefficientModEquivalence` with sheaves of
`T`-modules, it is the restriction of scalars along `ℤ → T` of an injective sheaf of `T`-modules,
which is acyclic for the pushforward of sheaves of `ℤ`-modules
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_restrictScalars_obj`), and sheaves of
`ℤ`-modules compute the same higher direct images as abelian sheaves
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarSheafComposeForget₂Iso`). Hence the higher
direct images of module objects are those of the underlying abelian sheaves
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerStarForgetIso`), and they commute with
filtered colimits (`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`),
the forgetful functor preserving and reflecting filtered colimits. We conclude by the
general statement
`CategoryTheory.Functor.isColimit_mapCocone_Q_comp_rightDerivedFunctor_comp_homologyFunctor`.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ring morphism `ℤ ⟶ T`, between the universe lifts of `ℤ` and `T` to `Type (u + 1)`. -/
noncomputable abbrev uliftIntCast : ULift.{u + 1} ℤ →+* ULift.{u + 1} T :=
  ULift.ringEquiv.symm.toRingHom.comp ((Int.castRingHom T).comp ULift.ringEquiv.toRingHom)

/-- **The underlying abelian sheaf of an injective module object over `Λ_X = p_X^* T̲` is acyclic
for the pushforward of abelian sheaves.** Through `ProEtale.finiteCoefficientModEquivalence`, it
is the restriction of scalars to `ℤ` of an injective sheaf of `T`-modules. -/
theorem rightAcyclic_lowerStar_forget_obj
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) [Injective M] :
    ((f)_*[Ab.{u + 1}]).rightAcyclic
      ((Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) X)).obj M) := fun q ↦ by
  let N := (finiteCoefficientModEquivalence X T).functor.obj M
  have hN := rightAcyclic_lowerStar_restrictScalars_obj (uliftIntCast.{u} T) f N q
  exact (Functor.map_isZero (sheafCompose (ProEt.topology Y)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Ab.{u + 1})) hN).of_iso
    ((rightDerivedLowerStarSheafComposeForget₂Iso (ULift.{u + 1} ℤ) f (q + 1)).app
      ((Sheaf.restrictScalars (ProEt.topology X) (uliftIntCast.{u} T)).obj N)).symm

/-- **Higher direct images of module objects over `Λ_X = p_X^* T̲` are those of the underlying
abelian sheaves**: `(Rᵠf_* M)_ab ≅ Rᵠf_*(M_ab)`, the base change morphism of the classical right
derived functors, invertible because the underlying abelian sheaves of injective module objects
are `f_*`-acyclic (`AlgebraicGeometry.ProEtale.CondensedRing.rightAcyclic_lowerStar_forget_obj`).
-/
noncomputable def rightDerivedLowerStarForgetIso (q : ℕ) :
    ((f)_*⟦Profinite.continuousMapRingObj T⟧).rightDerived q ⋙
        Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) Y) ≅
      Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) X) ⋙
        ((f)_*[Ab.{u + 1}]).rightDerived q :=
  let e : (f)_*⟦Profinite.continuousMapRingObj T⟧ ⋙
        Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) Y) ≅
      Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) X) ⋙ (f)_*[Ab.{u + 1}] :=
    Iso.refl _
  have : IsIso (Functor.rightDerivedBaseChange e.hom q) := by
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange e.hom) :=
      Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
        fun I _ ↦ rightAcyclic_lowerStar_forget_obj T f I
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    infer_instance
  asIso (Functor.rightDerivedBaseChange e.hom q)

variable [QuasiCompact f] [QuasiSeparated f]

/-- **Higher direct images of module objects over `Λ_X = p_X^* T̲` commute with filtered
colimits** indexed by essentially `u + 1`-small categories, for a quasi-compact quasi-separated
morphism `f`: this holds for the underlying abelian sheaves
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`), and the forgetful
functor preserves and reflects these colimits. -/
theorem preservesColimitsOfShape_rightDerived_lowerStar (J : Type v) [Category.{w} J]
    [EssentiallySmall.{u + 1} J] [IsFiltered J] (q : ℕ) :
    PreservesColimitsOfShape J
      (((f)_*⟦Profinite.continuousMapRingObj T⟧).rightDerived q) := by
  have : IsFiltered (SmallModel.{u + 1} J) := IsFiltered.of_equivalence (equivSmallModel J)
  suffices PreservesColimitsOfShape (SmallModel.{u + 1} J)
      (((f)_*⟦Profinite.continuousMapRingObj T⟧).rightDerived q) from
    preservesColimitsOfShape_of_equiv (equivSmallModel J).symm _
  have := ProEtale.preservesColimitsOfShape_rightDerived_lowerStar f (SmallModel.{u + 1} J) q
  have : PreservesColimitsOfShape (SmallModel.{u + 1} J)
      (((f)_*⟦Profinite.continuousMapRingObj T⟧).rightDerived q ⋙
        Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) Y)) :=
    preservesColimitsOfShape_of_natIso (rightDerivedLowerStarForgetIso T f q).symm
  have : ReflectsColimitsOfShape (SmallModel.{u + 1} J)
      (Mod.forget (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) Y)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (Mod.forget (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y))

/-- **The derived pushforward of module objects over `Λ_X = p_X^* T̲` commutes with filtered
colimits of uniformly bounded below complexes, on cohomology.** Let `f` be quasi-compact and
quasi-separated, `J` an essentially small filtered category, `F` a diagram of complexes of
module objects over `Λ_X` strictly concentrated in degrees `≥ a`, and `c` a colimit cocone of
`F`. Then for every `q`, the cocone `Hᵠ(Rf_*(c))` is a colimit cocone. -/
theorem isColimit_mapCocone_homologyFunctor_rightDerivedFunctor_lowerStar
    {J : Type v} [Category.{w} J] [EssentiallySmall.{u + 1} J] [IsFiltered J]
    (F : J ⥤ CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) ℤ)
    (a : ℤ) [∀ j, (F.obj j).IsStrictlyGE a] {c : Cocone F} (hc : IsColimit c) (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ R((f)_*⟦Profinite.continuousMapRingObj T⟧) ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone c)) := by
  have : IsFiltered (SmallModel.{u + 1} J) := IsFiltered.of_equivalence (equivSmallModel J)
  let e := (equivSmallModel.{u + 1} J).symm
  have (q : ℕ) := preservesColimitsOfShape_rightDerived_lowerStar T f (SmallModel.{u + 1} J) q
  have (j : SmallModel.{u + 1} J) : ((e.functor ⋙ F).obj j).IsStrictlyGE a :=
    inferInstanceAs ((F.obj (e.functor.obj j)).IsStrictlyGE a)
  obtain ⟨h⟩ := Functor.isColimit_mapCocone_Q_comp_rightDerivedFunctor_comp_homologyFunctor
    ((f)_*⟦Profinite.continuousMapRingObj T⟧) (e.functor ⋙ F) a (hc.whiskerEquivalence e) q
  exact ⟨IsColimit.ofWhiskerEquivalence e (IsColimit.ofIsoColimit h (Functor.mapCoconeWhisker _))⟩

end AlgebraicGeometry.ProEtale.CondensedRing
