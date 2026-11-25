/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointExceptionalDatum
public import WeilConjectures.WeilSheaf.CondensedWeilPrerequisites
public import WeilConjectures.WeilSheaf.CondensedWeilFrobeniusBounded
public import WeilConjectures.WeilSheaf.UpperShriekWeilDatum

/-!
# The exceptional datum in the condensed model

The framework `Endofunctor.IsoAlgebra.exists_forget_obj_iso_isWeilEquivariant_rightWeilDatum`
instantiated in the condensed model of Weil sheaves (`IsoAlgebra ((Fr⁻¹)_*)` on condensed module
objects over `ℚ̲̄_ℓ`), for the proper morphism `ḡ : Z̄ ⟶ Ȳ` of the compactification of `f̄`:
- the bounded constructible complexes are stable under shifts
  (`AlgebraicGeometry.ProEtale.boundedConstructible_shift`), preserved by the Frobenius
  (`boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff`) and the derived
  direct image preserves bounded below coproducts
  (`preservesColimit_discrete_rightDerivedFunctor_condensedLowerStar`);
- hence the Weil derived direct image on bounded constructible condensed Weil complexes is a left
  adjoint as soon as the geometric one is
  (`AlgebraicGeometry.WeilComplex.isLeftAdjoint_condensedWeilLowerStar`), and the underlying
  object of its right adjoint carries the Frobenius structure to the right Weil datum of the
  geometric adjunction
  (`AlgebraicGeometry.WeilComplex.exists_condensedForget_obj_iso_isWeilEquivariant_rightWeilDatum`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtale

/-- Bounded constructible complexes of condensed module objects are stable under shifts. -/
theorem boundedConstructible_shift (Y : Scheme.{u})
    (K : _root_.DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y))) (n : ℤ)
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y) K) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) Y) (K⟦n⟧) :=
  ⟨ObjectProperty.le_shift _ n K hK.1, fun m ↦
    IsConstructibleModuleObject.of_iso
      (((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso n m (n + m) rfl).app K).symm
      (hK.2 (n + m))⟩

end ProEtale

namespace WeilComplex

open ProEtale

attribute [local instance] Compactification.over

attribute [local instance 1100] CategoryTheory.instOverClass

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

variable (k₀) in
/-- The condensed Frobenius `(Fr⁻¹)_*` of a `k₀`-scheme `S`, on condensed module objects over
`ℚ̲̄_ℓ` on the geometric fibre `S̄`. -/
noncomputable abbrev condensedFrobenius (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))] :=
  CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
    (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv

instance (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))] :
    (condensedFrobenius k₀ l S).IsEquivalence :=
  (CondensedRing.lowerStarEquivalenceOfIso (Profinite.padicAlgClRingObj l)
    (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).isEquivalence_functor

variable (k₀) in
/-- Bounded constructible complexes on the geometric fibre `S̄`, condensed model. -/
noncomputable abbrev condensedBoundedConstructible (S : Scheme.{u})
    [S.Over (Spec (CommRingCat.of k₀))] :=
  boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
    (S ↘ Spec (CommRingCat.of k₀)).geometricFiber)

variable (k₀) in
/-- Bounded constructible condensed Weil complexes on `S`: Weil complexes of the condensed
model whose underlying complex is bounded constructible. -/
noncomputable abbrev condensedWeilObjectProperty (S : Scheme.{u})
    [S.Over (Spec (CommRingCat.of k₀))] :
    ObjectProperty (_root_.DerivedCategory (IsoAlgebra (condensedFrobenius k₀ l S))) :=
  fun M ↦ condensedBoundedConstructible k₀ l S
    ((IsoAlgebra.forget _).mapDerivedCategory.obj M)

instance : IsProper (shriekCompactification k₀ f).g := (shriekCompactification k₀ f).isProper

set_option linter.style.show false in
instance : IsSeparated ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)) := by
  show IsSeparated ((shriekCompactification k₀ f).g ≫ (Y ↘ Spec (CommRingCat.of k₀)))
  infer_instance

set_option linter.style.show false in
instance : LocallyOfFiniteType ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)) := by
  show LocallyOfFiniteType ((shriekCompactification k₀ f).g ≫ (Y ↘ Spec (CommRingCat.of k₀)))
  infer_instance

set_option linter.style.show false in
instance : QuasiCompact ((shriekCompactification k₀ f).Z ↘ Spec (CommRingCat.of k₀)) := by
  show QuasiCompact ((shriekCompactification k₀ f).g ≫ (Y ↘ Spec (CommRingCat.of k₀)))
  infer_instance

/-- Bounded constructible condensed Weil complexes are closed under isomorphisms. -/
instance (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))] :
    (condensedWeilObjectProperty k₀ l S).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ ObjectProperty.prop_of_iso (condensedBoundedConstructible k₀ l S)
    ((IsoAlgebra.forget _).mapDerivedCategory.mapIso e) h⟩

variable (k₀) in
/-- The base change `ḡ : Z̄ ⟶ Ȳ` of the proper part of the compactification. -/
noncomputable abbrev compactificationProperMap :=
  Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).g
    (comp_over (shriekCompactification k₀ f).g (Spec (CommRingCat.of k₀)))

variable (k₀) in
/-- The Frobenius exchange of the condensed pushforward along `ḡ`. -/
noncomputable abbrev condensedProperExchange :=
  CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj l)
    (shriekCompactification k₀ f).g
    (comp_over (shriekCompactification k₀ f).g (Spec (CommRingCat.of k₀)))

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
variable (k₀) in
/-- The Weil derived direct image along `g` in the condensed model preserves bounded
constructible condensed Weil complexes, as soon as the geometric one preserves bounded
constructible complexes (`hR`). -/
theorem condensedWeilObjectProperty_rightDerivedFunctor
    (hR : ∀ K, condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z K →
      condensedBoundedConstructible k₀ l Y
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (compactificationProperMap k₀ f)).rightDerivedFunctor.obj K))
    (M : _root_.DerivedCategory (IsoAlgebra (condensedFrobenius k₀ l (shriekCompactification k₀ f).Z)))
    (hM : condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z M) :
    condensedWeilObjectProperty k₀ l Y
      ((IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor.obj M) :=
  ObjectProperty.prop_of_iso (condensedBoundedConstructible k₀ l Y)
    ((IsoAlgebra.derivedForgetCommIso (condensedProperExchange k₀ l f)).app M).symm (hR _ hM)

set_option linter.style.longLine false in
variable (k₀) in
/-- **The Weil derived direct image is a left adjoint in the condensed model**, as soon as the
geometric derived direct image on bounded constructible complexes is. -/
theorem isLeftAdjoint_condensedWeilLowerStar
    (hR : ∀ K, condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z K →
      condensedBoundedConstructible k₀ l Y
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (compactificationProperMap k₀ f)).rightDerivedFunctor.obj K))
    (hadj : ((condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
      (condensedBoundedConstructible k₀ l Y)
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (compactificationProperMap k₀ f)).rightDerivedFunctor hR).IsLeftAdjoint) :
    ((condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
      (condensedWeilObjectProperty k₀ l Y)
      (IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor
      (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f hR)).IsLeftAdjoint := by
  have : IsProper (shriekCompactification k₀ f).g := (shriekCompactification k₀ f).isProper
  have : IsProper (compactificationProperMap k₀ f) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
      (shriekCompactification k₀ f).g _ ‹_›
  exact IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor
    (condensedProperExchange k₀ l f) _ _ (fun _ hK ↦ hK.1)
    (fun K n hK ↦ boundedConstructible_shift l _ K n hK)
    (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
      (shriekCompactification k₀ f).Z)
    (fun K hK ↦ (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)
    hR hadj
    (preservesColimit_discrete_rightDerivedFunctor_condensedLowerStar l
      (compactificationProperMap k₀ f))
    (condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z)
    (condensedWeilObjectProperty k₀ l Y) (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f hR)

set_option linter.style.longLine false in
variable (k₀) in
/-- **The Frobenius structure of the Weil `Rg^!` is the exceptional datum, condensed model**: for a
right adjoint `R'` of the geometric `Rḡ_*` on bounded constructible condensed complexes and a right
adjoint `RW` of the Weil `Rg_*` on bounded constructible condensed Weil complexes, the underlying
complex of `RW L'` is `R'` of the underlying complex of `L'`, by an isomorphism carrying the
Frobenius structure of `RW L'` to the right Weil datum of the geometric adjunction. -/
theorem exists_condensedForget_obj_iso_isWeilEquivariant_rightWeilDatum
    (hR : ∀ K, condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z K →
      condensedBoundedConstructible k₀ l Y
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (compactificationProperMap k₀ f)).rightDerivedFunctor.obj K))
    {R' : (condensedBoundedConstructible k₀ l Y).FullSubcategory ⥤
      (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z).FullSubcategory}
    (adj : (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
      (condensedBoundedConstructible k₀ l Y)
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (compactificationProperMap k₀ f)).rightDerivedFunctor hR ⊣ R')
    {RW : (condensedWeilObjectProperty k₀ l Y).FullSubcategory ⥤
      (condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z).FullSubcategory}
    (adjW : (condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
      (condensedWeilObjectProperty k₀ l Y)
      (IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor
      (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f hR) ⊣ RW)
    (L' : (condensedWeilObjectProperty k₀ l Y).FullSubcategory) :
    ∃ θ : (IsoAlgebra.forget _).mapDerivedCategory.obj (RW.obj L').obj ≅
        (R'.obj ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩).obj,
      IsWeilEquivariant (condensedFrobenius k₀ l (shriekCompactification k₀ f).Z).mapDerivedCategory
        ((IsoAlgebra.derivedStrIso _).hom.app (RW.obj L').obj)
        (Adjunction.rightWeilDatum adj
          (IsoAlgebra.liftedDerivedCommIso (condensedProperExchange k₀ l f) _ _
            (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
              (shriekCompactification k₀ f).Z)
            (fun K hK ↦
              (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK) hR)
          (ObjectProperty.homMk
            (X := (ObjectProperty.liftFullSubcategory _ _
              (condensedFrobenius k₀ l Y).mapDerivedCategory
              (fun K hK ↦
                (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)).obj
                ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩)
            (Y := ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩)
            ((IsoAlgebra.derivedStrIso _).hom.app L'.obj))).hom θ.hom := by
  have : IsProper (shriekCompactification k₀ f).g := (shriekCompactification k₀ f).isProper
  have : IsProper (compactificationProperMap k₀ f) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper)
      (shriekCompactification k₀ f).g _ ‹_›
  exact IsoAlgebra.exists_forget_obj_iso_isWeilEquivariant_rightWeilDatum
    (condensedProperExchange k₀ l f) _ _ (fun _ hK ↦ hK.1)
    (fun K n hK ↦ boundedConstructible_shift l _ K n hK)
    (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
      (shriekCompactification k₀ f).Z)
    (fun K hK ↦ (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)
    hR adj
    (preservesColimit_discrete_rightDerivedFunctor_condensedLowerStar l
      (compactificationProperMap k₀ f))
    (condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z)
    (condensedWeilObjectProperty k₀ l Y) (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f hR) adjW L'

end WeilComplex

end AlgebraicGeometry
