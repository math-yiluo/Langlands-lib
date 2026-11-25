/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1)
-/
module

public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriek

/-!
# The condensed exceptional datum of `Rg^!` with the concrete geometric adjunction

`WeilConjectures.WeilSheaf.CondensedWeilUpperShriek` identifies the Frobenius structure of the
Weil `Rg^! L'` (proper part `g : Z ⟶ Y` of the compactification of `f`, condensed model) with the
right Weil datum of ANY right adjoint of the geometric `Rḡ_*` on bounded constructible condensed
complexes. Here the geometric adjunction is made concrete: it is the upstream
`ProEtale.CondensedRing.boundedConstructibleLowerStar l ḡ` with its right adjoint
(`isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`), the one from which the upstream
`boundedConstructibleUpperShriekOfCompactification` is built.

## Main definitions

- `WeilComplex.condensedProperPreserves`: Deligne's finiteness for `Rḡ_*`, in the form used by
  `CondensedWeilUpperShriek`.
- `WeilComplex.condensedProperAdjunction`: the upstream adjunction `Rḡ_* ⊣ ḡ^!` on bounded
  constructible condensed complexes, with the left adjoint written as
  `ObjectProperty.liftFullSubcategory`.
- `WeilComplex.condensedWeilProperAdjunction`: the Weil `Rg_* ⊣ Rg^!` in the condensed model.

## Main result

- `WeilComplex.exists_condensedForget_obj_iso_isWeilEquivariant_rightWeilDatum_concrete`: the
  exceptional datum theorem for these concrete adjunctions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

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
/-- The proper part `ḡ : Z̄ ⟶ Ȳ` of the base-changed compactification, as a morphism over `k̄`
(`Compactification.overG` of `geometricFiberHomCompactification`). Its underlying morphism is
`compactificationProperMap k₀ f`. -/
noncomputable abbrev condensedProperOverHom :=
  (geometricFiberHomCompactification (k₀ := k₀) f).overG

set_option linter.unusedSectionVars false in
variable (k₀) in
/-- **Deligne's finiteness for `Rḡ_*`** in the form used by `CondensedWeilUpperShriek`. -/
theorem condensedProperPreserves (K)
    (hK : condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z K) :
    condensedBoundedConstructible k₀ l Y
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (compactificationProperMap k₀ f)).rightDerivedFunctor.obj K) :=
  CondensedRing.boundedConstructible_rightDerivedLowerStar_obj l (condensedProperOverHom k₀ f)
    ⟨K, hK⟩

variable (k₀) in
/-- The right adjoint `ḡ^!` of the upstream `Rḡ_*` on bounded constructible condensed
complexes. -/
noncomputable abbrev condensedProperRightAdjoint :=
  (CondensedRing.boundedConstructibleLowerStar l (condensedProperOverHom k₀ f)).rightAdjoint

variable (k₀) in
/-- The upstream `Rḡ_*` on bounded constructible condensed complexes, written as
`ObjectProperty.liftFullSubcategory`, is the upstream `boundedConstructibleLowerStar`. -/
noncomputable def condensedProperLowerStarIso :
    CondensedRing.boundedConstructibleLowerStar l (condensedProperOverHom k₀ f) ≅
      (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
        (condensedBoundedConstructible k₀ l Y)
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (compactificationProperMap k₀ f)).rightDerivedFunctor
        (condensedProperPreserves k₀ l f) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

variable (k₀) in
/-- **The geometric adjunction `Rḡ_* ⊣ ḡ^!`** on bounded constructible condensed complexes, the
upstream one, in the form used by `CondensedWeilUpperShriek`. -/
noncomputable def condensedProperAdjunction :
    (condensedBoundedConstructible k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
        (condensedBoundedConstructible k₀ l Y)
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (compactificationProperMap k₀ f)).rightDerivedFunctor
        (condensedProperPreserves k₀ l f) ⊣
      condensedProperRightAdjoint k₀ l f :=
  (Adjunction.ofIsLeftAdjoint
    (CondensedRing.boundedConstructibleLowerStar l (condensedProperOverHom k₀ f))).ofNatIsoLeft
    (condensedProperLowerStarIso k₀ l f)

variable (k₀) in
/-- The Weil `Rg_*` in the condensed model is a left adjoint. -/
instance isLeftAdjoint_condensedWeilProperLowerStar :
    ((condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
      (condensedWeilObjectProperty k₀ l Y)
      (IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor
      (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f
        (condensedProperPreserves k₀ l f))).IsLeftAdjoint :=
  isLeftAdjoint_condensedWeilLowerStar k₀ l f (condensedProperPreserves k₀ l f)
    (condensedProperAdjunction k₀ l f).isLeftAdjoint

variable (k₀) in
/-- **The Weil `Rg^!` in the condensed model**: the right adjoint of the Weil `Rg_*`. -/
noncomputable abbrev condensedWeilProperRightAdjoint :=
  ((condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
    (condensedWeilObjectProperty k₀ l Y)
    (IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor
    (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f
      (condensedProperPreserves k₀ l f))).rightAdjoint

variable (k₀) in
/-- **The Weil adjunction `Rg_* ⊣ Rg^!`** in the condensed model. -/
noncomputable def condensedWeilProperAdjunction :
    (condensedWeilObjectProperty k₀ l (shriekCompactification k₀ f).Z).liftFullSubcategory
        (condensedWeilObjectProperty k₀ l Y)
        (IsoAlgebra.mapOfNatIso (condensedProperExchange k₀ l f)).rightDerivedFunctor
        (condensedWeilObjectProperty_rightDerivedFunctor k₀ l f
          (condensedProperPreserves k₀ l f)) ⊣
      condensedWeilProperRightAdjoint k₀ l f :=
  Adjunction.ofIsLeftAdjoint _

set_option linter.style.longLine false in
variable (k₀) in
/-- **The Frobenius structure of the Weil `Rg^!` is the exceptional datum of the upstream
geometric adjunction** (condensed model, concrete adjunctions). -/
theorem exists_condensedForget_obj_iso_isWeilEquivariant_rightWeilDatum_concrete
    (L' : (condensedWeilObjectProperty k₀ l Y).FullSubcategory) :
    ∃ θ : (IsoAlgebra.forget (condensedFrobenius k₀ l (shriekCompactification k₀ f).Z)).mapDerivedCategory.obj
        ((condensedWeilProperRightAdjoint k₀ l f).obj L').obj ≅
        ((condensedProperRightAdjoint k₀ l f).obj
          ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩).obj,
      IsWeilEquivariant (condensedFrobenius k₀ l (shriekCompactification k₀ f).Z).mapDerivedCategory
        ((IsoAlgebra.derivedStrIso _).hom.app ((condensedWeilProperRightAdjoint k₀ l f).obj L').obj)
        (Adjunction.rightWeilDatum (condensedProperAdjunction k₀ l f)
          (IsoAlgebra.liftedDerivedCommIso (condensedProperExchange k₀ l f) _ _
            (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l
              (shriekCompactification k₀ f).Z)
            (fun K hK ↦
              (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)
            (condensedProperPreserves k₀ l f))
          (ObjectProperty.homMk
            (X := (ObjectProperty.liftFullSubcategory _ _
              (condensedFrobenius k₀ l Y).mapDerivedCategory
              (fun K hK ↦
                (boundedConstructible_lowerStar_frobenius_mapDerivedCategory_obj_iff l Y K).2 hK)).obj
                ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩)
            (Y := ⟨(IsoAlgebra.forget _).mapDerivedCategory.obj L'.obj, L'.property⟩)
            ((IsoAlgebra.derivedStrIso _).hom.app L'.obj))).hom θ.hom :=
  exists_condensedForget_obj_iso_isWeilEquivariant_rightWeilDatum k₀ l f
    (condensedProperPreserves k₀ l f) (condensedProperAdjunction k₀ l f)
    (condensedWeilProperAdjunction k₀ l f) L'

end WeilComplex

end AlgebraicGeometry
