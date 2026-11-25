/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointExceptionalDatum
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric

/-!
# The Frobenius structure of the Weil `Rf^!` is the exceptional datum

Let `f : X ⟶ Y` be a separated morphism of finite type of `k₀`-schemes of finite type, with the
compactification `X ⟶[i] Z ⟶[g] Y` chosen by `AlgebraicGeometry.WeilComplex.derivedLowerShriek`,
and let `L` be a Weil complex on `Y`. The underlying complex of `Rf^! L` on `X̄` is
`ī^* (ḡ^! L̄)`, for any right adjoint `ḡ^!` of `Rḡ_*` on bounded constructible adic complexes.
We show that under this identification the Frobenius structure of `Rf^! L` is the *exceptional
datum*: the transport along `ī^*` of the right Weil datum of the adjunction `Rḡ_* ⊣ ḡ^!`
(`CategoryTheory.Adjunction.rightWeilDatum`), i.e. the unique Weil datum on `ḡ^! L̄` for which the
counit `Rḡ_* ḡ^! L̄ ⟶ L̄` is Frobenius equivariant
(`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_obj_iso_isWeilEquivariant`).

This is the formal half of blueprint `proposition-purity-trace-commute-frobenius` (the Weil
structure of `Rf^!` is the exceptional datum of the Frobenius square); the geometric half, that
the canonical orientation carries the exceptional datum to the Tate datum, is the trace square.

## Proof
`Rf^! ≅ ḡ^! ∘ i^*` as functors of Weil complexes (`UpperShriekGeometric`), and isomorphisms of
Weil complexes are equivariant. The structure of `i^* M` is the transport of that of `M`
(`CategoryTheory.Endofunctor.IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app`),
and the structure of `ḡ^! L` is the right Weil datum
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_obj_iso_isWeilEquivariant_rightWeilDatum`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

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
/-- The compactification of `f` chosen by `AlgebraicGeometry.WeilComplex.derivedLowerShriek`. -/
noncomputable abbrev shriekCompactification :=
  HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)

variable (k₀ l) in
/-- The condition that `Rḡ_*` preserves bounded constructible adic complexes, for the
compactification `ḡ` of `f̄`. -/
abbrev PreservesBoundedConstructibleAdicLowerStar : Prop :=
  ∀ K, DerivedCategory.boundedConstructibleAdic l
      (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left K →
    DerivedCategory.boundedConstructibleAdic l
      (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
      ((adicLowerStar l
        (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor.obj K)

set_option linter.unusedSectionVars false in
/-- `Rḡ_*` preserves bounded constructible adic complexes. -/
theorem preservesBoundedConstructibleAdicLowerStar :
    PreservesBoundedConstructibleAdicLowerStar k₀ l f := fun _ hK ↦
  boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)) _ hK

variable {f} [HasUpperShriek k₀ l f]

set_option linter.style.longLine false in
/-- **The exceptional datum.** For a right adjoint `ḡ^!` of `Rḡ_*` on bounded constructible adic
complexes (`adjR'`) and a Weil complex `L` on `Y`, the Weil datum on `ī^* (ḡ^! L̄)`: the transport
along `ī^*` of the right Weil datum of `Rḡ_* ⊣ ḡ^!` of the structure of `L`. -/
noncomputable def upperShriekExceptionalDatum
    (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).FullSubcategory}
    (adjR' : (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)
        (adicLowerStar l (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor
        hR ⊣ R')
    (L : WeilComplex k₀ l Y) :
    (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.obj
        ((adicUpperStar l (Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
          (comp_over (shriekCompactification k₀ f).i _))).mapDerivedCategory.obj
          (R'.obj ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩).obj) ⟶
      (adicUpperStar l (Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
          (comp_over (shriekCompactification k₀ f).i _))).mapDerivedCategory.obj
          (R'.obj ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩).obj :=
  transportWeilDatum
    (adicUpperStar l (Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
      (comp_over (shriekCompactification k₀ f).i _))).mapDerivedCategory
    (IsoAlgebra.derivedExactCommIso (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l
      (shriekCompactification k₀ f).i (comp_over (shriekCompactification k₀ f).i _))).symm
    (Adjunction.rightWeilDatum adjR'
      (IsoAlgebra.liftedDerivedCommIso
        (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l (shriekCompactification k₀ f).g
          (comp_over (shriekCompactification k₀ f).g _)) _ _
        (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
          (k₀ := k₀) (l := l) (X := (shriekCompactification k₀ f).Z))
        (fun K hK ↦ (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
          (k₀ := k₀) (l := l) (X := Y) K).2 hK) hR)
      (ObjectProperty.homMk
        (X := (ObjectProperty.liftFullSubcategory _ _
          (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory
          (fun K hK ↦ (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
            (k₀ := k₀) (l := l) (X := Y) K).2 hK)).obj
            ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩)
        (Y := ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩)
        ((IsoAlgebra.derivedStrIso _).hom.app L.obj))).hom

set_option linter.style.longLine false in
set_option linter.unusedSectionVars false in
/-- **The Frobenius structure of the Weil `Rf^!` is the exceptional datum** (blueprint
`proposition-purity-trace-commute-frobenius`, formal half): for a right adjoint `ḡ^!` of
`Rḡ_*` on bounded constructible adic complexes and a Weil complex `L` on `Y`, there is an
identification `θ` of the underlying complex of `Rf^! L` with `ī^* (ḡ^! L̄)` which is Frobenius
equivariant for the structure of `Rf^! L` and the exceptional datum
`AlgebraicGeometry.WeilComplex.upperShriekExceptionalDatum`. -/
theorem exists_forget_upperShriek_obj_iso_isWeilEquivariant
    (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).FullSubcategory}
    (adjR' : (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)
        (adicLowerStar l (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor
        hR ⊣ R')
    (L : WeilComplex k₀ l Y) :
    ∃ θ : forget.obj ((upperShriek f).obj L) ≅
        (adicUpperStar l (Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
          (comp_over (shriekCompactification k₀ f).i _))).mapDerivedCategory.obj
          (R'.obj ⟨forget.obj L, (WeilComplex.objectProperty_iff _).1 L.property⟩).obj,
      IsWeilEquivariant (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
        ((IsoAlgebra.derivedStrIso _).hom.app ((upperShriek f).obj L).obj)
        (upperShriekExceptionalDatum hR adjR' L) θ.hom := by
  let c := shriekCompactification k₀ f
  let cb := geometricFiberHomCompactification (k₀ := k₀) f
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsProper (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) c.g _ ‹_›
  have hPC_F := WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
    (k₀ := k₀) (l := l) (X := c.Z)
  have hPD_G (K) (hK : DerivedCategory.boundedConstructibleAdic l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber K) :=
    (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
      (k₀ := k₀) (l := l) (X := Y) K).2 hK
  have hcoprod := ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar (l := l)
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀))))
  -- `Rg_*` on Weil complexes is a left adjoint
  have : (derivedLowerStar (k₀ := k₀) (l := l) c.g).IsLeftAdjoint :=
    IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))
      (DerivedCategory.boundedConstructibleAdic l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK) hPC_F hPD_G hR
      adjR'.isLeftAdjoint hcoprod
      (WeilComplex.objectProperty k₀ l c.Z) (WeilComplex.objectProperty k₀ l _)
      (WeilComplex.objectProperty_iff (X := c.Z)) (WeilComplex.objectProperty_iff (X := _))
      (WeilComplex.objectProperty_rightDerivedLowerStar c.g)
  let adjg := Adjunction.ofIsLeftAdjoint (derivedLowerStar (k₀ := k₀) (l := l) c.g)
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  -- `Rf^! ≅ R_g ⋙ i^*`
  have e : derivedLowerShriek k₀ l f ≅ extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (fun φ ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  let eR : upperShriek (k₀ := k₀) (l := l) f ≅
      (derivedLowerStar (k₀ := k₀) (l := l) c.g).rightAdjoint ⋙ upperStar c.i :=
    (derivedLowerShriekUpperShriekAdjunction f).rightAdjointUniq
      (((extensionByZeroUpperStarAdjunction c.i).comp adjg).ofNatIsoLeft e.symm)
  -- the structure of `R_g L` is the right Weil datum
  obtain ⟨θg, hθg⟩ := IsoAlgebra.exists_forget_obj_iso_isWeilEquivariant_rightWeilDatum
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))
      (DerivedCategory.boundedConstructibleAdic l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK) hPC_F hPD_G hR
      adjR' hcoprod
      (WeilComplex.objectProperty k₀ l c.Z) (WeilComplex.objectProperty k₀ l _)
      (WeilComplex.objectProperty_iff (X := c.Z)) (WeilComplex.objectProperty_iff (X := _))
      (WeilComplex.objectProperty_rightDerivedLowerStar c.g) adjg L
  let ci := ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l c.i
    (comp_over c.i (Spec (CommRingCat.of k₀)))
  let ī := adicUpperStar l (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀))))
  -- isomorphisms of Weil complexes are equivariant
  have h₁ : IsWeilEquivariant (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
      ((IsoAlgebra.derivedStrIso _).hom.app ((upperShriek f).obj L).obj)
      ((IsoAlgebra.derivedStrIso _).hom.app
        ((upperStar c.i).obj ((derivedLowerStar c.g).rightAdjoint.obj L)).obj)
      (forget.map (eR.hom.app L)) :=
    (IsoAlgebra.derivedStrIso _).hom.naturality (eR.hom.app L).hom
  -- the structure of `i^* M` is the transport of that of `M`
  have h₂ := IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app ci
    ((derivedLowerStar c.g).rightAdjoint.obj L).obj
  -- transport `θg` along `ī^*`
  have h₃ := hθg.map ī.mapDerivedCategory (IsoAlgebra.derivedExactCommIso ci).symm
  exact ⟨forget.mapIso (eR.app L) ≪≫
    (IsoAlgebra.derivedExactForgetCommIso ci).app ((derivedLowerStar c.g).rightAdjoint.obj L).obj ≪≫
    ī.mapDerivedCategory.mapIso θg, h₁.comp (h₂.comp h₃)⟩

end WeilComplex

end AlgebraicGeometry
