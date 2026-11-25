/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CompactProjectionFormula

/-!
# Compact pushforward of pullback from the constant object

The projection formula expresses `Rf! f*` as tensoring with `Rf!` of the
constant complex. This reduces the trivial-line Thom functor to its constant
coefficient value.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Tensoring the constant complex with an ambient native complex is the identity. -/
noncomputable def nativeDerivedTensorConstantIso :
    Prod.sectR ((DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X)) _ ⋙
      nativeDerivedTensor k₀ l X ≅ 𝟭 _ := by
  let C := nativeDerivedClosedComparison k₀ l X
  letI := C.weilClosed.monoidal
  let A := (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X)
  let e : tensorLeft A ≅ Prod.sectR A _ ⋙ nativeDerivedTensor k₀ l X :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
      dsimp [nativeDerivedTensor, WeilConjectures.CoefficientClosedStructure.tensor]
      change A ◁ g ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 A ⊗ₘ g)
      simp)
  exact e.symm ≪≫ (curriedTensor _).mapIso C.weilUnit.symm ≪≫ leftUnitorNatIso _

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- Tensoring the constant Weil complex with a Weil complex is the identity. -/
noncomputable def nativeConstructibleTensorConstantIso :
    Prod.sectR (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) _ ⋙
      nativeConstructibleTensor k₀ l X ≅ 𝟭 _ :=
  ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
      (ProEtaleWeilSheaf.nativeDerivedTensorConstantIso (k₀ := k₀) (l := l)))

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Compact pushforward after pullback is tensoring with compact pushforward of
the constant object, naturally in the input complex. -/
theorem nonempty_upperStar_comp_shriek_iso_tensor_constant :
    Nonempty (upperStar f ⋙ derivedLowerShriek k₀ l f ≅
      Prod.sectR ((derivedLowerShriek k₀ l f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))) _ ⋙
      nativeConstructibleTensor k₀ l Y) := by
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)
  obtain ⟨π⟩ := nonempty_nativeCompactProjectionLeft_iso (k₀ := k₀) (l := l) f
  let eR : Prod.sectR U _ ⋙ nativeCompactProjectionRight k₀ l f ≅
      upperStar f ⋙ (Prod.sectR U _ ⋙ nativeConstructibleTensor k₀ l X) ⋙
        derivedLowerShriek k₀ l f :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
      simp [nativeCompactProjectionRight, nativeConstructibleTensor])
  let eL : Prod.sectR U _ ⋙ nativeCompactProjectionLeft k₀ l f ≅
      Prod.sectR ((derivedLowerShriek k₀ l f).obj U) _ ⋙
        nativeConstructibleTensor k₀ l Y :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.comp_map,
        Prod.sectR_map, Functor.prod_map, Functor.id_map, Iso.refl_hom, Category.comp_id,
        Category.id_comp]
      erw [(derivedLowerShriek k₀ l f).map_id U])
  exact ⟨Functor.isoWhiskerLeft (upperStar f)
      (Functor.isoWhiskerRight
        (nativeConstructibleTensorConstantIso (k₀ := k₀) (l := l) (X := X)).symm
        (derivedLowerShriek k₀ l f)) ≪≫
    eR.symm ≪≫ Functor.isoWhiskerLeft (Prod.sectR U _) π.symm ≪≫ eL⟩

end AlgebraicGeometry.WeilComplex
