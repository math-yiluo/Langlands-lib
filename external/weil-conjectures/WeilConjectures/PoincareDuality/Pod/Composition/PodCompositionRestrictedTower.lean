/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralInverseImageComparisonComposition

/-! # Composition of the normalized restricted towers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Restricted generator comparisons respect the normalized ordinary compositor.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL
(blueprint: lem-pod-composition-restricted-tower).

Proof: the ordinary compositor is invertible, so its stated forward section
formula determines the inverse section formula by cancellation. Test the tower
maps at every tower index, complex degree, and original local section. The
restricted-generator equations replace each comparison by its actual adjunction
unit. Restricted-section naturality moves the inverse compositor to the original
section. The strict sequence compositor sends a unit generator to two successive
unit generators. Their site naturality then moves all arrows to the final sheaf,
where functoriality combines them. The actual comma-arrow composition identity
identifies the two resulting arrows, proving the section equality and hence the
entire tower-map equality. Zero sections and empty sites obey the same equations. -/
theorem podCompositionRestrictedTower
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (Df : PodCompletionReindex l E f) (Dh : PodCompletionReindex l E h)
    (Dc : PodCompletionReindex l E (h ≫ f))
    (hf : PodCompletionReindex.RestrictedGenerators l E f Df)
    (hh : PodCompletionReindex.RestrictedGenerators l E h Dh)
    (hc : PodCompletionReindex.RestrictedGenerators l E (h ≫ f) Dc)
    (a : isoReductionIntegralInverse l E (h ≫ f) ≅
      isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h)
    (ha : ∀ (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      (a.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x)
    (C : CochainComplex (coefficientSequenceModules l E V) ℤ) :
    let σ := NatTrans.mapHomologicalComplex
      (integralComparisonSequenceComposition l E h f).hom (.up ℤ)
    let τ := whiskerLeft (podRestrictedTower l E C)
      (NatTrans.mapHomologicalComplex a.inv (.up ℤ))
    τ ≫ (Dc.restricted C).hom ≫
        HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).map
            (σ.app C)) =
      (podReindexTower l E h).map (Df.restricted C).hom ≫
        (Dh.restricted
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex
            (.up ℤ)).obj C)).hom := by
  dsimp only
  have hai (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose f).obj
        ((proEtaleIsoPostcompose h).obj U)))) :
      (a.inv.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).hom.app U).op x := by
    have hinj : Function.Injective ((a.hom.app M).val.app (op U)) := by
      apply Function.LeftInverse.injective (g := (a.inv.app M).val.app (op U))
      intro x
      change ((a.hom.app M) ≫ (a.inv.app M)).val.app (op U) x = x
      rw [a.hom_inv_id_app]
      rfl
    apply hinj
    change ((a.inv.app M) ≫ (a.hom.app M)).val.app (op U) x = _
    rw [a.inv_hom_id_app, ha]
    change x = M.val.presheaf.map _ (M.val.presheaf.map _ x)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  ext n i U x
  let M := C.X i
  let R := coefficientSequenceRestriction l E V
  obtain ⟨x, rfl⟩ := (Equiv.cast
    (integralComparisonRestrictedSectionType l E V M n.unop
      (op ((proEtaleIsoPostcompose f).obj
        ((proEtaleIsoPostcompose h).obj U.unop)))).symm).surjective x
  change (((coefficientSequenceRestriction l E Z).map
      ((integralComparisonSequenceComposition l E h f).hom.app M)).app n).val.app U
    (((((Dc.restricted C).hom.app n).f i).val.app U)
      ((a.inv.app ((R.obj M).obj n)).val.app U
        (integralComparisonRestrictedSection l E V M n.unop
          (op ((proEtaleIsoPostcompose f).obj
            ((proEtaleIsoPostcompose h).obj U.unop))) x))) =
    (((((Dh.restricted _).hom.app n).f i).val.app U)
      (((((Df.restricted C).hom.app n).f i).val.app
        (op ((proEtaleIsoPostcompose h).obj U.unop)))
          (integralComparisonRestrictedSection l E V M n.unop
            (op ((proEtaleIsoPostcompose f).obj
              ((proEtaleIsoPostcompose h).obj U.unop))) x)))
  rw [hai]
  erw [AlgebraicGeometry.ProEtale.restrictedSection_naturality]
  erw [hc C n.unop i U.unop, AlgebraicGeometry.ProEtale.restrictedSection_map]
  erw [hf C n.unop i ((proEtaleIsoPostcompose h).obj U.unop)]
  erw [hh _ n.unop i U.unop]
  congr 1
  let B := (integralComparisonSequencePullback l E h).obj
    ((integralComparisonSequencePullback l E f).obj M)
  let v := (MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).hom.app U.unop
  have hs := PresheafOfModules.naturality_apply
    ((integralComparisonSequenceComposition l E h f).hom.app M).val
    (Prod.mkHom (𝟙 n.unop) (proEtaleIsoCommaArrow (h ≫ f) U.unop)).op
    (integralComparisonSequenceGenerator l E (h ≫ f) M n.unop
      ((proEtaleIsoPostcompose (h ≫ f)).obj U.unop)
      (M.val.map (Prod.mkHom (𝟙 n.unop) v).op x))
  erw [hs]
  erw [AlgebraicGeometry.ProEtale.sequenceGenerator_composition]
  erw [AlgebraicGeometry.ProEtale.sequenceGenerator_naturality l E f M n.unop v x]
  erw [AlgebraicGeometry.ProEtale.sequenceGenerator_naturality l E h
    ((integralComparisonSequencePullback l E f).obj M) n.unop
    ((proEtaleBaseChange f).map v)]
  erw [AlgebraicGeometry.ProEtale.sequenceGenerator_naturality l E h
    ((integralComparisonSequencePullback l E f).obj M) n.unop
    (proEtaleIsoCommaArrow f ((proEtaleIsoPostcompose h).obj U.unop))]
  change B.val.presheaf.map _ (B.val.presheaf.map _ (B.val.presheaf.map _ _)) =
    B.val.presheaf.map _ (B.val.presheaf.map _ _)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  apply congrArg (fun t ↦ B.val.presheaf.map t
    (integralComparisonSequenceGenerator l E h
      ((integralComparisonSequencePullback l E f).obj M) n.unop
      ((proEtaleBaseChange f).obj
        ((proEtaleIsoPostcompose f).obj ((proEtaleIsoPostcompose h).obj U.unop)))
      (integralComparisonSequenceGenerator l E f M n.unop
        ((proEtaleIsoPostcompose f).obj ((proEtaleIsoPostcompose h).obj U.unop)) x)))
  apply congrArg Quiver.Hom.op
  apply Prod.hom_ext
  · simp
  · change proEtaleIsoCommaArrow (h ≫ f) U.unop ≫
        (MorphismProperty.Over.pullbackComp h f).hom.app _ ≫
        (proEtaleBaseChange h).map ((proEtaleBaseChange f).map v) = _
    erw [← (MorphismProperty.Over.pullbackComp h f).hom.naturality v]
    exact AlgebraicGeometry.ProEtale.comma_composition h f U.unop

end WeilConjectures
