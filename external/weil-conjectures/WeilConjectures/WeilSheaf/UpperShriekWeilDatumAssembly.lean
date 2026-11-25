/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.UpperShriekWeilDatum
public import WeilConjectures.WeilSheaf.UpperShriekWeilDatumComposite

/-!
# The Weil orientation from an equivariant geometric orientation

The target `WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`
(an isomorphism of the underlying complexes `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` commuting with the Frobenius
structures) follows from a *geometric orientation* `o : ī^* (ḡ^! ℚ̄_ℓ) ≅ ℚ̄_ℓ(d)[2d]` on `X̄` which
is
equivariant for the exceptional datum `AlgebraicGeometry.WeilComplex.upperShriekExceptionalDatum`
and the Frobenius structure of `ℚ̄_ℓ(d)[2d]`: compose with the comparison
`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_obj_iso_isWeilEquivariant`, which carries
the Frobenius structure of `Rf^! ℚ̄_ℓ` to the exceptional datum.
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
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] [HasUpperShriek k₀ l f]

set_option linter.style.whitespace false in
/-- **The Weil orientation from an equivariant geometric orientation.** Let `ḡ^!` be a right
adjoint of `Rḡ_*` for the compactification `ḡ` of `f̄` (`adjR'`), and let `o` be an isomorphism
`ī^* (ḡ^! ℚ̄_ℓ) ≅ ℚ̄_ℓ(d)[2d]` of complexes on `X̄` which is Frobenius equivariant for the
exceptional datum and the Frobenius structure of the Tate twist. Then the underlying complex of
`Rf^! ℚ̄_ℓ` is isomorphic to that of `ℚ̄_ℓ(d)[2d]` compatibly with the Frobenius structures: the
statement of `exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_isWeilEquivariant
    (d : ℕ) (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
          ).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).FullSubcategory}
    (adjR' : (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)
        (adicLowerStar l
          (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor
        hR ⊣ R')
    (o : (adicUpperStar l (Scheme.Hom.geometricFiberMap (shriekCompactification k₀ f).i
          (comp_over (shriekCompactification k₀ f).i _))).mapDerivedCategory.obj
          (R'.obj ⟨forget.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)),
            (WeilComplex.objectProperty_iff _).1
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)).property⟩).obj ≅
        forget.obj (((tateTwist k₀ l X d).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧))
    (ho : IsWeilEquivariant (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
      (upperShriekExceptionalDatum hR adjR'
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))
      ((IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj) o.hom) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨θ, hθ⟩ := exists_forget_upperShriek_obj_iso_isWeilEquivariant hR adjR'
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))
  exact ⟨θ ≪≫ o, (hθ.comp ho).symm⟩

set_option linter.style.longLine false in
set_option linter.style.whitespace false in
/-- **The Weil orientation from the trace square** (the uniqueness route, blueprint
`proposition-purity-trace-commute-frobenius`): let `o : f̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` be an
orientation on `X̄` (`f̄^! = ī^* ∘ ḡ^!` for the compactification), whose trace
`f̄_! ℚ̄_ℓ(d)[2d] ⟶ ℚ̄_ℓ` is Frobenius equivariant for the composite exchange of `f̄_!` and the
structures of `ℚ̄_ℓ(d)[2d]` and `ℚ̄_ℓ`. Then the underlying complex of `Rf^! ℚ̄_ℓ` is isomorphic to
that of `ℚ̄_ℓ(d)[2d]` compatibly with the Frobenius structures: the statement of
`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_trace
    (d : ℕ) (hR : PreservesBoundedConstructibleAdicLowerStar k₀ l f)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
          ).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).FullSubcategory}
    (adjR' : (DerivedCategory.boundedConstructibleAdic l
        (geometricFiberHomCompactification (k₀ := k₀) f).overObj.left).liftFullSubcategory
        (DerivedCategory.boundedConstructibleAdic l
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)
        (adicLowerStar l
          (geometricFiberHomCompactification (k₀ := k₀) f).overG.left).rightDerivedFunctor
        hR ⊣ R')
    (o : (R' ⋙ ObjectProperty.liftFullSubcategory _ _
        (adicUpperStar l (compactificationOpenImmersion k₀ f)).mapDerivedCategory
        (fun _ hK ↦ ProEtale.DerivedCategory.boundedConstructibleAdic.mapDerivedCategory_adicUpperStar
          (compactificationOpenImmersion k₀ f) hK)).obj
        ⟨forget.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)),
          (WeilComplex.objectProperty_iff _).1
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)).property⟩ ≅
      ⟨forget.obj (((tateTwist k₀ l X d).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
        (WeilComplex.objectProperty_iff _).1 (((tateTwist k₀ l X d).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).property⟩)
    (htrace : IsWeilEquivariant
      (ObjectProperty.liftFullSubcategory _ _
        (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory
        (fun K hK ↦
          (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
            (k₀ := k₀) (l := l) (X := Y) K).2 hK))
      (Adjunction.leftWeilDatum (compactifiedExchange hR)
        (ObjectProperty.homMk
          (X := (ObjectProperty.liftFullSubcategory _ _
            (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory
            (fun K hK ↦
              (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
                (k₀ := k₀) (l := l) (X := X) K).2 hK)).obj _)
          (Y := ⟨forget.obj (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
            (WeilComplex.objectProperty_iff _).1 (((tateTwist k₀ l X d).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).property⟩)
          ((IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj)))
      (ObjectProperty.homMk
        (X := (ObjectProperty.liftFullSubcategory _ _
          (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory
          (fun K hK ↦
            (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
              (k₀ := k₀) (l := l) (X := Y) K).2 hK)).obj
            ⟨forget.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)),
              (WeilComplex.objectProperty_iff _).1
                (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)).property⟩)
        (Y := ⟨forget.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)),
          (WeilComplex.objectProperty_iff _).1
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)).property⟩)
        ((IsoAlgebra.derivedStrIso _).hom.app
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)).obj))
      ((compactifiedAdjunction hR adjR').orientationTrace o)) :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  have h := ((compactifiedAdjunction hR adjR').isWeilEquivariant_rightWeilDatum_iff_trace
    (compactifiedExchange hR) o _ _).2 htrace
  refine exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_isWeilEquivariant d hR
    adjR' ((ObjectProperty.ι _).mapIso o) ?_
  rw [upperShriekExceptionalDatum_eq_rightWeilDatum]
  unfold IsWeilEquivariant at h ⊢
  exact congrArg InducedCategory.Hom.hom h

end WeilComplex

end AlgebraicGeometry
