/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroRepresentativeData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleUnitor
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleFormal

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

-- The assembly elaborates several large localized composites at once.
/-- The scalar transpose formula for one explicit zero-cycle representative.
Source: Stacks 03CZ, 079P and 08JA.
Proof: apply the finite tensor comparison square to the fixed Hom-complex
representative, use the uncurrying models to identify evaluation with the scalar
extension transpose, and then use the ordinary scalar-section formula. The
normalized zero-cycle equivalences turn the resulting chain-map equality into the
displayed derived-category equality.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-cycle-representative)
-/
theorem coefficientDerivedSectionsScalarHomZero_cycle_representative
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (M : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (N : CochainComplex (scalarReductionSource l E W) ℤ)
    (eN : DerivedCategory.Q.obj N ≅
      (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))
    (z : (coefficientHomSectionComplex.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P N).cycles 0)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op (DerivedCategory.Q.obj P),
          (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))))
    (hx :
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
          ((coefficientIntegralGlobalHom l E W).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) eN.hom))
        (coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P N z) = x) :
    coefficientFiniteHomEquiv l E W n _ _
        (coefficientDerivedSectionsScalarHomZeroMap l E W R D n
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M) x) =
      ((coefficientFiniteAdjunction l E W n).homEquiv
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M)).symm
        (coefficientIntegralHomEquiv l E W (DerivedCategory.Q.obj P)
          ((coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M)) x) := by
  have hUA := coefficientUnitComplex_isKFlat.{u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = coefficientHomUnitMapOfCycle.{u, t + 1, t}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P N z :=
    ⟨_, rfl⟩
  -- the class of `z` is the image of the unit class
  have hcls : coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P N z =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
        ((coefficientIntegralSections l E W).map
          (DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, t + 1, t}
            (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P N).inv))
        (coefficientUnitClass.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)) := by
    subst hσ
    have h := coefficientHomZeroClass_cycleOfUnitMap.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P N
      (coefficientHomUnitMapOfCycle.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P N z)
    rw [coefficientHomCycleOfUnitMap_unitMapOfCycle] at h
    exact h
  -- the H-zero class `x` as a morphism
  have heA : coefficientIntegralHomEquiv l E W (DerivedCategory.Q.obj P)
      ((coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M)) x =
      DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P).inv ≫
        (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) R.integralClosed
          R.integralTensorModel (coefficientIntegralUnitComplex l E W) P hUA hP).hom ≫
        (R.integralClosed.transpose _ _ _).symm
          (DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, t + 1, t}
            (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P N).inv) ≫
        eN.hom := by
    have hn := (coefficientHomZeroEquiv_exists.{u, t + 1, t, max (t + 2) (u + 1)}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).choose_spec.1.1
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) (DerivedCategory.Q.obj P)
        ((coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M)) (𝟙 _) eN.hom
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
          ((coefficientIntegralSections l E W).map
            (DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, t + 1, t}
              (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
                P N).inv))
          (coefficientUnitClass.{u} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)))
    have h4 := coefficientHomZeroEquiv_unitClass_transpose.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) R.integralClosed R.integralTensorModel P N
      hP ((R.integralClosed.transpose _ _ _).symm
        (DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, t + 1, t}
          (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P N).inv))
    erw [Equiv.apply_symm_apply] at h4
    rw [← hx, hcls]
    refine hn.trans ?_
    rw [Category.id_comp]
    refine (congrArg (· ≫ eN.hom) h4).trans ?_
    simp only [Category.assoc]
  have hU := coefficientFiniteAdjunction_unit_unitClass l E W D n
  -- the class `x` is the image of the unit class
  have hx' : x = (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
      ((coefficientIntegralSections l E W).map
        ((DerivedCategory.Q.map σ ≫ (coefficientHomResolutionIso.{u, t + 1, t}
          (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P N).inv) ≫
          (coefficientIntegralInternalHom l E W).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) eN.hom)))
      (coefficientUnitClass.{u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)) := by
    refine hx.symm.trans ((congrArg _ hcls).trans ?_)
    refine (Functor.map_comp_apply_addCommGrp _ _ _ _).trans ?_
    simp only [Functor.map_comp]
    rfl
  have hP' := (coefficientTensorModelPreservation l E W).1 P hP n
  have hnat := (coefficientHomZeroEquiv_exists.{u, t + 1, t, max (t + 2) (u + 1)}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)).choose_spec.1.1
      ((coefficientFiniteDerivedExtension l E W n).obj (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.obj M)
      (DerivedCategory.Q.obj (((scalarReductionExtension l E W n).mapHomologicalComplex
        (.up ℤ)).obj P))
      (DerivedCategory.Q.obj M) (coefficientFiniteReductionModel l E W P hP n).inv (𝟙 _)
  have h4 := coefficientHomZeroEquiv_unitClass_transpose.{u, t + 1, t, max (t + 2) (u + 1)}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n)
    (R.finiteTensorModel n)
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) M hP'
  have hW := coefficientFiniteTensor_unitLeftUnitor l E W R hF D n P hP
  exact coefficientEnrichedAdjunctionMap_homZero R.integralClosed (R.finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteAdjunction l E W n)
    (R.finiteTensor n) (coefficientIntegralSections l E W) (coefficientFiniteSections l E W n)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0) (D.scalarSections n).hom
    (fun X Y ↦ coefficientFiniteHomEquiv l E W n X Y) _ _ _ hU
    (coefficientFiniteReductionModel l E W P hP n) hnat
    (DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)).inv ≫
      (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (R.finiteClosed n) (R.finiteTensorModel n)
        (coefficientFiniteUnitComplex l E W n)
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficientUnitComplex_isKFlat.{u} _ _) hP').hom)
    (fun X ↦ (h4 X).trans (Category.assoc _ _ _).symm)
    (DerivedCategory.Q.map (coefficientUnitLeftUnitor.{u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P).inv ≫
      (CoefficientTensorModels.iso.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) R.integralClosed
        R.integralTensorModel (coefficientIntegralUnitComplex l E W) P hUA hP).hom)
    (by simpa only [Category.assoc] using hW) _ eN.hom x hx' _
    (heA.trans (Category.assoc _ _ _).symm)

end WeilConjectures
