/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
/-! # Signed completed scalar shift coordinates and normalization

Source: Stacks Project Tags 011G, 014E, 06YS, 06YT, 06YU and 08TC;
blueprint main-20261015, the Weil-structures paragraph of the open-closed
triangle proof (blueprint: def-pur-completed-scalar-shift-coordinates).

The finite-level and product maps and the two predicates are extracted from
CompletedScalarShift without changing names, signatures or bodies. These are
normalization definitions; they assert no existence or shift compatibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 1024

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {L : Type u} [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

/-- The canonical tensor reindexing at a finite level, followed by scalar restriction.
Both comparisons are the `mapCochainComplexShiftIso` comparisons of the underlying
additive module functors; no tower isomorphism is chosen.
Source: Stacks Tags 011G and 08TC (blueprint: def-pur-completed-scalar-shift-coordinates). -/
noncomputable def completedScalarShiftLevelIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) (n : ℕ) :
    (integralScalarLevel l E L ι Y n).obj (P⟦m⟧) ≅
      ((integralScalarLevel l E L ι Y n).obj P)⟦m⟧ :=
  (integralOperationsRestrict l L Y n).mapIso
      (((integralScalarReduction l E L ι Y n).mapCochainComplexShiftIso m).app P) ≪≫
    ((SheafOfModules.restrictScalars
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))).mapCochainComplexShiftIso
            m).app
      ((integralScalarFiniteComplex l E L ι Y n).obj P)

/-- The canonical degreewise product reindexing, fixed at every quotient level.
Source: Stacks Tags 011G and 08TC (blueprint: def-pur-completed-scalar-shift-coordinates). -/
noncomputable def completedScalarShiftProductIso
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) :
    (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj (P⟦m⟧)).obj (op n)) ≅
      (∏ᶜ fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))⟦m⟧ :=
  Limits.Pi.mapIso (fun n ↦ completedScalarShiftLevelIso ι Y P m n) ≪≫
    (PreservesProduct.iso (shiftFunctor (CochainComplex (integralTowerModules l L Y) ℤ) m)
      (fun n : ℕ ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))).symm

/-- The two coordinates of the actual Roos shift map. The first inclusion carries
coefficient one, and the second carries `(-1)^m`. These are inclusions in the
mapping *cocone*, rather than in the unshifted mapping cone.
Source: Stacks Tags 011G, 014E and 08TC
(blueprint: def-pur-completed-scalar-shift-coordinates). -/
def completedScalarShiftConeFormula
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (m : ℤ) : Prop :=
  (∀ j : ℤ,
    (CochainComplex.mappingCocone.inl
        (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧))).v j j (by omega) ≫
        ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P).f j =
      (completedScalarShiftProductIso ι Y P m).hom.f j ≫
        (CochainComplex.mappingCocone.inl
          (completedScalarRoosEndomorphism l E L ι Y P)).v (j + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((integralScalarComplexFunctor l E L ι Y).obj P)
          m j (j + m) rfl).inv) ∧
  (∀ (i j : ℤ) (h : i + 1 = j),
    (CochainComplex.mappingCocone.inr
        (completedScalarRoosEndomorphism l E L ι Y (P⟦m⟧))).1.v i j h ≫
        ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
          (self := eC) m).hom.app P).f j =
      m.negOnePow • ((completedScalarShiftProductIso ι Y P m).hom.f i ≫
        (CochainComplex.mappingCocone.inr
          (completedScalarRoosEndomorphism l E L ι Y P)).1.v
            (i + m) (j + m) (by omega) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((integralScalarComplexFunctor l E L ι Y).obj P)
          m j (j + m) rfl).inv))

/-- The strict derived shift is the descent of this same chain alpha, with the
retained localization comparison. Shifted representatives remain good.
Source: Stacks Tags 011G, 06YS and 08TC
(blueprint: def-pur-completed-scalar-shift-coordinates). -/
def completedScalarShiftIntegralNormalization
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ)
    (eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ) : Prop := by
  exact ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ),
    ∃ hP : integralOperationsGoodComplex l E Y (P.obj⟦m⟧),
      (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι Y) (self := eL) m).hom.app
            (DerivedCategory.Q.obj P.obj) ≫
          ((integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P)⟦m⟧' =
        (integralScalarExtensionOfUniverses l E L ι Y).map
            ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app
            ⟨P.obj⟦m⟧, hP⟩ ≫
          DerivedCategory.Q.map
            ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
              (self := eC) m).hom.app P.obj) ≫
          (DerivedCategory.Q.commShiftIso m).hom.app
            ((integralScalarComplexFunctor l E L ι Y).obj P.obj)

end WeilConjectures
