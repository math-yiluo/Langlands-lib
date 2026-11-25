/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Category

/-! # Cohomology of ordinary derived Frobenius pairs

The functor from native Weil complexes below forgets derived equivariant morphisms.
No inverse, fullness, or equivalence of derived categories is asserted.

(blueprint: def-sf-native-derived-pair-cohomology)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures.NativePairCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (.of k₀))]

/-- Ordinary derived objects with an invertible derived Frobenius structure. -/
abbrev Pairs := IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory

/-- Exact Frobenius pullback commutes with ordinary derived cohomology. -/
def homology (n : ℤ) : Pairs k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mapOfNatIso
    ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategoryHomologyFunctorIso n)

/-- The action on the underlying derived object of a native Weil complex is the
localization of its termwise action. -/
def theta :
    (WeilComplex.forget (k₀ := k₀) (l := l) (X := X)) ⋙
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory ≅
      WeilComplex.forget :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι (WeilComplex.objectProperty k₀ l X))
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l X)))

/-- Forget native derived equivariance while retaining its induced invertible action. -/
def native : WeilComplex k₀ l X ⥤ Pairs k₀ l X where
  obj K := IsoAlgebra.mk (WeilComplex.forget.obj K) ((theta k₀ l X).app K)
  map {K L} f :=
    ⟨{ f := WeilComplex.forget.map f
       h := (theta k₀ l X).hom.naturality f }⟩
  map_id K := by
    apply (IsoAlgebra.forget _).map_injective
    exact WeilComplex.forget.map_id K
  map_comp f g := by
    apply (IsoAlgebra.forget _).map_injective
    exact WeilComplex.forget.map_comp f g

end WeilConjectures.NativePairCohomology
