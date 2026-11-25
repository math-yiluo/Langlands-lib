/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Single

/-!
# Determinant normalization of the Koszul dual comparison

Source: Stacks Project, duality.tex, Tag 0BQZ, lemma-regular-immersion-ext, its
comparison induced by the quotient map (blueprint: def-sc-koszul-conormal-comparison).

## Main definitions

* `koszulNormalDeterminant`: the restricted normal determinant module.
* `koszulConormalVector`: the class of a free-module vector in the conormal module.
* `IsKoszulConormalComparison`: determinant normalization of the top comparison.
-/

@[expose] public section

universe uC

open CategoryTheory

namespace ExteriorAlgebra

/-- The normal determinant `⋀^r_B Hom_B(I/I²,B)` as an `A`-module by restriction.
Source: Stacks Project, Tag 0BQZ (blueprint: def-sc-koszul-conormal-comparison). -/
noncomputable def koszulNormalDeterminant (A : Type uC) [CommRing A] (I : Ideal A)
    (r : ℕ) : ModuleCat.{uC} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent)))

/-- The map from the free module to the conormal module sending the `i`th basis vector
 to the class of `f i`. Source: Stacks Project, Tag 0BQZ
(blueprint: def-sc-koszul-conormal-comparison). -/
noncomputable def koszulConormalVector (A : Type uC) [CommRing A] (I : Ideal A)
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    (Fin r →₀ A) →ₗ[A] I.Cotangent :=
  Finsupp.linearCombination A
    (fun i ↦ I.toCotangent ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩)

/-- The value in the normal determinant of a comparison on a degree-`r` dual vector.
Source: Stacks Project, Tag 0BQZ (blueprint: def-sc-koszul-conormal-comparison). -/
noncomputable def koszulComparisonValue (A : Type uC) [CommRing A] (I : Ideal A) (r : ℕ)
    (f : Fin r → A)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (x : (koszulComplex A r f).X r ⟶ ModuleCat.of A A) :
    ⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) r
    (koszulNormalDeterminant A I r)).hom (φ.f r x)

/-- A comparison is canonical when its top component is the determinant pairing on
conormal classes, after reducing its input functional modulo `I` and multiplying by the contraction
order sign `(-1)^(r*(r-1)/2)`. This condition fixes
all components, since the target is supported only in degree `r`.
Source: Stacks Project, Tag 0BQZ (blueprint: def-sc-koszul-conormal-comparison). -/
def IsKoszulConormalComparison (A : Type uC) [CommRing A] (I : Ideal A) (r : ℕ)
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r)) : Prop :=
  ∀ (x : (koszulComplex A r f).X r ⟶ ModuleCat.of A A)
    (v : Fin r → (Fin r →₀ A)),
    exteriorPower.pairingDual (A ⧸ I) I.Cotangent r
        (koszulComparisonValue A I r f φ x)
        (exteriorPower.ιMulti (A ⧸ I) r (fun i ↦ koszulConormalVector A I r f hf (v i))) =
      (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
        Ideal.Quotient.mk I (x.hom (exteriorPower.ιMulti A r v))

end ExteriorAlgebra
