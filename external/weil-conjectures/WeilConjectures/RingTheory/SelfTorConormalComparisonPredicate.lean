/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.ConormalExteriorModule
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Koszul normalization of the comparison. For every tuple of ideal elements, lift
its Koszul augmentation to any projective resolution of the quotient. A degree-n wedge,
after tensoring with the quotient, is a cycle. Its image in resolution homology is
the value of the comparison on the wedge of the corresponding conormal classes.
This fixes the comparison, since these wedges generate the exterior power.
Source: Stacks Project, Tags 09PQ and 062I.
(blueprint: new-r4-self-tor-conormal-comparison). 
(blueprint: new-r4-self-tor-conormal-predicate)
-/
def IsSelfTorConormalComparison (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) : Prop :=
  ∀ (r : ℕ) (g : Fin r → I) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex),
    a.f 0 ≫ P.π.f 0 =
      ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) →
    let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
    let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    ∀ (v : Fin n → (Fin r →₀ A)) (z : (T.obj K).cycles n),
      (T.obj K).iCycles n z =
        (exteriorPower.ιMulti A n v) ⊗ₜ[A] (1 : A ⧸ I) →
      (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom
          (c (exteriorPower.ιMulti (A ⧸ I) n
            (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))) =
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
          (T.map a)) ((T.obj K).homologyπ n z)


end AlgebraicGeometry
