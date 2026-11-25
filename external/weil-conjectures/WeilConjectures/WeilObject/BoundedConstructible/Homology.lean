/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.WeilObject.BoundedConstructible.Defs
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# Weil structures on homology sheaves of bounded constructible complexes

Let `ℓ` be a prime, `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ` the condensed ring of `ℚ̄_ℓ`, and
let `X` be a separated scheme of finite type over `Spec k` with an automorphism `e : X ≅ X` over
`Spec k`. Write `e^* = (e.hom.left)^*⟦ℚ̲̄_ℓ⟧` for the pullback on module objects and
`Le^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ e.hom` for the derived pullback on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.

Since `Le^*` is computed levelwise by the exact functor `e^*`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`), the `n`-th homology sheaf
of a Weil object `(K, φ_K)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is a Weil sheaf
(`ProEtale.CondensedRing.WeilSheaf`), with the structure isomorphism
```
e^* Hⁿ(K) ≅ Hⁿ(Le^* K) --Hⁿ(φ_K)--> Hⁿ(K),
```
the comparison `Hⁿ ⋙ e^* ≅ Le^* ⋙ Hⁿ` (`ProEtale.CondensedRing.weilHomologyComparison`) being
assembled from `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`. The homology
functor `ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor` is the transport
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` along this comparison.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor`: the `n`-th homology sheaf,
  a functor `WeilBoundedConstructible ℓ e.hom ⥤ WeilSheaf ℓ e`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X) (n : ℤ)

/-- The Frobenius comparison of the `n`-th homology sheaf: `Hⁿ ⋙ e^* ≅ Le^* ⋙ Hⁿ` on
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, that is `e^* Hⁿ(K) ≅ Hⁿ(Le^* K)`, the composite
```
Hⁿ(-) ⋙ e^* ≅ D(e^*) ⋙ Hⁿ(-) ≅ L(e^*) ⋙ Hⁿ(-) ≅ Hⁿ(Le^* -)
```
of the commutation `Functor.mapDerivedCategoryHomologyFunctorIso` of the exact functor `e^*`
with homology, the identification `leftDerivedUpperStarIsoMapDerivedCategory` of the derived
pullback with the levelwise pullback, and the compatibility
`boundedConstructibleUpperStarCompatibility` of `Le^*` with the inclusion `ι` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def weilHomologyComparison :
    ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n) ⋙
        (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom ⋙
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapDerivedCategoryHomologyFunctorIso n ≪≫
        Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ℓ)
            e.hom.left).symm _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
        e.hom).symm _ ≪≫
    Functor.associator _ _ _

/-- The `n`-th homology sheaf `Hⁿ(K)` of a Weil object `(K, φ_K)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, as a Weil
sheaf: its structure isomorphism is `e^* Hⁿ(K) ≅ Hⁿ(Le^* K) ≅ Hⁿ(K)` given by
`weilHomologyComparison` and `Hⁿ(φ_K)`. -/
noncomputable def WeilBoundedConstructible.homologyFunctor :
    WeilBoundedConstructible ℓ e.hom ⥤ WeilSheaf ℓ e :=
  IsoAlgebra.mapOfNatIso (weilHomologyComparison ℓ e n)

@[simp]
lemma WeilBoundedConstructible.homologyFunctor_obj_carrier (K : WeilBoundedConstructible ℓ e.hom) :
    ((WeilBoundedConstructible.homologyFunctor ℓ e n).obj K).carrier =
      (DerivedCategory.homologyFunctor _ n).obj K.carrier.obj :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
