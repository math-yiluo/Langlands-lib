/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.SchemeGaloisIterate

/-!
# Operators of Frobenius correspondences with finite coefficients

Let `Λ` be a finite coefficient ring, `a : X ⟶ s` a morphism admitting a compactification and
`h : X ⟶ X` a proper endomorphism over `s`, that is `h ≫ a = a`. For a cohomological
correspondence `ψ : Lh^* K ⟶ K` on `K ∈ D(X_ét, Λ)` (not necessarily invertible), its operator
on compactly supported cohomology is
```
T(ψ) = RΓ_c(X, ψ) ∘ h^♯ : RΓ_c(X, K) ⟶ RΓ_c(X, Lh^* K) ⟶ RΓ_c(X, K),
```
where the pullback `h^♯` is induced by the unit of `Lh^* ⊣ Rh_*`:
```
Ra_! K ⟶ Ra_! Rh_* Lh^* K ≅ Ra_! Rh_! Lh^* K ≅ R(h ≫ a)_! Lh^* K = Ra_! Lh^* K.
```
For the base change `Φ_X` of the scheme Frobenius of a model `X₀` of `X` and a Frobenius
correspondence `ψ : LΦ_X^* K ⟶ K`, the operator of the iterate `ψ_m`
(`AlgebraicGeometry.Etale.weilDatumIterate`) for the graph `c_m` of `Φ_X^m` is
`T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ (Φ_X^m)^♯`, and the stalk of `ψ_m` at a fixed point `x̄` of
`Φ_X^m` is the endomorphism `ψ_{m,x̄}` of `K_x̄` (blueprint
`definition-frobenius-correspondences-their-operators`, for finite coefficients `A`).

## Main definitions

- `AlgebraicGeometry.Etale.lowerShriekPullback`: the pullback `h^♯ : Ra_! ⟶ Lh^* ⋙ Ra_!`.
- `AlgebraicGeometry.Etale.correspondenceOperator`: the operator `T(ψ)` on `RΓ_c(X, K)`.
- `AlgebraicGeometry.Etale.frobeniusCompactOperator`: the operator `T_{c_m}(ψ_m)`.
- `AlgebraicGeometry.Etale.frobeniusStalkMap`: the stalk `ψ_{m,x̄}` at a fixed point.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable {X s : Scheme.{u}} {a : X ⟶ s}

/-- The iterates of a proper endomorphism are proper. -/
instance isProper_iterateHom (g : X ⟶ X) [IsProper g] (m : ℕ) : IsProper (iterateHom g m) := by
  induction m with
  | zero => rw [iterateHom_zero]; infer_instance
  | succ m ih => rw [iterateHom_succ]; infer_instance

/-- The iterates of an endomorphism over `s` lie over `s`. -/
lemma iterateHom_comp_of_comp_eq {g : X ⟶ X} (hg : g ≫ a = a) (m : ℕ) :
    iterateHom g m ≫ a = a := by
  induction m with
  | zero => rw [iterateHom_zero, Category.id_comp]
  | succ m ih => rw [iterateHom_succ, Category.assoc, ih, hg]

end ProEtale

namespace Etale

open Scheme

open ProEtale (iterateHom isProper_iterateHom iterateHom_comp_of_comp_eq)

variable {X s : Scheme.{u}} {a : X ⟶ s}

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [QuasiCompact a] [HasCompactification a]

/-- The *pullback on compactly supported cohomology* `h^♯ : Ra_! ⟶ Lh^* ⋙ Ra_!` along a proper
endomorphism `h` over `s` (`h ≫ a = a`), for finite coefficients: the composite
```
Ra_! K ⟶ Ra_! Rh_* Lh^* K ≅ Ra_! Rh_! Lh^* K ≅ R(h ≫ a)_! Lh^* K = Ra_! Lh^* K
```
of the unit of `Lh^* ⊣ Rh_*`, the identification `Rh_! ≅ Rh_*` of the proper morphism `h` and the
composition isomorphism of the lower shriek (blueprint
`definition-frobenius-correspondences-their-operators`). -/
noncomputable def lowerShriekPullback (h : X ⟶ X) [IsProper h] (ha : h ≫ a = a) :
    R(a)_![ModuleCat.{u + 1} Λ] ⟶
      L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ R(a)_![ModuleCat.{u + 1} Λ] :=
  have : HasCompactification (h ≫ a) := by rw [ha]; infer_instance
  have : QuasiCompact (h ≫ a) := by rw [ha]; infer_instance
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar _ h).inv _ ≫
        (rightDerivedLowerShriekCompIso Λ h a).inv ≫ (rightDerivedLowerShriekCongrIso Λ ha).hom)

/-- The *operator* `T(ψ) = RΓ_c(X, ψ) ∘ h^♯` on `RΓ_c(X, K)` of a cohomological correspondence
`ψ : Lh^* K ⟶ K` along a proper endomorphism `h` over `s`, for finite coefficients (blueprint
`definition-frobenius-correspondences-their-operators`). The correspondence `ψ` need not be
invertible. -/
noncomputable def correspondenceOperator (h : X ⟶ X) [IsProper h] (ha : h ≫ a = a)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((h)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K ⟶
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
    ((lowerShriekPullback Λ h ha).app K ≫ (R(a)_![ModuleCat.{u + 1} Λ]).map ψ)

/-- Blueprint `definition-frobenius-correspondences-their-operators` (the operator, finite
coefficients): for a Frobenius correspondence `ψ : LΦ^* K ⟶ K` along a proper endomorphism `Φ`
over `s` (for instance the base change `Φ_X` of the scheme Frobenius of a model of `X`) and
`m : ℕ`, the operator `T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ (Φ^m)^♯` on `RΓ_c(X, K)` of the iterate
`ψ_m : L(Φ^m)^* K ⟶ K` (`AlgebraicGeometry.Etale.weilDatumIterate`), the cohomological
correspondence for the graph `c_m = (𝟙, Φ^m)`. -/
noncomputable def frobeniusCompactOperator (Φ : X ⟶ X) [IsProper Φ] (hΦ : Φ ≫ a = a)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((Φ)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) (m : ℕ) :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K ⟶
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K :=
  correspondenceOperator Λ (iterateHom Φ m) (iterateHom_comp_of_comp_eq hΦ m)
    (weilDatumIterate ψ m)

variable {Λ} in
/-- Blueprint `definition-frobenius-correspondences-their-operators` (the stalk maps, finite
coefficients): the stalk `ψ_{x̄} : K_x̄ ⟶ K_x̄` of a cohomological correspondence
`ψ : Lh^* K ⟶ K` at a fixed point `x̄ : s ⟶ X` of `h` (`x̄ ≫ h = x̄`), the composite
```
RΓ(s, Lx̄^* K) ≅ RΓ(s, Lx̄^* Lh^* K) --RΓ(s, Lx̄^* ψ)--> RΓ(s, Lx̄^* K).
```
For `h = Φ^m` and the iterate `ψ_m` this is the stalk map `ψ_{m,x̄}` of the blueprint. -/
noncomputable def frobeniusStalkMap {h : X ⟶ X} {x : s ⟶ X} (hx : x ≫ h = x)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L((h)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).obj
        ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).obj
        ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
    ((leftDerivedUpperStarComp _ x h x hx.symm).hom.app K ≫
      (L((x)^*[ModuleCat.{u + 1} Λ])).map ψ)

end Etale

end AlgebraicGeometry
