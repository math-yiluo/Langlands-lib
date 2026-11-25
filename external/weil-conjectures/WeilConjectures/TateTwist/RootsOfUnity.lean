/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!

# The sheaves of roots of unity on the pro-étale site

Let `X` be a scheme and `n` a natural number. The sheaf `μ_n` of `n`-th roots of unity on the
small pro-étale site `X_proét` is the sheafification of the abelian presheaf
```
U ↦ μ_n(Γ(U, 𝒪_U)) = {x ∈ Γ(U, 𝒪_U)ˣ | xⁿ = 1},
```
written additively and lifted to the universe `u + 1` of the coefficient sheaves of
`WeilConjectures.CategoryTheory.RingObjects.EllAdic`. (The presheaf is already an fpqc sheaf,
`μ_n` being representable, but this is not needed: the sheafification is canonically
isomorphic to it.)

For a prime `ℓ`, the `ℓ`-th power maps `μ_{ℓ^{n+1}} ⟶ μ_{ℓ^n}` form the inverse system whose
limit is the Tate module `ℤ_ℓ(1)`, see `WeilConjectures.TateTwist.ProEtale`.

## Main definitions

- `CommRingCat.rootsOfUnityFunctor n`: the functor `R ↦ μ_n(R)` from commutative rings to
  abelian groups, and `CommRingCat.rootsOfUnityPow n m`: the `m`-th power map
  `μ_{m n}(R) ⟶ μ_n(R)`, natural in `R`.
- `AlgebraicGeometry.ProEtale.rootsOfUnityPresheaf X n`: the presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` on
  `X_proét`, and `AlgebraicGeometry.ProEtale.rootsOfUnitySheaf X n`: its sheafification `μ_n`.
- `AlgebraicGeometry.ProEtale.rootsOfUnitySheafPow X n m`: the `m`-th power map
  `μ_{m n} ⟶ μ_n`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CommRingCat

variable (n : ℕ)

/-- The functor `R ↦ μ_n(R)` sending a commutative ring to its group of `n`-th roots of unity,
written additively and lifted to the universe `u + 1`. -/
noncomputable def rootsOfUnityFunctor : CommRingCat.{u} ⥤ Ab.{u + 1} where
  obj R := AddCommGrpCat.of (ULift.{u + 1} (Additive (rootsOfUnity n R)))
  map f := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((restrictRootsOfUnity f.hom n).toAdditive.comp AddEquiv.ulift.toAddMonoidHom))
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

lemma rootsOfUnityFunctor_map_apply_val {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : (rootsOfUnityFunctor n).obj R) :
    (((rootsOfUnityFunctor n).map f x).down.toMul : Sˣ).val =
      f.hom (x.down.toMul : Rˣ).val :=
  rfl

/-- The `m`-th power map `μ_{m n}(R) ⟶ μ_n(R)`, as a monoid homomorphism. -/
def rootsOfUnityPowHom (m : ℕ) (R : Type*) [CommMonoid R] :
    rootsOfUnity (m * n) R →* rootsOfUnity n R where
  toFun x := ⟨x.1 ^ m, (mem_rootsOfUnity _ _).2 (by
    rw [← pow_mul]
    exact (mem_rootsOfUnity _ _).1 x.2)⟩
  map_one' := Subtype.ext (one_pow m)
  map_mul' x y := Subtype.ext (mul_pow x.1 y.1 m)

/-- The `m`-th power map `μ_{m n} ⟶ μ_n`, natural in the commutative ring. -/
noncomputable def rootsOfUnityPow (m : ℕ) :
    rootsOfUnityFunctor.{u} (m * n) ⟶ rootsOfUnityFunctor.{u} n where
  app R := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((rootsOfUnityPowHom n m R).toAdditive.comp AddEquiv.ulift.toAddMonoidHom))
  naturality _ _ f := by
    ext x
    apply ULift.ext
    apply Subtype.ext
    apply Units.ext
    exact (map_pow f.hom _ m).symm

end CommRingCat

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- The presheaf `U ↦ μ_n(Γ(U, 𝒪_U))` of `n`-th roots of unity on the small pro-étale site of
`X`, written additively and lifted to the universe `u + 1`. -/
noncomputable def rootsOfUnityPresheaf : X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  (ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ ⋙ CommRingCat.rootsOfUnityFunctor n

/-- The sheaf `μ_n` of `n`-th roots of unity on the small pro-étale site of `X`: the
sheafification of `U ↦ μ_n(Γ(U, 𝒪_U))`. -/
noncomputable def rootsOfUnitySheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).obj (rootsOfUnityPresheaf X n)

/-- The `m`-th power map `μ_{m n} ⟶ μ_n` of sheaves of roots of unity on `X_proét`. -/
noncomputable def rootsOfUnitySheafPow (m : ℕ) :
    rootsOfUnitySheaf X (m * n) ⟶ rootsOfUnitySheaf X n :=
  (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
    (Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow n m))

end AlgebraicGeometry.ProEtale
