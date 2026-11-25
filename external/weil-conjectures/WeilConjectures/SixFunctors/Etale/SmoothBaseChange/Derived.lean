/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Data.Nat.Factorization.Induction

/-!
# Derived smooth base change

Fix a commutative ring `Λ` and a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact and quasi-separated. The smooth base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` says that the degreewise
base-change maps `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` are isomorphisms for every sheaf `F` which is
torsion of orders invertible on `S`. This file deduces the derived forms of the theorem: the
derived base-change map

`BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)`

of `AlgebraicGeometry.Etale.baseChange` is an isomorphism for every bounded below complex `K`
whose cohomology sheaves are torsion of orders invertible on `S`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth_of_qcqs`: the classical form of
  the theorem, `g⁻¹ R^q f_* F ≅ R^q f'_* v⁻¹ F` for `g` smooth and `f` qcqs (blueprint
  `sk-rem-rest`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_isGE_of_isLE`: the finite-range comparison
  (blueprint `theorem-smooth-base-change-classical-torsion-2`).
- `AlgebraicGeometry.Etale.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app`
  and its companions: the bounded-below truncation criterion (blueprint
  `theorem-pbc-injective-acyclicity`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_bounded_of_smooth`: bounded complexes with
  allowable torsion (blueprint `theorem-smooth-base-change-classical-torsion-2`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_smooth`: bounded below complexes with allowable
  torsion (blueprint `theorem-smooth-base-change-classical-torsion-2--1`).
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth`: bounded
  constructible complexes of sheaves of modules over a ring killed by an integer invertible on
  `S` (blueprint `theorem-smooth-base-change-all-admissible--1`).

## Implementation notes

The blueprint compares the hypercohomology spectral sequences of the two sides. Here the
comparison is made by dévissage along the truncation triangles
(`DerivedCategory.Plus.isIso_app_of_isGE_of_isLE`), using that the derived base-change map
commutes with the shifts (`AlgebraicGeometry.Etale.commShift_baseChange`); for bounded below
complexes, `Hⁿ` of both sides only depends on `τ_{≤ n} K`
(`DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

open DerivedCategory.Plus.TStructure (t)

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The set of primes invertible on a scheme `S`. -/
def Scheme.invertiblePrimes (S : Scheme.{u}) : Set ℕ :=
  {p | p.Prime ∧ IsUnit (p : Γ(S, ⊤))}

/-- A sheaf which is torsion with prime divisors invertible on `S` is torsion of orders
invertible on `S`. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes {S T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheafOfPrimes S.invertiblePrimes F] : IsTorsionSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨n, hn, hP, hx⟩ :=
      IsTorsionSheafOfPrimes.exists_nsmul_eq_zero (P := S.invertiblePrimes) Ω s x
    exact ⟨n, hn, isUnit_natCast_of_forall_mem_primeFactors n hn fun p hp ↦ (hP p hp).2, hx⟩

/-- Being torsion of orders invertible on `S` is invariant under isomorphisms of sheaves. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.of_iso {S T : Scheme.{u}}
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ≅ G)
    [IsTorsionSheafOfInvertibleOrder S F] : IsTorsionSheafOfInvertibleOrder S G where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    let ψ := (pointSmallEtale s).sheafFiber.mapIso φ
    obtain ⟨n, hn, hu, hx⟩ :=
      IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) (F := F) Ω s
        (ψ.inv.hom x)
    refine ⟨n, hn, hu, ?_⟩
    have : ψ.hom.hom (ψ.inv.hom x) = x := by
      rw [← ModuleCat.comp_apply, ψ.inv_hom_id, ModuleCat.id_apply]
    rw [← this, ← map_nsmul, hx, map_zero]

/-- The property of being torsion of orders invertible on `S`, as a property of sheaves. -/
def Scheme.isTorsionSheafOfInvertibleOrder (S : Scheme.{u}) (T : Scheme.{u}) :
    ObjectProperty (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsTorsionSheafOfInvertibleOrder S F

instance (S T : Scheme.{u}) :
    (isTorsionSheafOfInvertibleOrder Λ S T).IsClosedUnderIsomorphisms where
  of_iso φ h := by
    have : IsTorsionSheafOfInvertibleOrder S _ := h
    exact IsTorsionSheafOfInvertibleOrder.of_iso Λ φ

/-- Blueprint `sk-rem-rest`: the *classical form* of the smooth base change theorem, in which
the roles of the two legs of the square are exchanged with respect to `prose-08-06`. For a
Cartesian square

```
X' --v--> X
|         |
f'        f
v         v
S' --g--> S
```

with `g` **smooth** and `f` quasi-compact and quasi-separated, and a sheaf `F` of `Λ`-modules
on `X_ét` all of whose geometric stalks are torsion of orders invertible on `S`, the
base-change map `g⁻¹ R^q f_* F ⟶ R^q f'_* v⁻¹ F` is an isomorphism in every degree `q`.

The base-change map of `AlgebraicGeometry.Etale.baseChangeHomologyMap` attached to the square
`sq : IsPullback v f' f g` is by construction `g⁻¹ R^q f_* F ⟶ R^q f'_* v⁻¹ F`: it pulls back
along the bottom leg and pushes forward along the right leg. So the classical form is
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` for this square, with the smooth
morphism `g` in the role of the morphism pulled back along. -/
theorem Etale.isIso_baseChangeHomologyMap_of_smooth_of_qcqs {X S S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (v : X' ⟶ X) (f' : X' ⟶ S') [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] (sq : IsPullback v f' f g) (q : ℤ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  Etale.isIso_baseChangeHomologyMap_of_smooth Λ g f v f' sq q F

/-- Blueprint `sk-rem-rest`: the isomorphism `g⁻¹ R^q f_* F ≅ R^q f'_* v⁻¹ F` of the classical
form of the smooth base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth_of_qcqs`). -/
noncomputable def Etale.smoothBaseChangeHomologyIso {X S S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (v : X' ⟶ X) (f' : X' ⟶ S') [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] (sq : IsPullback v f' f g) (q : ℤ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheafOfInvertibleOrder S F] :
    (Etale.baseChangeSourceFunctor Λ g f q).obj F ≅
      (Etale.baseChangeTargetFunctor Λ v f' q).obj F :=
  have := Etale.isIso_baseChangeHomologyMap_of_smooth_of_qcqs Λ f g v f' sq q F
  asIso (Etale.baseChangeHomologyMap Λ sq q F)

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The derived base-change map is an isomorphism at a sheaf `F` placed in degree `0` if and only
if all the degreewise base-change maps at `F` are isomorphisms. -/
lemma Etale.isIso_baseChange_app_singleFunctor_obj_iff (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ↔
      ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  -- This file elaborates the statement with the shortcut instance
  -- `ModuleCat.isGrothendieckAbelian_of_commRing`, while
  -- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff` was elaborated with Mathlib's
  -- `instIsGrothendieckAbelianModuleCat`. The two are proofs of the same proposition, but
  -- identifying the derived categories built on them makes the kernel unfold huge terms.
  -- Rewriting the instance first keeps every later comparison syntactic.
  have hS : ModuleCat.isGrothendieckAbelian_of_commRing Λ = instIsGrothendieckAbelianModuleCat Λ :=
    proof_irrel _ _
  rw [hS]
  exact (DerivedCategory.Plus.isIso_iff _).trans
    (forall_congr' fun q ↦ (Etale.isIso_baseChangeHomologyMap_iff Λ sq q F).symm)

/-- The source `p^* ∘ Rg_*` of the derived base-change map does not lower the cohomological
degree. -/
lemma Etale.isZero_homologyFunctor_baseChangeSource_obj (p : X ⟶ S) (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((p)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  refine IsZero.of_iso ?_ (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
    q |>.app _).symm
  exact Functor.map_isZero (p)^*[ModuleCat.{u + 1} Λ]
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ K n hq)

/-- The target `Rh_* ∘ e^*` of the derived base-change map does not lower the cohomological
degree. -/
lemma Etale.isZero_homologyFunctor_baseChangeTarget_obj (e : Y ⟶ T) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((h)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
  have : (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
    intro i hi
    refine IsZero.of_iso ?_ (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
      i |>.app _).symm
    exact Functor.map_isZero (e)^*[ModuleCat.{u + 1} Λ]
      (DerivedCategory.Plus.isZero_homology_of_isGE K n i hi)
  exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ n hq

/-- Blueprint `theorem-pbc-injective-acyclicity`: for `K ∈ D⁺(T_ét)`, only the
cohomology sheaves of `K` in degrees `≤ n` contribute to `Hⁿ(Rg_* K)`: the map
`Hⁿ(Rg_* τ_{≤ n} K) ⟶ Hⁿ(Rg_* K)` is an isomorphism. -/
lemma Etale.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      (R+((g)_*[ModuleCat.{u + 1} Λ]).map ((t.truncLEι n).app K))) :=
  DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app _
    (fun K n _ _ hq ↦ Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ K n hq)
    K n

/-- Blueprint `theorem-pbc-injective-acyclicity`, after pullback: the map
`Hⁿ(p^* Rg_* τ_{≤ n} K) ⟶ Hⁿ(p^* Rg_* K)` is an isomorphism. -/
lemma Etale.isIso_homologyFunctor_map_baseChangeSource_map_truncLEι_app (p : X ⟶ S) (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((R+((g)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((p)^*[ModuleCat.{u + 1} Λ])).map
        ((t.truncLEι n).app K))) :=
  DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app _
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ p g K n q hq) K n

/-- Blueprint `theorem-pbc-injective-acyclicity`, for `h_*`: the map
`Hⁿ(Rh_* e^* τ_{≤ n} K) ⟶ Hⁿ(Rh_* e^* K)` is an isomorphism. -/
lemma Etale.isIso_homologyFunctor_map_baseChangeTarget_map_truncLEι_app (e : Y ⟶ T) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙ R+((h)_*[ModuleCat.{u + 1} Λ])).map
        ((t.truncLEι n).app K))) :=
  DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app _
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ e h K n q hq) K n

/-- Blueprint `theorem-smooth-base-change-classical-torsion-2`: let `K ∈ D⁺(T_ét)` have cohomology
sheaves concentrated in `[a, b]`. If the comparison of the two hypercohomology spectral sequences is
an isomorphism on every `E₂`-term, i.e. the base-change map
`p⁻¹ R^i g_* Hʲ(K) ⟶ R^i h_* e⁻¹ Hʲ(K)` is an isomorphism for all `i` and `j`, then the derived
base-change map `BC(K)` is an isomorphism. -/
theorem Etale.isIso_baseChange_app_of_isGE_of_isLE (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a b : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hK : ∀ i j, IsIso (Etale.baseChangeHomologyMap Λ sq i
      ((DerivedCategory.Plus.homologyFunctor _ j).obj K))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  let P : ObjectProperty (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := fun F ↦
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have : P.IsClosedUnderIsomorphisms := ⟨fun φ h ↦
    (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.Plus.singleFunctor _ 0).mapIso φ)).1 h⟩
  exact DerivedCategory.Plus.isIso_app_of_bounded _ P (fun _ hF ↦ hF) K a b fun j ↦
    (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq _).2 fun i ↦ hK i j

variable (p) in
/-- The derived base-change map of a smooth base change square is an isomorphism at a sheaf which
is torsion of orders invertible on `S`, placed in degree `0`. -/
lemma Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheafOfInvertibleOrder S F] :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
    Etale.isIso_baseChangeHomologyMap_of_smooth Λ p g e h sq q F

variable (p) in
/-- The derived base-change map of a smooth base change square is an isomorphism at every bounded
below complex whose cohomology sheaves are torsion of orders invertible on `S`. -/
theorem Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ j, IsTorsionSheafOfInvertibleOrder S
      ((DerivedCategory.Plus.homologyFunctor _ j).obj K)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  DerivedCategory.Plus.isIso_app_of_forall_homology _ (isTorsionSheafOfInvertibleOrder Λ S T)
    (fun F hF ↦ have : IsTorsionSheafOfInvertibleOrder S F := hF
      Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth Λ p sq F)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ p g K n q hq)
    (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ e h K n q hq) K hK

/-- Blueprint `theorem-smooth-base-change-classical-torsion-2`, bounded version: the objects of
`D^b_P-tor(X_ét)`, the bounded complexes of `D⁺(X_ét, Λ)` whose cohomology sheaves have
`P`-torsion geometric stalks, for a set `P` of primes. The bounded below version is
`AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomologyOfPrimes`. -/
noncomputable def Etale.DerivedCategory.Plus.boundedTorsionHomologyOfPrimes (X : Scheme.{u})
    (P : Set ℕ) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  t.bounded ⊓ Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P

variable (p) in
/-- Blueprint `theorem-smooth-base-change-classical-torsion-2`: for a Cartesian square with `p`
smooth and `g` quasi-compact and quasi-separated, and `P` the set of primes invertible on `S`, the
derived base-change map `BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)` is an isomorphism for every
`K ∈ D^b_P-tor(T_ét)`. Both sides are then bounded below; the comparison is made in
`D⁺(X_ét, Λ)`. -/
theorem Etale.isIso_baseChange_app_of_bounded_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.boundedTorsionHomologyOfPrimes Λ T S.invertiblePrimes K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hK⟩ := hK
  exact DerivedCategory.Plus.isIso_app_of_bounded _ (isTorsionSheafOfInvertibleOrder Λ S T)
    (fun F hF ↦ have : IsTorsionSheafOfInvertibleOrder S F := hF
      Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth Λ p sq F) K a b fun j ↦
    have := hK j
    IsTorsionSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes Λ _

variable (p) in
/-- Blueprint `theorem-smooth-base-change-classical-torsion-2--1`: for a Cartesian square with `p`
smooth and `g` quasi-compact and quasi-separated, and a bounded below complex
`K ∈ D⁺_P-tor(T_ét)` whose cohomology sheaves are torsion with prime divisors invertible on `S`,
the derived base-change map `BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)` is an isomorphism. -/
theorem Etale.isIso_baseChange_app_of_smooth [Smooth p] [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ T S.invertiblePrimes K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ p sq K fun j ↦
    have := hK j
    IsTorsionSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes Λ _

/-- If a nonzero integer `N` kills the coefficient ring `Λ` and is invertible on `S`, then every
sheaf of `Λ`-modules is torsion of orders invertible on `S`. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero {S T : Scheme.{u}} (N : ℕ)
    (hN₀ : N ≠ 0) (hN : (N : Λ) = 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x :=
    ⟨N, Nat.pos_of_ne_zero hN₀, hNS, by rw [← Nat.cast_smul_eq_nsmul Λ, hN, zero_smul]⟩

variable (p) in
/-- Blueprint `theorem-smooth-base-change-all-admissible--1`: for a Cartesian square with `p`
smooth and `g` quasi-compact and quasi-separated, and a coefficient ring `Λ` killed by a nonzero
integer `N` invertible on `S`, the derived base-change map
`BC(K) : p^*(Rg_* K) ⟶ Rh_*(e^* K)` is an isomorphism for every `K ∈ D^b_c(T_ét, Λ)`. Since
`K` is bounded and `p^*` is exact, `BC(K)` is computed in the bounded below derived
categories. -/
theorem Etale.isIso_baseChange_app_of_boundedConstructible_of_smooth [Smooth p]
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p) (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : Λ) = 0) (hNS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app ⟨K, hK.1.1⟩) :=
  Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ p sq _ fun _ ↦
    IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀ hN hNS _

end AlgebraicGeometry
