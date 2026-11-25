/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion

/-!

# Torsion étale sheaves and torsion cohomology

Let `Λ` be a commutative ring and `X` a scheme. This file defines the two
torsion conditions entering the statement of the proper base change theorem:

- `AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`: a sheaf `F` of `Λ`-modules on the small
  étale site of `X` is *torsion* if the stalk of `F` at every geometric point of `X` is
  a torsion abelian group. A geometric point `Spec Ω ⟶ X`, with `Ω` a separably closed
  field, induces a point of the small étale site (`Scheme.pointSmallEtale`), and the
  stalk of `F` is its fiber `CategoryTheory.GrothendieckTopology.Point.sheafFiber` at
  this point. Since the geometric points form a conservative family, this stalkwise
  condition agrees with the classical definition [Stacks 03SA] that `F` is the filtered
  union of its `n`-torsion subsheaves.
  The bridge `AlgebraicGeometry.Scheme.isTorsionModuleSheaf_iff_isTorsion` identifies it with the
  local condition `CategoryTheory.Sheaf.IsTorsion` (every section is locally torsion) on the
  underlying sheaf of abelian groups.
- `AlgebraicGeometry.Etale.DerivedCategory.Plus.moduleTorsionHomology`: the property of an
  object of the bounded below derived category of étale sheaves of `Λ`-modules that all
  its cohomology sheaves are torsion.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfPrimes` and
  `AlgebraicGeometry.Etale.DerivedCategoryPlusTorsionOfPrimes`: `P`-torsion sheaves, for a set
  `P` of primes, and the category `D⁺_P-tor(X, Λ)` of bounded below complexes with `P`-torsion
  cohomology sheaves.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`: the refinement of
  `IsTorsionModuleSheaf` in which the orders are required to be invertible on a second scheme
  `S`. This is the coefficient condition of the smooth base change theorem, and it
  implies `IsTorsionModuleSheaf`. Such a sheaf is the filtered colimit of subsheaves killed by
  integers invertible on `S`
  (`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit`).

Torsion refers throughout to the underlying abelian group, not to the `Λ`-module
structure: for `Λ = ℤ` the definition specializes to torsion abelian sheaves, the
setting of the classical proper base change theorem [Stacks 0DDE], and for a coefficient
ring `Λ` which is torsion as an additive group — in particular for the finite rings
`Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf.of_isTorsion`).

The design follows `AlgebraicGeometry.Scheme.IsFiniteSheaf` of
`WeilConjectures.ConstructibleSheaf.Defs` (stalkwise condition at geometric points) and
`AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology` of
`WeilConjectures.DerivedCategory.Constructible` (homologywise `ObjectProperty` on a
derived category).

Following the convention of the `SixFunctors` folder, the coefficient category has
`Hom`-types in the universe `u + 1`, one above the universe `u` of the base schemes: it
is `ModuleCat.{u + 1} Λ` for a commutative ring `Λ : Type (u + 1)`, mathlib insisting
that the ring and the modules live in the same universe. The `Type u`-valued geometric
points of the small étale site nevertheless have fibers in `ModuleCat.{u + 1} Λ`, the
`u`-indexed filtered colimits computing them being obtained by shrinking from the
`u + 1`-indexed ones, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`.

-/

@[expose] public section

universe w u

open CategoryTheory Limits

local instance (X : AlgebraicGeometry.Scheme.{u}) :
    LocallySmall.{u} X.Etale :=
  CategoryTheory.locallySmall_self _

namespace AlgebraicGeometry

open Scheme

section TorsionSheaf

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *torsion* if the stalk
of `F` at every geometric point of `X` is a torsion abelian group, i.e. every element of
every geometric stalk is killed by a positive integer. Torsion refers to the underlying
abelian group of the stalk, not to its `Λ`-module structure; for `Λ = ℤ` this is the
classical notion of a torsion abelian sheaf [Stacks 03SA].

This is the notion of torsion sheaf of blueprint `definition-torsion-sheaves--1`, phrased with
geometric stalks, which the blueprint notes is equivalent to local killing of sections. -/
class Scheme.IsTorsionModuleSheaf {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  isTorsion_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsAddTorsion (↥((pointSmallEtale s).sheafFiber.obj F))

/-- A sheaf of `Λ`-modules on the small étale site is torsion in the stalkwise sense
`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf` if and only if its underlying sheaf of abelian
groups is torsion in the local sense `CategoryTheory.Sheaf.IsTorsion`: every section is locally
torsion. -/
lemma Scheme.isTorsionModuleSheaf_iff_isTorsion {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionModuleSheaf F ↔
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).IsTorsion := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  rw [isTorsion_iff_isAddTorsion_sheafFiber]
  refine ⟨fun h Ω _ _ s ↦ ?_, fun h ↦ ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · let e := ((pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F
    have : IsAddTorsion ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((pointSmallEtale s).sheafFiber.obj F)) :=
      IsTorsionModuleSheaf.isTorsion_sheafFiber (F := F) Ω s
    exact IsAddTorsion.of_surjective (f := e.inv.hom)
      (ConcreteCategory.bijective_of_isIso e.inv).2 this
  · let e := ((pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F
    have : IsAddTorsion ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((pointSmallEtale s).sheafFiber.obj F)) :=
      IsAddTorsion.of_surjective (f := e.hom.hom) (ConcreteCategory.bijective_of_isIso e.hom).2
        (h Ω s)
    exact this

/-- If the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ`
is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then every sheaf of `Λ`-modules on the small étale site is
torsion: every stalk is a `Λ`-module, and is killed elementwise by the additive order of
`1 : Λ`. -/
lemma Scheme.IsTorsionModuleSheaf.of_isTorsion {Λ : Type (u + 1)} [CommRing Λ]
    (hΛ : IsAddTorsion Λ) {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionModuleSheaf F where
  isTorsion_sheafFiber _ _ _ _ := IsAddTorsion.module_of_torsion Λ _ hΛ

/-- Every sheaf of modules over a finite coefficient ring is torsion. -/
instance {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : IsTorsionModuleSheaf F :=
  .of_isTorsion isAddTorsion_of_finite F

/-- A quotient of a torsion sheaf is torsion. -/
lemma Scheme.IsTorsionModuleSheaf.of_epi {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (π : F ⟶ G) [Epi π]
    [IsTorsionModuleSheaf F] : IsTorsionModuleSheaf G where
  isTorsion_sheafFiber Ω _ _ s x := by
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have :=
      ((pointSmallEtale s).skyscraperSheafAdjunction (A := ModuleCat.{u + 1} Λ)).isLeftAdjoint
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((pointSmallEtale s).sheafFiber.map π)).mp inferInstance x
    obtain ⟨n, hn, hy⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
      (IsTorsionModuleSheaf.isTorsion_sheafFiber (F := F) Ω s y)
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, by rw [← map_nsmul, hy, map_zero]⟩

open Etale in
/-- The pullback of a torsion sheaf of `Λ`-modules is torsion: the stalk of `f^* F` at a
geometric point `s` is the stalk of `F` at `s ≫ f`. -/
instance isTorsionModuleSheaf_upperStar {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F] :
    IsTorsionModuleSheaf ((f)^*[ModuleCat.{u + 1} Λ].obj F) where
  isTorsion_sheafFiber Ω _ _ s :=
    IsAddTorsion.of_surjective
      (f := ((Etale.upperStarCompSheafFiberIso _ f s).app F).toLinearEquiv.symm.toAddMonoidHom)
      (LinearEquiv.surjective _) (IsTorsionModuleSheaf.isTorsion_sheafFiber Ω (s ≫ f))

/-- A sheaf `F` of `Λ`-modules on the small étale site of `T` is *torsion of orders
invertible on `S`*, for a second scheme `S`, if every element of every geometric stalk of
`F` is killed by a positive integer which is invertible on `S`, i.e. which is a unit of
`Γ(S, ⊤)` (blueprint `sk-def-smooth`, "allowed torsion"). No common annihilator is required,
and invertibility is read globally on `S`, not only near the support of `F`.

This strengthening of `AlgebraicGeometry.Scheme.IsTorsionModuleSheaf` is the coefficient
condition of the smooth base change theorem, where `T` lies over `S` along the morphism
`g : T ⟶ S` of the Cartesian square and the smooth morphism is the one with target `S`.
For `Λ = ℤ/nℤ` with `n` invertible on `S` every sheaf of `Λ`-modules satisfies it, and a
general such sheaf is the filtered union of its `n`-torsion subsheaves over the integers
`n` invertible on `S`. -/
class Scheme.IsTorsionSheafOfInvertibleOrder {Λ : Type (u + 1)} [CommRing Λ] (S : Scheme.{u})
    {T : Scheme.{u}} (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  exists_isUnit_nsmul_eq_zero (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0

/-- A sheaf which is torsion of orders invertible on some scheme `S` is in particular a
torsion sheaf, so that the coefficients allowed by smooth base change are among those
allowed by proper base change. This is not an instance: the scheme `S` cannot be
recovered from the conclusion. -/
lemma Scheme.IsTorsionModuleSheaf.of_isTorsionSheafOfInvertibleOrder
    {Λ : Type (u + 1)} [CommRing Λ] (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] : IsTorsionModuleSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    obtain ⟨n, hn, -, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

/-- A sheaf `F` of `Λ`-modules on the small étale site of `X` is *`P`-torsion*, for a set `P`
of primes, if every element of every geometric stalk of `F` is killed by a positive integer all
of whose prime divisors lie in `P`. This is the condition on the cohomology sheaves in the
categories with allowable torsion of blueprint `theorem-smooth-base-change-classical-torsion-2`
and `definition-constructible-sheaves`. -/
class Scheme.IsTorsionSheafOfPrimes (P : Set ℕ) {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop where
  exists_nsmul_eq_zero (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
    ∃ n : ℕ, 0 < n ∧ (∀ p ∈ n.primeFactors, p ∈ P) ∧ n • x = 0

/-- A `P`-torsion sheaf is in particular a torsion sheaf. This is not an instance: the set `P`
cannot be recovered from the conclusion. -/
lemma Scheme.IsTorsionModuleSheaf.of_isTorsionSheafOfPrimes (P : Set ℕ) {Λ : Type (u + 1)}
    [CommRing Λ] {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfPrimes P F] : IsTorsionModuleSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    obtain ⟨n, hn, -, hx⟩ := Scheme.IsTorsionSheafOfPrimes.exists_nsmul_eq_zero (P := P) Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

/-- A torsion sheaf `F` of `Λ`-modules is the point of a colimit cocone over a filtered diagram
of sheaves, each of which is killed by some positive integer.

This is blueprint `definition-torsion-sheaves--3`: `F` is the colimit of its
`n`-torsion subsheaves `F[n] = ker (n : F ⟶ F)` over the positive integers ordered by
divisibility, because every local section of `F` is, locally, killed by a positive integer;
this lemma only records the existence of some such diagram, which is the form in which it is
used. -/
theorem Scheme.IsTorsionModuleSheaf.exists_isColimit
    (Λ : Type (u + 1)) [CommRing Λ] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Cocone D)
      (_ : IsColimit c), c.pt = F ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ n • 𝟙 (D.obj j) = 0 := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasColimitsOfShape ℕ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    inferInstance
  have : AB5OfSize.{0, 0} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  -- the chain of subsheaves `F[k!]` of `F`
  have hN : Monotone fun k : ℕ ↦ kernelSubobject (k.factorial • 𝟙 F) := fun k k' hk ↦ by
    obtain ⟨r, hr⟩ := Nat.factorial_dvd_factorial hk
    have : k'.factorial • 𝟙 F = (k.factorial • 𝟙 F) ≫ (r • 𝟙 F) := by
      simp only [hr, Preadditive.comp_nsmul, Category.comp_id, mul_comm, mul_nsmul]
      exact smul_comm _ _ _
    change kernelSubobject _ ≤ kernelSubobject _
    rw [this]
    exact kernelSubobject_comp_le _ _
  let K : ℕ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hN.functor ⋙ Subobject.underlying
  let α : K ⟶ (Functor.const ℕ).obj F :=
    { app k := (kernelSubobject (k.factorial • 𝟙 F)).arrow
      naturality k k' f := by simp [K] }
  have : Mono α := NatTrans.mono_of_mono_app α
  let cK : Cocone K := { pt := F, ι := α }
  let t := colimit.desc K cK
  have ht : Mono t := colim.map_mono' α (colimit.isColimit K) (isColimitConstCocone ℕ F) t
    (fun k ↦ by simp [t, cK])
  -- `t` is an epimorphism, as can be checked on geometric stalks, which are torsion
  have : Epi t := by
    refine ⟨fun {G} g h hgh ↦ ?_⟩
    have hk (k : ℕ) : α.app k ≫ g = α.app k ≫ h := by
      simpa [t, cK] using colimit.ι K k ≫= hgh
    have : AB5OfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) := inferInstance
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    refine sheafHom_ext_of_sheafFiber_map_algClosurePoint fun p ↦ ?_
    have := (pointSmallEtale (T.algClosurePoint p)).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    ext x
    obtain ⟨m, hm, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
      (IsTorsionModuleSheaf.isTorsion_sheafFiber (F := F) _ _ x)
    have hS :=
      (ShortComplex.kernelSequence_exact (m.factorial • 𝟙 F)).map_of_mono_of_preservesKernel
        (pointSmallEtale (T.algClosurePoint p)).sheafFiber inferInstance inferInstance
    have hx' : (pointSmallEtale (T.algClosurePoint p)).sheafFiber.map (m.factorial • 𝟙 F) x =
        0 := by
      obtain ⟨r, hr⟩ := Nat.dvd_factorial hm le_rfl
      simp [hr, mul_nsmul, hx]
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS x hx'
    have e : kernel.ι (m.factorial • 𝟙 F) ≫ g = kernel.ι (m.factorial • 𝟙 F) ≫ h := by
      rw [← kernelSubobject_arrow', Category.assoc, Category.assoc]
      exact (kernelSubobjectIso _).inv ≫= hk m
    have := congr((pointSmallEtale (T.algClosurePoint p)).sheafFiber.map $e y)
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at this
    rw [← hy]
    exact this
  have : IsIso ((colimit.isColimit K).desc cK) := isIso_of_mono_of_epi t
  refine ⟨ℕ, inferInstance, inferInstance, K, cK, IsColimit.ofPointIso (colimit.isColimit K),
    rfl, fun k ↦ ⟨k.factorial, k.factorial_pos, ?_⟩⟩
  have := kernelSubobject_arrow_comp (k.factorial • 𝟙 F)
  rw [Preadditive.comp_nsmul, Category.comp_id] at this
  rw [← cancel_mono (α.app k), Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  exact this

section InvertibleOrder

open scoped Classical in
/-- The product of the positive integers `d ≤ k` which are invertible on `S`. It is invertible
on `S`, divisible by every positive integer `d ≤ k` invertible on `S`, and increasing in `k`
for divisibility. -/
private noncomputable def invertibleOrderProd (S : Scheme.{u}) (k : ℕ) : ℕ :=
  ∏ d ∈ (Finset.range (k + 1)).filter (fun d : ℕ ↦ 0 < d ∧ IsUnit ((d : ℕ) : Γ(S, ⊤))), d

private lemma invertibleOrderProd_pos (S : Scheme.{u}) (k : ℕ) : 0 < invertibleOrderProd S k := by
  classical
  exact Finset.prod_pos fun _ hd ↦ (Finset.mem_filter.1 hd).2.1

private lemma isUnit_invertibleOrderProd (S : Scheme.{u}) (k : ℕ) :
    IsUnit ((invertibleOrderProd S k : ℕ) : Γ(S, ⊤)) := by
  classical
  rw [invertibleOrderProd, Nat.cast_prod]
  exact Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one
    fun d hd ↦ (Finset.mem_filter.1 hd).2.2

private lemma invertibleOrderProd_dvd (S : Scheme.{u}) {k k' : ℕ} (hk : k ≤ k') :
    invertibleOrderProd S k ∣ invertibleOrderProd S k' := by
  classical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset_filter _
    (Finset.range_subset_range.2 (by omega)))

private lemma dvd_invertibleOrderProd (S : Scheme.{u}) {d k : ℕ} (hd : 0 < d) (hdk : d ≤ k)
    (hS : IsUnit ((d : ℕ) : Γ(S, ⊤))) : d ∣ invertibleOrderProd S k := by
  classical
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hd, hS⟩)

/-- A morphism `φ : G ⟶ F` from a sheaf killed by a positive integer `n` to a sheaf which is
torsion of orders invertible on `S` is killed by `invertibleOrderProd S n`: on a geometric
stalk, the additive order of an element of the image of `φ` divides `n` and an integer
invertible on `S`, so it is a positive integer `≤ n` invertible on `S`. -/
private lemma invertibleOrderProd_nsmul_eq_zero {Λ : Type (u + 1)} [CommRing Λ]
    (S : Scheme.{u}) {T : Scheme.{u}} {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    [IsTorsionSheafOfInvertibleOrder S F] (φ : G ⟶ F) {n : ℕ} (hn : 0 < n)
    (hG : n • 𝟙 G = 0) :
    invertibleOrderProd S n • φ = 0 := by
  have : AB5OfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) := inferInstance
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  refine sheafHom_ext_of_sheafFiber_map_algClosurePoint fun t ↦ ?_
  have := (pointSmallEtale (T.algClosurePoint t)).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  rw [Functor.map_nsmul, Functor.map_zero]
  ext x
  set y := (pointSmallEtale (T.algClosurePoint t)).sheafFiber.map φ x
  have hny : n • y = 0 := by
    have := congr_arg (fun f ↦ (pointSmallEtale (T.algClosurePoint t)).sheafFiber.map
      (f ≫ φ)) hG
    simp only [Preadditive.nsmul_comp, Category.id_comp, zero_comp, Functor.map_nsmul,
      Functor.map_zero] at this
    simpa [y] using congr_arg (fun f ↦ f.hom x) this
  obtain ⟨m, hm, hmS, hmy⟩ :=
    IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero (S := S) _ _ y
  have h₁ : addOrderOf y ∣ n := addOrderOf_dvd_of_nsmul_eq_zero hny
  obtain ⟨r, hr⟩ : addOrderOf y ∣ m := addOrderOf_dvd_of_nsmul_eq_zero hmy
  rw [hr, Nat.cast_mul] at hmS
  have ho : addOrderOf y ∣ invertibleOrderProd S n :=
    dvd_invertibleOrderProd S (Nat.pos_of_dvd_of_pos h₁ hn) (Nat.le_of_dvd hn h₁)
      (isUnit_of_mul_isUnit_left hmS)
  simpa using addOrderOf_dvd_iff_nsmul_eq_zero.1 ho

/-- A sheaf `F` of `Λ`-modules which is torsion of orders invertible on `S` is the point of a
colimit cocone over a filtered diagram of sheaves, each of which is killed by some positive
integer `n` invertible on `S`.

This is blueprint `definition-torsion-sheaves--3` for the integers invertible on `S`.
The diagram is the chain of the `N_k`-torsion subsheaves `F[N_k]`, `k ∈ ℕ`, where `N_k` is the
product of the positive integers `d ≤ k` invertible on `S`. Its colimit maps monomorphically
to `F`, filtered colimits of sheaves being exact. It maps epimorphically too: by
`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf.exists_isColimit`, `F` is a filtered colimit of
sheaves `D_j` killed by integers `n_j`, and on geometric stalks the image of `D_j` in `F` is
killed by `N_{n_j}`, so `D_j ⟶ F` factors through `F[N_{n_j}]`. -/
theorem Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit
    (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Cocone D)
      (_ : IsColimit c), c.pt = F ∧
        ∀ j, ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • 𝟙 (D.obj j) = 0 := by
  have := IsTorsionModuleSheaf.of_isTorsionSheafOfInvertibleOrder S F
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasColimitsOfShape ℕ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    inferInstance
  have : AB5OfSize.{0, 0} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  obtain ⟨J, _, _, D, c, hc, rfl, hD⟩ := IsTorsionModuleSheaf.exists_isColimit Λ F
  let N := invertibleOrderProd S
  -- the chain of subsheaves `F[N_k]` of `F`
  have hN : Monotone fun k ↦ kernelSubobject (N k • 𝟙 c.pt) := fun k k' hk ↦ by
    obtain ⟨r, hr⟩ := invertibleOrderProd_dvd S hk
    have : N k' • 𝟙 c.pt = (N k • 𝟙 c.pt) ≫ (r • 𝟙 c.pt) := by
      simp only [N, hr, Preadditive.comp_nsmul, Category.comp_id, mul_comm, mul_nsmul]
      exact smul_comm _ _ _
    change kernelSubobject _ ≤ kernelSubobject _
    rw [this]
    exact kernelSubobject_comp_le _ _
  let K : ℕ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hN.functor ⋙ Subobject.underlying
  let α : K ⟶ (Functor.const ℕ).obj c.pt :=
    { app k := (kernelSubobject (N k • 𝟙 c.pt)).arrow
      naturality k k' f := by simp [K] }
  have : Mono α := NatTrans.mono_of_mono_app α
  let cK : Cocone K := { pt := c.pt, ι := α }
  let t := colimit.desc K cK
  have ht : Mono t := colim.map_mono' α (colimit.isColimit K) (isColimitConstCocone ℕ c.pt) t
    (fun k ↦ by simp [t, cK])
  -- each `D_j ⟶ F` factors through some `F[N_k]`
  have hf (j : J) : ∃ (n : ℕ) (f : D.obj j ⟶ K.obj n), f ≫ α.app n = c.ι.app j := by
    obtain ⟨n, hn, hDn⟩ := hD j
    have hz : c.ι.app j ≫ (N n • 𝟙 c.pt) = 0 := by
      simpa using invertibleOrderProd_nsmul_eq_zero S (F := c.pt) (c.ι.app j) hn hDn
    exact ⟨n, (kernelSubobject (N n • 𝟙 c.pt)).factorThru _ (kernelSubobject_factors _ _ hz),
      Subobject.factorThru_arrow _ _ _⟩
  choose n f hf using hf
  let s : c.pt ⟶ colimit K := hc.desc
    { pt := colimit K
      ι :=
        { app j := f j ≫ colimit.ι K (n j)
          naturality j j' φ := by
            rw [← cancel_mono t]
            simp [t, cK, hf] } }
  have hst : s ≫ t = 𝟙 c.pt := hc.hom_ext fun j ↦ by simp [s, t, cK, hf]
  have : IsSplitEpi t := ⟨⟨s, hst⟩⟩
  have : IsIso ((colimit.isColimit K).desc cK) := isIso_of_mono_of_isSplitEpi t
  refine ⟨ℕ, inferInstance, inferInstance, K, cK, IsColimit.ofPointIso (colimit.isColimit K),
    rfl, fun k ↦ ⟨N k, invertibleOrderProd_pos S k, isUnit_invertibleOrderProd S k, ?_⟩⟩
  have := kernelSubobject_arrow_comp (N k • 𝟙 c.pt)
  rw [Preadditive.comp_nsmul, Category.comp_id] at this
  rw [← cancel_mono (α.app k), Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  exact this

end InvertibleOrder

end TorsionSheaf

section TorsionHomology

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `ℤ`-indexed colimits of `Λ`-modules are exact: `ℤ` is a filtered category, and
`ModuleCat.{u + 1} Λ` is Grothendieck abelian, hence satisfies `AB5` for shapes of size
`u + 1`; `AB5OfSize_of_univLE` brings that down to the shapes of size `0` in which `ℤ`
lives. It is not an instance in mathlib because in that generality instance search would
climb the universes. -/
instance : HasExactColimitsOfShape ℤ (ModuleCat.{u + 1} Λ) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  infer_instance

variable (X : Scheme.{u})
  [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- An object of the bounded below derived category of étale sheaves of `Λ`-modules has
*torsion cohomology* if all its cohomology sheaves are torsion
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`). This is the hypothesis on the coefficient
complex in the general proper base change theorem. -/
noncomputable def Etale.DerivedCategory.Plus.moduleTorsionHomology :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ n : ℤ, IsTorsionModuleSheaf
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj K)

/-- If the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ`
is finite — then every object of the bounded below derived category of étale sheaves of
`Λ`-modules has torsion cohomology. -/
lemma Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion (hΛ : IsAddTorsion Λ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X K :=
  fun _ ↦ .of_isTorsion hΛ _

/-- A torsion sheaf placed in degree `0` has torsion cohomology: its cohomology sheaf in
degree `0` is the sheaf itself, and all its other cohomology sheaves vanish. -/
lemma Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf I] :
    Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X
      ((DerivedCategory.Plus.singleFunctor _ 0).obj I) := by
  intro n
  by_cases hn : n = 0
  · subst hn
    exact IsTorsionModuleSheaf.of_epi (F := I)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app I)
  · have hZ : IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj I)) :=
      IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)
        ((DerivedCategory.homologyFunctorFactors _ n).app _)
    have := hZ.epi (0 : I ⟶ _)
    exact IsTorsionModuleSheaf.of_epi (0 : I ⟶ _)

/-- An object of the bounded below derived category of étale sheaves of `Λ`-modules has
*`P`-torsion cohomology*, for a set `P` of primes, if all its cohomology sheaves are `P`-torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheafOfPrimes`). -/
noncomputable def Etale.DerivedCategory.Plus.torsionHomologyOfPrimes (P : Set ℕ) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ n : ℤ, IsTorsionSheafOfPrimes P
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n).obj K)

/-- `P`-torsion cohomology is in particular torsion cohomology. -/
lemma Etale.DerivedCategory.Plus.torsionHomologyOfPrimes_le_moduleTorsionHomology (P : Set ℕ) :
    Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P ≤
      Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X :=
  fun _ hK n ↦ have := hK n; .of_isTorsionSheafOfPrimes P _

/-- Blueprint `definition-constructible-sheaves`: Ambient categories and small subcategories.

The ambient category `D⁺_P-tor(X, Λ)` of bounded below complexes of étale sheaves of
`Λ`-modules whose cohomology sheaves have `P`-torsion geometric stalks, for a set `P` of primes,
as a full subcategory of `D⁺(X_ét, Λ)` (blueprint
`theorem-smooth-base-change-classical-torsion-2`). -/
noncomputable def Etale.DerivedCategoryPlusTorsionOfPrimes (P : Set ℕ) : Type _ :=
  (Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P).FullSubcategory

noncomputable instance (P : Set ℕ) : Category (Etale.DerivedCategoryPlusTorsionOfPrimes Λ X P) :=
  inferInstanceAs <|
    Category (Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P).FullSubcategory

/-- The inclusion of `D⁺_P-tor(X, Λ)` into `D⁺(X_ét, Λ)`. -/
noncomputable def Etale.DerivedCategoryPlusTorsionOfPrimes.ι (P : Set ℕ) :
    Etale.DerivedCategoryPlusTorsionOfPrimes Λ X P ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Etale.DerivedCategory.Plus.torsionHomologyOfPrimes Λ X P).ι

end TorsionHomology


/-- This is for describing sheaves in smooth base change. -/
class Scheme.OrderInvertibleOnSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) : Prop where
  isUnit_addOrderOf_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ↥((pointSmallEtale s).sheafFiber.obj F)) :
    IsUnit ((addOrderOf x : ℕ) : Γ(Y, ⊤))


/-- An object of `D+` with cohomologies `OrderInvertibleOnSheaf`. -/
noncomputable def Etale.DerivedCategory.Plus.orderInvertibleOnHomology
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) :=
  fun K ↦ ∀ n : ℤ, OrderInvertibleOnSheaf f
    ((DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)


end AlgebraicGeometry
