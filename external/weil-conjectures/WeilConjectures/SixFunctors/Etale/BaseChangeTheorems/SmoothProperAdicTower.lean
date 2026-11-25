/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdicTowerSequence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarMittagLeffler
public import WeilConjectures.ConstructibleSheaf.UniformMittagLeffler

/-!
# Higher direct images of `ℓ`-adic towers along smooth proper morphisms are `ℓ`-adic

Let `K` be a field, `Y` of finite type over `K`, `f : X ⟶ Y` smooth and proper, and `(Gₙ)` an
`ℓ`-adic tower (`CategoryTheory.AdicTowerStructure`) of étale sheaves of `Λ`-modules on `X`, each
`Gₙ` being the restriction of scalars of a finite locally constant sheaf of `Λ ⧸ Iₙ`-modules with
`Λ ⧸ Iₙ` finite and killed by an integer invertible in `K` (e.g. `Λ = ℤ_ℓ`, `Iₙ = (ℓⁿ)`,
`ℓ ≠ char K`). Assume `Λ` noetherian and `ℓ`-adically precomplete. Then at every geometric point
`s` of `Y`, the tower of stalks `((Rʲf_* Gₙ)_s)ₙ` is Artin-Rees `ℓ`-adic: its limit `L` is a
finitely generated `Λ`-module, and there is `c` such that `L / ℓᵐ ⟶ (Rʲf_* Gₘ)_s` is injective
and `(Rʲf_* Gₘ₊꜀)_s ⟶ (Rʲf_* Gₘ)_s` factors through it
(`AlgebraicGeometry.Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar`).

The stalks are finite by the smooth proper base change theorem
(`Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`) and
the coefficient change `AlgebraicGeometry.Etale.homologyRightDerivedLowerStarRestrictScalarsIso`;
the long exact sequences of `Rf_*` applied to `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` give the data of
`CategoryTheory.AdicTowerStructure.exists_artinRees`.

The constant `c` can be chosen independently of `s`
(`AlgebraicGeometry.Etale.exists_forall_sheafFiber_exists_eval_eq_homology_rightDerivedLowerStar`):
at the sheaf level, the tower `(Rʲf_* Gₘ)ₘ` is uniformly Mittag-Leffler, the image of
`Rʲf_* Gₘ₊꜀ ⟶ Rʲf_* Gₘ` being contained in that of `Rʲf_* G_k ⟶ Rʲf_* Gₘ` for all `k ≥ m + c`
(`Etale.exists_imageSubobject_le_homology_rightDerivedLowerStar_of_smooth_of_isProper`),
as the stalkwise constants at finitely many points suffice.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Finiteness of the stalks of higher direct images of smooth proper morphisms**: in the
situation of
`AlgebraicGeometry.ProEtale.mittagLeffler_homology_rightDerivedLowerStar_of_smooth_of_isProper`,
the stalks of `Rᵠf_* Gₙ` at geometric points of `Y` are finite. -/
lemma Etale.finite_sheafFiber_homology_rightDerivedLowerStar_of_smooth_of_isProper
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (J : Ideal Λ) [Finite (Λ ⧸ J)]
    [HasInvertibleExponent (Λ ⧸ J) (Spec (.of K))]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J))) [IsFiniteLocallyConstantSheaf F]
    (eG : G ≅ (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj F) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Finite ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((DerivedCategory.homologyFunctor _ q).obj (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)))) := by
  let e := (DerivedCategory.homologyFunctor _ q).mapIso
      ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso eG)) ≪≫
      (Etale.homologyRightDerivedLowerStarRestrictScalarsIso (Ideal.Quotient.mk J) f F q).symm
  have := Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
    (Λ ⧸ J) aY f F q
  have := finite_sheafFiber_restrictScalars_of_isFiniteSheaf J
    ((DerivedCategory.homologyFunctor _ q).obj
      (R(Etale.lowerStar (ModuleCat.{u + 1} (Λ ⧸ J)) f).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) s
  exact Finite.of_equiv _
    ((pointSmallEtale s).sheafFiber.mapIso e).toLinearEquiv.toEquiv.symm

/-- **Higher direct images of `ℓ`-adic towers along smooth proper morphisms are Artin-Rees
`ℓ`-adic, stalkwise.** Let `K` be a field, `Y` of finite type over `K`, `f : X ⟶ Y` smooth and
proper, `Λ` noetherian and `ℓ`-adically precomplete, and `(Gₙ)` an `ℓ`-adic tower of étale
sheaves of `Λ`-modules on `X` such that each `Gₙ` is the restriction of scalars of a finite
locally constant sheaf of `Λ ⧸ Iₙ`-modules, `Λ ⧸ Iₙ` finite and killed by an integer invertible
in `K`. Let `s` be a geometric point of `Y` and `j : ℕ`. Then the limit `L` of the tower of stalks
`((Rʲf_* Gₙ)_s)ₙ` is a finitely generated `Λ`-module, and there is `c` such that for every `m`
the kernel of `L ⟶ (Rʲf_* Gₘ)_s` is `ℓᵐ L` and the image of `(Rʲf_* Gₘ₊꜀)_s ⟶ (Rʲf_* Gₘ)_s` is
contained in the image of `L`: the tower `((Rʲf_* Gₘ)_s)ₘ` is Artin-Rees isomorphic to
`(L / ℓᵐ)ₘ`. -/
theorem Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f] (ℓ : ℕ) [IsNoetherianRing Λ]
    [IsPrecomplete (Ideal.span {(ℓ : Λ)}) Λ]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (A : AdicTowerStructure G ℓ)
    (I : ℕ → Ideal Λ) [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Module.Finite Λ (ModuleCat.sectionsSubmodule (G ⋙ AdicTowerStructure.homologyRightDerived
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j)) ∧
      ∃ c : ℕ, ∀ m : ℕ,
        (∀ x : ModuleCat.sectionsSubmodule (G ⋙ AdicTowerStructure.homologyRightDerived
            (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j),
          x.1 (op m) = 0 ↔ ∃ y, ℓ ^ m • y = x) ∧
        ∀ z : (AdicTowerStructure.homologyRightDerived (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
            (pointSmallEtale s).sheafFiber j).obj (G.obj (op (m + c))),
          ∃ x : ModuleCat.sectionsSubmodule (G ⋙ AdicTowerStructure.homologyRightDerived
              (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j),
            x.1 (op m) = ((AdicTowerStructure.homologyRightDerived
              (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j).map
                (G.map (homOfLE (Nat.le_add_right m c)).op)).hom z := by
  have : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have (n : ℕᵒᵖ) : Finite ((AdicTowerStructure.homologyRightDerived
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j).obj
        (G.obj n)) :=
    Etale.finite_sheafFiber_homology_rightDerivedLowerStar_of_smooth_of_isProper
      aY f (G.obj n) (I n.unop) (F n.unop) (eG n.unop) j s
  have (n : ℕᵒᵖ) : Finite ((AdicTowerStructure.homologyRightDerived
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber (j + 1)).obj
        (G.obj n)) :=
    Etale.finite_sheafFiber_homology_rightDerivedLowerStar_of_smooth_of_isProper
      aY f (G.obj n) (I n.unop) (F n.unop) (eG n.unop) (j + 1) s
  exact A.exists_artinRees (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (pointSmallEtale s).sheafFiber j

/-- **Higher direct images of `ℓ`-adic towers along smooth proper morphisms are uniformly
Mittag-Leffler.** In the situation of
`AlgebraicGeometry.Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar`, there is `c`
such that for every `m` and `k ≥ m + c`, the image of `Rʲf_* G_{m+c} ⟶ Rʲf_* Gₘ` is contained in
the image of `Rʲf_* G_k ⟶ Rʲf_* Gₘ`: the tower `(Rʲf_* Gₘ)ₘ` is Artin-Rees isomorphic to the tower
of its stable images `Eₘ = im(Rʲf_* G_{m+c} ⟶ Rʲf_* Gₘ)`, whose stalk at a geometric point `s`
is `L_s / ℓᵐ` for the finitely generated limit `L_s` of the stalks
(`AlgebraicGeometry.Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar`).

The constant `c` is obtained from the stalkwise constants at finitely many points
(`AlgebraicGeometry.Etale.exists_imageSubobject_le_of_forall_range_sheafFiber_eq`). -/
theorem Etale.exists_imageSubobject_le_homology_rightDerivedLowerStar_of_smooth_of_isProper
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f] (ℓ : ℕ) [IsNoetherianRing Λ]
    [IsPrecomplete (Ideal.span {(ℓ : Λ)}) Λ]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (A : AdicTowerStructure G ℓ)
    (I : ℕ → Ideal Λ) [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    ∃ c : ℕ, ∀ (m k : ℕ) (hk : m + c ≤ k),
      imageSubobject ((G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ DerivedCategory.homologyFunctor _ j).map
            (homOfLE (Nat.le_add_right m c)).op) ≤
        imageSubobject ((G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ DerivedCategory.homologyFunctor _ j).map
            (homOfLE (le_trans (Nat.le_add_right m c) hk)).op) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let H := G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ DerivedCategory.homologyFunctor _ j
  -- `Rʲf_* Gₙ ≅ res Rʲf_* Fₙ` is finite locally constant
  have (n : ℕ) : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (H.obj (op n)) :=
    have := Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
      (Λ ⧸ I n) aY f (F n) j
    IsFiniteLocallyConstantSheaf.of_iso (((DerivedCategory.homologyFunctor _ j).mapIso
      ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (eG n))) ≪≫
      (Etale.homologyRightDerivedLowerStarRestrictScalarsIso (Ideal.Quotient.mk (I n)) f
        (F n) j).symm).symm)
  let T (y : Y) := AdicTowerStructure.homologyRightDerived (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (pointSmallEtale (Y.algClosurePoint y)).sheafFiber j
  choose c₀ hc₀ using fun y : Y ↦ (Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar
    aY f ℓ G A I F eG j (Y.algClosurePoint y)).2
  have key (y : Y) (m j' : ℕ) (hj' : c₀ y ≤ j') :
      Set.range (ModuleCat.towerMap (G ⋙ T y) (Nat.le_add_right m j')) =
        Set.range (ModuleCat.towerMap (G ⋙ T y) (Nat.le_add_right m (c₀ y))) := by
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      refine ⟨ModuleCat.towerMap (G ⋙ T y) (Nat.add_le_add_left hj' m) z, ?_⟩
      rw [ModuleCat.towerMap_towerMap]
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := ((hc₀ y) m).2 z
      refine ⟨x.1 (op (m + j')), ?_⟩
      rw [(ModuleCat.mem_sectionsSubmodule_iff _ _).1 x.2]
      exact hx
  exact exists_imageSubobject_le_of_forall_range_sheafFiber_eq H
    (fun n y ↦ Etale.finite_sheafFiber_homology_rightDerivedLowerStar_of_smooth_of_isProper
      aY f (G.obj (op n)) (I n) (F n) (eG n) j (Y.algClosurePoint y)) c₀ key

/-- **Higher direct images of `ℓ`-adic towers along smooth proper morphisms are Artin-Rees
`ℓ`-adic, uniformly in the geometric point.** In the situation of
`AlgebraicGeometry.Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar`, there is a
single `c` such that at every geometric point `s` of `Y` and for every `m`, the image of
`(Rʲf_* Gₘ₊꜀)_s ⟶ (Rʲf_* Gₘ)_s` is contained in the image of the limit `L_s` of the stalks. As
the kernel of `L_s ⟶ (Rʲf_* Gₘ)_s` is `ℓᵐ L_s`, the towers of stalks `((Rʲf_* Gₘ)_s)ₘ` are
Artin-Rees isomorphic to `(L_s / ℓᵐ)ₘ` with a constant independent of `s`. -/
theorem Etale.exists_forall_sheafFiber_exists_eval_eq_homology_rightDerivedLowerStar
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f] (ℓ : ℕ) [IsNoetherianRing Λ]
    [IsPrecomplete (Ideal.span {(ℓ : Λ)}) Λ]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (A : AdicTowerStructure G ℓ)
    (I : ℕ → Ideal Λ) [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    ∃ c : ℕ, ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) (m : ℕ)
      (z : (AdicTowerStructure.homologyRightDerived (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
        (pointSmallEtale s).sheafFiber j).obj (G.obj (op (m + c)))),
      ∃ x : ModuleCat.sectionsSubmodule (G ⋙ AdicTowerStructure.homologyRightDerived
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j),
        x.1 (op m) = ((AdicTowerStructure.homologyRightDerived
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j).map
            (G.map (homOfLE (Nat.le_add_right m c)).op)).hom z := by
  obtain ⟨c, hc⟩ :=
    Etale.exists_imageSubobject_le_homology_rightDerivedLowerStar_of_smooth_of_isProper
      aY f ℓ G A I F eG j
  refine ⟨c, fun {Ω} _ _ s m z ↦ ?_⟩
  let T := AdicTowerStructure.homologyRightDerived (Etale.lowerStar (ModuleCat.{u + 1} Λ) f)
    (pointSmallEtale s).sheafFiber j
  obtain ⟨c', hc'⟩ := (Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar
    aY f ℓ G A I F eG j s).2
  have hk : m + c ≤ m + (c + c') := by omega
  obtain ⟨w, hw⟩ := range_sheafFiber_map_subset_of_imageSubobject_le s (hc m _ hk)
    (Set.mem_range_self z)
  obtain ⟨x, hx⟩ := (hc' m).2 (ModuleCat.towerMap (G ⋙ T) (by omega : m + c' ≤ m + (c + c')) w)
  exact ⟨x, hx.trans ((ModuleCat.towerMap_towerMap (G ⋙ T) _ _ w).trans hw)⟩

end AlgebraicGeometry
