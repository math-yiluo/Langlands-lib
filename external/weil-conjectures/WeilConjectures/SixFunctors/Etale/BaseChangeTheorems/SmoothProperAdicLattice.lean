/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperAdicTower
public import WeilConjectures.ConstructibleSheaf.AdicImageTower
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Higher direct images of `ℓ`-adic towers along smooth proper morphisms are lisse up to isogeny

Let `K` be a field, `Y` of finite type over `K`, `f : X ⟶ Y` smooth and proper, and `(Gₙ)` an
`ℓ`-adic tower of étale sheaves of `Λ`-modules on `X` as in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperAdicTower`, and
`Hₙ = Rʲf_* Gₙ`. Then:

- the tower `(Hₙ)` is uniformly Artin-Rees
  (`AlgebraicGeometry.Etale.isArtinReesTower_homology_rightDerivedLowerStar`): the constants of
  `Etale.exists_forall_sheafFiber_exists_eval_eq_homology_rightDerivedLowerStar`
  in degrees `j` and `j - 1`, the latter bounding the torsion of the limits of the stalks of
  `(Hₙ)` (`CategoryTheory.AdicTowerStructure.pow_smul_eq_zero_of_exists_eval_eq`);
- hence, when `Λ` is a discrete valuation ring and `Y` is connected, the `ℓ`-adic image tower
  `G'ₘ = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c})` is an exact `ℓ`-adic tower of finite locally constant
  sheaves, étale locally isomorphic to `(Λ / ℓᵐ)ʳ`, and the inclusion `G'ₘ ⟶ H_{m+c}` is a
  monomorphism with cokernel killed by `ℓ²ᶜ`
  (`AlgebraicGeometry.Etale.exists_adicTowerStructure_homology_rightDerivedLowerStar`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite DerivedCategory Abelian

open scoped CategoryTheory.Functor

namespace CategoryTheory.AdicTowerStructure

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
  {R : Type u} [CommRing R] (Φ : D ⥤ ModuleCat.{v} R) [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] {G : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

/-- **Artin-Rees in degree `q` bounds the torsion of the limit in degree `q + 1`.** If the
modules `Φ Hᵠ(RF Gₙ)` are finite and the tower `(Φ Hᵠ(RF Gₙ))ₙ` satisfies the Artin-Rees
condition with constant `c`, then `ℓᶜ` kills the `ℓ`-power torsion of `lim Φ Hᵠ⁺¹(RF Gₙ)`. -/
lemma pow_smul_eq_zero_of_exists_eval_eq (A : AdicTowerStructure G ℓ) {q j : ℤ} (hqj : q + 1 = j)
    [∀ n, Finite ((homologyRightDerived F Φ q).obj (G.obj n))] (c : ℕ)
    (hc : ∀ (m : ℕ) (z : (homologyRightDerived F Φ q).obj (G.obj (op (m + c)))),
      ∃ x : ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ q),
        x.1 (op m) = ModuleCat.towerMap (G ⋙ homologyRightDerived F Φ q) (Nat.le_add_right m c) z)
    (y : ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j)) (k : ℕ)
    (hk : ℓ ^ k • y = 0) : ℓ ^ c • y = 0 := by
  subst hqj
  have (n : ℕᵒᵖ) : Finite ((G ⋙ homologyRightDerived F Φ q).obj n) :=
    inferInstanceAs (Finite ((homologyRightDerived F Φ q).obj (G.obj n)))
  exact (A.adicTowerSequence F Φ q).pow_smul_eq_zero_of_exists_eval_eq c hc y k hk

end CategoryTheory.AdicTowerStructure

namespace AlgebraicGeometry

open Scheme

open scoped Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

section

variable {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K))
  [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f] (ℓ : ℕ)
  [IsNoetherianRing Λ] [IsPrecomplete (Ideal.span {(ℓ : Λ)}) Λ]
  (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (A : AdicTowerStructure G ℓ)
  (I : ℕ → Ideal Λ) [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
  (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
  [∀ n, IsFiniteLocallyConstantSheaf (F n)]
  (eG : ∀ n, G.obj (op n) ≅
    (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))

omit [IsNoetherianRing Λ] [IsPrecomplete (Ideal.span {(ℓ : Λ)}) Λ] in
include aY eG in
/-- The higher direct images `Rʲf_* Gₙ` along a smooth proper morphism are finite locally
constant. -/
lemma Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_obj (j : ℕ) (n : ℕ) :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((G ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
        DerivedCategory.homologyFunctor _ j).obj (op n)) :=
  have := Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
    (Λ ⧸ I n) aY f (F n) j
  IsFiniteLocallyConstantSheaf.of_iso (((DerivedCategory.homologyFunctor _ j).mapIso
    ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (eG n))) ≪≫
    (Etale.homologyRightDerivedLowerStarRestrictScalarsIso (Ideal.Quotient.mk (I n)) f
      (F n) j).symm).symm)

include aY A eG in
/-- **The torsion of the limits of the stalks of `Rʲf_* Gₙ` is uniformly bounded.** There is `c`
such that at every geometric point `s` of `Y`, `ℓᶜ` kills the `ℓ`-power torsion of the limit of
the tower of stalks `((Rʲf_* Gₙ)_s)ₙ`: for `j = 0` it is torsion free, and for `j ≥ 1` the
constant `c` of the uniform Artin-Rees property in degree `j - 1` works
(`CategoryTheory.AdicTowerStructure.pow_smul_eq_zero_of_exists_eval_eq`). -/
theorem Etale.exists_pow_smul_eq_zero_sectionsSubmodule_homology_rightDerivedLowerStar (j : ℕ) :
    ∃ c : ℕ, ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
      (y : ModuleCat.sectionsSubmodule (G ⋙ AdicTowerStructure.homologyRightDerived
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j)) (k : ℕ),
      ℓ ^ k • y = 0 → ℓ ^ c • y = 0 := by
  cases j with
  | zero =>
    refine ⟨0, fun {Ω} _ _ s y k hk ↦ ?_⟩
    let Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hzero (n : ℕᵒᵖ) : Subsingleton ((AdicTowerStructure.homologyRightDerived
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) Φ (-1)).obj (G.obj n)) := by
      have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (G.obj n)
      exact ModuleCat.isZero_iff_subsingleton.1
        (Φ.map_isZero (DerivedCategory.isZero_of_isGE _ 0 (-1) (by omega)))
    have (n : ℕᵒᵖ) : Finite ((AdicTowerStructure.homologyRightDerived
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) Φ (-1)).obj (G.obj n)) :=
      Finite.of_subsingleton
    exact A.pow_smul_eq_zero_of_exists_eval_eq _ Φ (q := -1) (by simp) 0
      (fun m z ↦ ⟨0, by
        rw [Subsingleton.elim z 0, map_zero]
        rfl⟩) y k hk
  | succ j =>
    obtain ⟨c, hc⟩ := Etale.exists_forall_sheafFiber_exists_eval_eq_homology_rightDerivedLowerStar
      aY f ℓ G A I F eG j
    refine ⟨c, fun {Ω} _ _ s y k hk ↦ ?_⟩
    have (n : ℕᵒᵖ) : Finite ((AdicTowerStructure.homologyRightDerived
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) (pointSmallEtale s).sheafFiber j).obj
          (G.obj n)) :=
      Etale.finite_sheafFiber_homology_rightDerivedLowerStar_of_smooth_of_isProper
        aY f (G.obj n) (I n.unop) (F n.unop) (eG n.unop) j s
    exact A.pow_smul_eq_zero_of_exists_eval_eq _ _ (q := (j : ℤ)) (Nat.cast_succ j).symm c
      (hc s) y k hk

include aY A eG in
/-- **Higher direct images of `ℓ`-adic towers along smooth proper morphisms are uniformly
Artin-Rees**: there is `c` such that `(Rʲf_* Gₙ)ₙ` is uniformly Artin-Rees with constant `c`
(`AlgebraicGeometry.Etale.IsArtinReesTower`). -/
theorem Etale.isArtinReesTower_homology_rightDerivedLowerStar (j : ℕ) :
    ∃ c : ℕ, Etale.IsArtinReesTower (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙ DerivedCategory.homologyFunctor _ j) ℓ c := by
  obtain ⟨c₁, hc₁⟩ :=
    Etale.exists_forall_sheafFiber_exists_eval_eq_homology_rightDerivedLowerStar aY f ℓ G A I F eG j
  obtain ⟨c₂, hc₂⟩ :=
    Etale.exists_pow_smul_eq_zero_sectionsSubmodule_homology_rightDerivedLowerStar aY f ℓ G A I F
      eG j
  refine ⟨c₁ + c₂, ⟨fun s m z ↦ ?_, fun s m x ↦ ?_, fun s y k hk ↦ ?_⟩⟩
  · obtain ⟨x, hx⟩ := hc₁ s m (ModuleCat.towerMap _ (by omega : m + c₁ ≤ m + (c₁ + c₂)) z)
    exact ⟨x, hx.trans (ModuleCat.towerMap_towerMap _ _ _ z)⟩
  · exact ((Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar aY f ℓ G A I F eG j
      s).2.choose_spec m).1 x
  · rw [pow_add, mul_smul, hc₂ s y k hk, smul_zero]

include aY A eG in
/-- **Higher direct images of `ℓ`-adic towers along smooth proper morphisms are lisse up to
bounded isogeny.** Let `Λ` be a discrete valuation ring in which `ℓ` is a nonzero nonunit
(e.g. `ULift ℤ_[ℓ]`), and `Y` connected. Then there are `c`, `r`, an exact `ℓ`-adic tower `G'`
of finite locally constant sheaves on `Y` (an `ℓ`-adic tower structure whose transition maps
`G'ₖ ⟶ G'ₙ` are cokernels of `ℓⁿ`), with all stalks of `G'ₘ` isomorphic to `(Λ / ℓᵐ)ʳ` and
`G'ₘ` étale locally isomorphic to the constant sheaf `(Λ / ℓᵐ)ʳ`, and a morphism of towers
`G' ⟶ (Rʲf_* G_{m+c})ₘ` which is a monomorphism with cokernels killed by `ℓ²ᶜ`. Namely,
`G'ₘ = ℓᶜ · im(Rʲf_* G_{m+2c} ⟶ Rʲf_* G_{m+c})` (`CategoryTheory.Functor.adicImageTower`). -/
theorem Etale.exists_adicTowerStructure_homology_rightDerivedLowerStar [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [ConnectedSpace Y] (hℓ : (ℓ : Λ) ≠ 0) (hℓ' : ¬IsUnit (ℓ : Λ))
    (j : ℕ) :
    ∃ (c r : ℕ) (G' : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (_ : AdicTowerStructure G' ℓ)
      (φ : G' ⟶ (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
          DerivedCategory.homologyFunctor _ j).towerShift c),
      (∀ m : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (G'.obj (op m))) ∧
      (∀ {n k : ℕ} (h : n ≤ k), ∃ w : (ℓ ^ n • 𝟙 (G'.obj (op k))) ≫ G'.map (homOfLE h).op = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ _ w))) ∧
      (∀ m : ℕ, Mono (φ.app (op m))) ∧
      (∀ m : ℕ, ℓ ^ (c + c) • cokernel.π (φ.app (op m)) = 0) ∧
      (∀ (m : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj (G'.obj (op m))
          ≃ₗ[Λ] (Fin r → Λ ⧸ Ideal.span {(ℓ : Λ) ^ m}))) ∧
      ∀ m : ℕ, ∃ 𝒰 : Cover.{u} etalePrecoverage Y, ∀ i : 𝒰.I₀,
        Nonempty (((𝒰.f i)^*[ModuleCat.{u + 1} Λ]).obj (G'.obj (op m)) ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Fin r → Λ ⧸ Ideal.span {(ℓ : Λ) ^ m}))) := by
  obtain ⟨c, hc⟩ := Etale.isArtinReesTower_homology_rightDerivedLowerStar aY f ℓ G A I F eG j
  have (n : ℕ) := Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_obj aY f G I F
    eG j n
  have hzero := Functor.pow_smul_id_eq_zero_of_adicTowerStructure ℓ A
    (DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
      DerivedCategory.homologyFunctor _ j)
  obtain ⟨r, hr⟩ := hc.exists_forall_linearEquiv_sheafFiber hℓ hℓ' fun y ↦
    (Etale.exists_artinRees_sheafFiber_homology_rightDerivedLowerStar aY f ℓ G A I F eG j
      (Y.algClosurePoint y)).1
  refine ⟨c, r, _, hc.adicTowerStructure hzero, Functor.adicImageTowerHom _ ℓ c,
    fun m ↦ inferInstance, fun h ↦ ⟨_, ⟨hc.isColimitCokernelCofork hzero h⟩⟩, fun m ↦ ?_,
    fun m ↦ ?_, hr, fun m ↦ ?_⟩
  · rw [Functor.adicImageTowerHom_app]
    infer_instance
  · exact Functor.pow_smul_cokernel_π_adicImageTowerι_eq_zero_of_adicTowerStructure ℓ c A _ m
  · exact exists_cover_nonempty_iso_constantSheaf _ _ fun y ↦
      ⟨(hr m (Y.algClosurePoint y)).some.toModuleIso⟩

end

end AlgebraicGeometry
