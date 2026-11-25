/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SmoothProperSpecialization

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianSections
public import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper

/-!
# Higher direct images of smooth proper morphisms are locally constant

Let `k` be a field, `Λ` a finite ring killed by an integer invertible in `k`, `Y` a scheme of
finite type over `k`, `f : X ⟶ Y` smooth and proper and `F` a finite locally constant sheaf of
`Λ`-modules on `X_ét`. Then every higher direct image `Rᵠf_* F` is finite locally constant
(`Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`,
[SGA 4, Exp. XVI, Cor. 2.2]).

The proof follows SGA 4. The sheaf `G = Rᵠf_* F` is constructible, so by the specialization
criterion it suffices that for every geometric point `s` of `Y`, with strict localization
`g : Y_(s) ⟶ Y`, and every geometric point `t` of `Y_(s)`, the cospecialization map
`G_s ⟶ G_{t ≫ g}` is bijective. It is the restriction map
`Γ(Y_(s), g^* G) ⟶ Γ(Spec Ω', t^* g^* G)`. By proper base change, `g^* G` is the higher direct
image `Rᵠπ_* F'` along the base change `π : X ×_Y Y_(s) ⟶ Y_(s)`. Over the strictly local base
the specialization isomorphism says that the restriction to the closed point of
`Rπ_* F' ⟶ Rπ_* Rh_* h^* F'` is an isomorphism, where `h` is the base change of `t`; by proper
base change along `t` this is the restriction to the closed point of the unit
`Rπ_* F' ⟶ Rt_* t^* Rπ_* F'`, which then induces bijections on the global sections of the
homology sheaves.

## Main results

- `CategoryTheory.Adjunction.unit_app_comp_map_mate_app`: units, mates and conjugates of a
  square of adjunctions.
- `AlgebraicGeometry.Etale.isIso_map_unit_app_lowerStar_of_isIso_map_lowerStar_map_unit`: the
  unit along the base from the unit along the source, under base change.
- `Etale.isIso_globalSectionsUpperStarMap_homology_lowerStar_of_smooth_of_isProper`:
  over a strictly henselian local ring, restriction of the sections of `Rᵠπ_* F` to a geometric
  point is bijective.
- `Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`:
  the theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Units, conjugates and mates.** Let `Lt ⊣ Rt`, `Lπ ⊣ Rπ`, `Lh ⊣ Rh`, `Lπ' ⊣ Rπ'` be
adjunctions and `θ : Lt ⋙ Lπ' ⟶ Lπ ⋙ Lh`. The unit of `Lt ⊣ Rt` at `Rπ M` followed by `Rt` of
the mate `Lt Rπ M ⟶ Rπ' Lh M` of `θ` is `Rπ` of the unit of `Lh ⊣ Rh` at `M` followed by the
conjugate `Rπ Rh ⟶ Rt Rπ'` of `θ`. -/
lemma _root_.CategoryTheory.Adjunction.unit_app_comp_map_mate_app {A B A' B' : Type*} [Category* A]
    [Category* B] [Category* A'] [Category* B'] {Lt : B ⥤ B'} {Rt : B' ⥤ B} {Lπ : B ⥤ A}
    {Rπ : A ⥤ B} {Lh : A ⥤ A'} {Rh : A' ⥤ A} {Lπ' : B' ⥤ A'} {Rπ' : A' ⥤ B'}
    (adjt : Lt ⊣ Rt) (adjπ : Lπ ⊣ Rπ) (adjh : Lh ⊣ Rh) (adjπ' : Lπ' ⊣ Rπ')
    (θ : Lt ⋙ Lπ' ⟶ Lπ ⋙ Lh) (M : A) :
    adjt.unit.app (Rπ.obj M) ≫ Rt.map (adjπ'.unit.app (Lt.obj (Rπ.obj M)) ≫
        Rπ'.map (θ.app (Rπ.obj M)) ≫ Rπ'.map (Lh.map (adjπ.counit.app M))) =
      Rπ.map (adjh.unit.app M) ≫
        (conjugateEquiv (adjπ.comp adjh) (adjt.comp adjπ') θ).app (Lh.obj M) := by
  have hB : Lπ'.map (adjπ'.unit.app (Lt.obj (Rπ.obj M)) ≫ Rπ'.map (θ.app (Rπ.obj M)) ≫
      Rπ'.map (Lh.map (adjπ.counit.app M))) ≫ adjπ'.counit.app (Lh.obj M) =
      θ.app (Rπ.obj M) ≫ Lh.map (adjπ.counit.app M) := by
    simp
  apply ((adjt.comp adjπ').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  conv_rhs => erw [Functor.map_comp, Category.assoc, conjugateEquiv_counit,
    Adjunction.comp_counit_app, reassoc_of% (θ.naturality (Rπ.map (adjh.unit.app M))),
    Functor.comp_map, ← Functor.map_comp_assoc, Adjunction.counit_naturality, Functor.map_comp,
    Category.assoc, Adjunction.left_triangle_components, Category.comp_id]
  have hA : Lt.map (adjt.unit.app (Rπ.obj M) ≫ Rt.map (adjπ'.unit.app (Lt.obj (Rπ.obj M)) ≫
      Rπ'.map (θ.app (Rπ.obj M)) ≫ Rπ'.map (Lh.map (adjπ.counit.app M)))) ≫
      adjt.counit.app _ = adjπ'.unit.app (Lt.obj (Rπ.obj M)) ≫
      Rπ'.map (θ.app (Rπ.obj M)) ≫ Rπ'.map (Lh.map (adjπ.counit.app M)) := by
    simp
  erw [Adjunction.comp_counit_app, Functor.comp_map, ← Functor.map_comp_assoc, hA, hB]

/-- **The unit along the base and the base-change morphism.** For a commutative square
`h ≫ π = π' ≫ t` of schemes and `M ∈ D⁺(X_ét)`, the unit `Rπ_* M ⟶ Rt_* t^* Rπ_* M` followed by
`Rt_*` of the base-change morphism `t^* Rπ_* M ⟶ Rπ'_* h^* M` is `Rπ_*` of the unit
`M ⟶ Rh_* h^* M` followed by the conjugate isomorphism `Rπ_* Rh_* ≅ Rt_* Rπ'_*` of the pullback
comparison `π'^* t^* ≅ h^* π^*`. -/
lemma Etale.unit_app_comp_lowerStar_map_baseChange_app {X X' T T' : Scheme.{u}} {h : X' ⟶ X}
    {π' : X' ⟶ T'} {π : X ⟶ T} {t : T' ⟶ T} (sq : CommSq h π' π t)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.derivedUpperStarLowerStarAdjunctionPlus _ t).unit.app
        (R+((π)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      R+((t)_*[ModuleCat.{u + 1} Λ]).map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app M) =
    R+((π)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ h).unit.app M) ≫
      (conjugateEquiv ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ π).comp
          (Etale.derivedUpperStarLowerStarAdjunctionPlus _ h))
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ t).comp
          (Etale.derivedUpperStarLowerStarAdjunctionPlus _ π'))
        (Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom).app
          (D+((h)^*[ModuleCat.{u + 1} Λ]).obj M) := by
  rw [Etale.baseChange_app, Etale.baseChangeUnitStep_app, Etale.baseChangeSquareStep_hom_app,
    Etale.baseChangeCounitStep_app]
  exact Adjunction.unit_app_comp_map_mate_app _ _ _ _ _ M


/-- **Units along the base from units along the source.** For a commutative square
`h ≫ π = π' ≫ t` of schemes whose base-change morphism is an isomorphism at `M`, a functor `Φ`
out of `D⁺(T_ét)` sends the unit `Rπ_* M ⟶ Rt_* t^* Rπ_* M` to an isomorphism as soon as it
sends `Rπ_*` of the unit `M ⟶ Rh_* h^* M` to an isomorphism. -/
lemma Etale.isIso_map_unit_app_lowerStar_of_isIso_map_lowerStar_map_unit
    {X X' T T' : Scheme.{u}} {h : X' ⟶ X} {π' : X' ⟶ T'} {π : X ⟶ T} {t : T' ⟶ T}
    (sq : CommSq h π' π t) {C : Type*} [Category* C]
    (Φ : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ C)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app M)]
    [IsIso (Φ.map (R+((π)_*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ h).unit.app M)))] :
    IsIso (Φ.map ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ t).unit.app
      (R+((π)_*[ModuleCat.{u + 1} Λ]).obj M))) := by
  have h := congrArg Φ.map (Etale.unit_app_comp_lowerStar_map_baseChange_app Λ sq M)
  rw [Φ.map_comp, Φ.map_comp] at h
  have : IsIso (Φ.map ((Etale.derivedUpperStarLowerStarAdjunctionPlus _ t).unit.app
      (R+((π)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫ Φ.map (R+((t)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app M))) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Φ.map (R+((t)_*[ModuleCat.{u + 1} Λ]).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq).app M)))

/-- **Higher direct images of a smooth proper morphism over a strictly local base.** Let
`π : X ⟶ Spec R` be smooth and proper over a strictly henselian local ring, `t : Spec Ω ⟶ Spec R`
a geometric point, and `F` a locally constant sheaf of modules over a coefficient ring killed by
an integer `N ≠ 0` invertible in `R`. Then for every `q` the restriction of global sections
`Γ(Spec R, Rᵠπ_* F) ⟶ Γ(Spec Ω, t^* Rᵠπ_* F)` is an isomorphism.

The restriction to the closed point of `Rπ_* F ⟶ Rπ_* Rh_* h^* F` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_upperStar_map_lowerStar_map_unit_of_smooth_of_isProper`); by
proper base change along `t` so is the restriction to the closed point of the unit
`Rπ_* F ⟶ Rt_* t^* Rπ_* F`
(`AlgebraicGeometry.Etale.isIso_map_unit_app_lowerStar_of_isIso_map_lowerStar_map_unit`), and
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit` applies. -/
theorem Etale.isIso_globalSectionsUpperStarMap_homology_lowerStar_of_smooth_of_isProper
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)) {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [Smooth π] [IsProper π] (N : ℕ) (hN₀ : N ≠ 0) (hN : (N : Λ) = 0)
    (hNR : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F] (q : ℤ) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        (R+((π)_*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  have := Etale.isIso_upperStar_map_lowerStar_map_unit_of_smooth_of_isProper Λ π
    (IsPullback.of_hasPullback t π) N hN₀ hN hNR (IsPullback.of_hasPullback π _) F
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ
    (isAddTorsion_of_natCast_eq_zero N hN₀ hN) (IsPullback.of_hasPullback t π).flip
  exact Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit R t _
    (Etale.isIso_map_unit_app_lowerStar_of_isIso_map_lowerStar_map_unit Λ
      (IsPullback.of_hasPullback t π).flip.toCommSq _ _) q

/-- **Higher direct images of a smooth proper morphism, restricted to a strict localization.**
Let `f : X ⟶ Y` be smooth and proper, `F` a locally constant sheaf of modules over a coefficient
ring killed by an integer `N ≠ 0` invertible on `Y`, `s` a geometric point of `Y` with strict
localization `g : Y_(s) ⟶ Y` and `t` a geometric point of `Y_(s)`. Then for every `q` the
restriction of global sections `Γ(Y_(s), g^* Rᵠf_* F) ⟶ Γ(Spec Ω', t^* g^* Rᵠf_* F)` is an
isomorphism: by proper base change `g^* Rᵠf_* F` is the higher direct image along the base
change of `f` to the strictly local scheme `Y_(s)`, where
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_homology_lowerStar_of_smooth_of_isProper`
applies. -/
theorem Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f] (N : ℕ) (hN₀ : N ≠ 0)
    (hN : (N : Λ) = 0) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s) (q : ℤ) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((strictLocalizationToBase s)^*[ModuleCat.{u + 1} Λ].obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((f)_*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) := by
  let g := strictLocalizationToBase s
  let sq := IsPullback.of_hasPullback f g
  have : Smooth (pullback.snd f g) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsProper (pullback.snd f g) := MorphismProperty.pullback_snd _ _ inferInstance
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ
    (isAddTorsion_of_natCast_eq_zero N hN₀ hN) sq
  have := IsLocallyConstantSheaf.upperStar (pullback.fst f g) F
  have := Etale.isIso_globalSectionsUpperStarMap_homology_lowerStar_of_smooth_of_isProper Λ
    (strictHenselization s) t (pullback.snd f g) N hN₀ hN (by simpa using hNY.map g.appTop.hom)
    ((pullback.fst f g)^*[ModuleCat.{u + 1} Λ].obj F) q
  exact @Etale.isIso_globalSectionsUpperStarMap_of_iso _ _ _ _ t _ _ (Iso.symm
    (((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso q).app
        (R+((f)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (asIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
          R+((pullback.snd f g)_*[ModuleCat.{u + 1} Λ]).mapIso
            ((((pullback.fst f g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
              0).app F)))) this

/-- **Higher direct images of a smooth proper morphism are finite locally constant**
([SGA 4, Exp. XVI, Cor. 2.2], [SGA 4½, Arcata, V, Thm. 3.1]). Let `k` be a field, `Λ` a finite
ring killed by an integer invertible in `k`, `Y` of finite type over `k`, `f : X ⟶ Y` smooth and
proper and `F` a finite locally constant sheaf of `Λ`-modules on `X_ét`. Then every higher direct
image `Rᵠf_* F` is finite locally constant.

The sheaf `Rᵠf_* F` is constructible
(`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_isProper`),
so by the specialization criterion
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap`) it
suffices that its cospecialization maps are bijective. These are the restriction maps of
sections from a strict localization to its geometric points
(`AlgebraicGeometry.Scheme.bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap`),
which are bijective by proper base change and the specialization isomorphism
(`Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper`).
-/
theorem Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [Smooth f] [IsProper f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] (q : ℤ) :
    IsFiniteLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain ⟨N, hN₀, hN, hNk⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Spec (.of k))
  have hNY : IsUnit (N : Γ(Y, ⊤)) := by simpa using hNk.map aY.appTop.hom
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have hF : IsConstructibleSheaf F :=
    ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩
  have := Etale.hasConstructibleDirectImages_of_isProper (Λ := Λ) aY f F hF q
  refine isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap _ fun s _ _ _ t ↦
    bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap s t _ ?_
  have := Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper Λ f N
    hN₀.ne' hN hNY F s t q
  exact @Etale.isIso_globalSectionsUpperStarMap_of_iso _ _ _ _ t _ _ (Iso.symm
    ((strictLocalizationToBase s)^*[ModuleCat.{u + 1} Λ].mapIso
      (Etale.homologyRightDerivedLowerStarSingleIsoPlus f F q))) this

end AlgebraicGeometry
