/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-!
# Constant coefficients under a finite modification

Let `f : X ⟶ S` be proper, and let `ν : Y ⟶ X` be finite, surjective, and an isomorphism over
the complement `U` of a closed subscheme `i : Z ⟶ X` on which `f` is finite. For a finite
`Λ`-module `M`, the higher direct images of the constant sheaf `M` along `f` and along `ν ≫ f`
are compared (`proposition-proper-direct-image-finite-coefficients`): the cokernel of the unit
`M_X ⟶ ν_* ν^* M_X` is supported on `Z`, whose direct images along `f` are concentrated in
degree `0`.

The constant sheaf on `Y` is written `ν^* M_X`; it is identified with `M_Y` by
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Unit

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- On stalks, the unit `G ⟶ t_* t^* G` followed by restriction to a geometric point `s` of `T`
and the identification `(t^* G)_s ≅ G_{s ≫ t}` is the identity. -/
lemma sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso_moduleCat {R T : Scheme.{u}}
    (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    (pointSmallEtale (s ≫ t)).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app G) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) t (s ≫ t) ⟨s, rfl⟩
        ((t)^*[ModuleCat.{u + 1} Λ].obj G) ≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t s).hom.app G = 𝟙 _ := by
  rw [Etale.stalkRestrict_eq_counit]
  have h := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t s).inv.naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app G)
  simp only [Category.assoc]
  rw [reassoc_of% h, ← Functor.map_comp_assoc, Adjunction.left_triangle_components,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- At a geometric point over which a finite morphism `ν` has exactly one geometric point, the
unit `G ⟶ ν_* ν^* G` is an isomorphism on stalks. -/
lemma isIso_sheafFiber_map_unit_of_unique {X Y : Scheme.{u}} (ν : Y ⟶ X) [IsFinite ν]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    [Unique (Scheme.Hom.GeometricFiber ν x)]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((pointSmallEtale x).sheafFiber.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app G)) := by
  have h₁ : IsIso (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν x default
      ((ν)^*[ModuleCat.{u + 1} Λ].obj G)) := by
    rw [← Pi.lift_comp_π (fun t ↦ Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν x t
      ((ν)^*[ModuleCat.{u + 1} Λ].obj G)) default, ← productUniqueIso_hom]
    infer_instance
  obtain ⟨s, hs⟩ : Scheme.Hom.GeometricFiber ν x := default
  have hd : (default : Scheme.Hom.GeometricFiber ν x) = ⟨s, hs⟩ := Subsingleton.elim _ _
  subst hs
  rw [hd] at h₁
  have h := sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso_moduleCat ν G s
  have : IsIso (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν (s ≫ ν) ⟨s, rfl⟩
      ((ν)^*[ModuleCat.{u + 1} Λ].obj G) ≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν s).hom.app G) := inferInstance
  have : IsIso ((pointSmallEtale (s ≫ ν)).sheafFiber.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app G) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν (s ≫ ν) ⟨s, rfl⟩
        ((ν)^*[ModuleCat.{u + 1} Λ].obj G) ≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν s).hom.app G) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν (s ≫ ν)
    ⟨s, rfl⟩ ((ν)^*[ModuleCat.{u + 1} Λ].obj G) ≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν s).hom.app G)

/-- Over a geometric point of the open `U` over which `ν` is an isomorphism, `ν` has exactly one
geometric point. -/
noncomputable abbrev uniqueGeometricFiberOfIsIsoPullbackSnd {X Y U : Scheme.{u}} (ν : Y ⟶ X)
    (j : U ⟶ X) (hν : IsIso (pullback.snd ν j)) {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ U) : Unique (Scheme.Hom.GeometricFiber ν (s ≫ j)) where
  default := ⟨s ≫ inv (pullback.snd ν j) ≫ pullback.fst ν j, by
    rw [Category.assoc, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩
  uniq t := by
    ext1
    have h : pullback.lift t.1 s t.2 = s ≫ inv (pullback.snd ν j) := by
      rw [IsIso.eq_comp_inv, pullback.lift_snd]
    simp only
    rw [← reassoc_of% h, pullback.lift_fst]

/-- If a finite `ν : Y ⟶ X` is an isomorphism over an open `j : U ⟶ X`, then the restriction
to `U` of the unit `F ⟶ ν_* ν^* F` is an isomorphism. -/
lemma isIso_upperStar_map_unit_of_isIso_pullbackSnd {X Y U : Scheme.{u}} (ν : Y ⟶ X)
    [IsFinite ν] (j : U ⟶ X) (hν : IsIso (pullback.snd ν j))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((j)^*[ModuleCat.{u + 1} Λ].map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app F)) := by
  refine isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app F
  have : IsIso ((pointSmallEtale (U.algClosurePoint s)).sheafFiber.map
      ((j)^*[ModuleCat.{u + 1} Λ].map η)) := by
    have := uniqueGeometricFiberOfIsIsoPullbackSnd ν j hν (U.algClosurePoint s)
    have := isIso_sheafFiber_map_unit_of_unique ν (U.algClosurePoint s ≫ j) F
    have h := NatIso.naturality_2
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) j (U.algClosurePoint s)) η
    rw [Functor.comp_map] at h
    rw [← h]
    infer_instance
  have : IsIso (((pointSmallEtale (U.algClosurePoint s)).ulift.{u + 1}).sheafFiber.map
      ((j)^*[ModuleCat.{u + 1} Λ].map η)) := by
    rw [← NatIso.naturality_2 ((pointSmallEtale (U.algClosurePoint s)).uliftSheafFiberIso
      (ModuleCat.{u + 1} Λ)) ((j)^*[ModuleCat.{u + 1} Λ].map η)]
    infer_instance
  exact this

end Unit

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The comparison map `Rf_*(M_X) ⟶ R(ν ≫ f)_*(ν^* M_X)` for a finite `ν : Y ⟶ X`: the direct
image along `f` of the unit `M_X ⟶ ν_* ν^* M_X`, followed by the identification
`Rf_*(ν_* G) = R(ν ≫ f)_* G` of `AlgebraicGeometry.Etale.rightDerivedLowerStarSingleLowerStarIso`.
It is defined for any sheaf `F` in place of `M_X`. -/
noncomputable def rightDerivedLowerStarUnitComparison {X Y S : Scheme.{u}} (f : X ⟶ S)
    (ν : Y ⟶ X) [IsFinite ν] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F) ⟶
      (R((ν ≫ f)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((ν)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  (R((f)_*[ModuleCat.{u + 1} Λ])).map ((singleFunctor _ 0).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app F)) ≫
    (rightDerivedLowerStarSingleLowerStarIso ν f _).hom

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`: Constant coefficients under a
finite normalization comparison.

Let `f : X ⟶ S` be proper with `S` of finite type over a field `k`, and let `ν : Y ⟶ X` be finite
and surjective. Suppose `ν` is an isomorphism over the open `j : U ⟶ X` complementary to a
closed immersion `i : Z ⟶ X` for which `i ≫ f` is finite. Put `v = ν ≫ f` and let `M` be a finite
`Λ`-module, with constant sheaf `M_X` on `X` (and `ν^* M_X = M_Y` on `Y`). If all `Rᵠv_*(M_Y)`
are constructible, then so are all `Rᵠf_*(M_X)`, and the natural map
`Rᵠf_*(M_X) ⟶ Rᵠv_*(M_Y)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarUnitComparison`) is an
isomorphism for every `q ≥ 2`. The blueprint takes `Z` reduced; this is not needed. -/
theorem constructible_and_isIso_rightDerivedLowerStarUnitComparison {k : Type u} [Field k]
    {X Y Z U S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) [IsProper f] (ν : Y ⟶ X) [IsFinite ν] [Surjective ν]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (hν : IsIso (pullback.snd ν j))
    [IsFinite (i ≫ f)] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hv : ∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((ν ≫ f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((ν)^*[ModuleCat.{u + 1} Λ].obj ((constantSheaf X.smallEtaleTopology _).obj M)))))) :
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology _).obj M))))) ∧
    ∀ q : ℤ, 2 ≤ q → IsIso ((homologyFunctor _ q).map
      (rightDerivedLowerStarUnitComparison f ν
        ((constantSheaf X.smallEtaleTopology _).obj M))) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ aS)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ aS)
  have : IsNoetherian X := {}
  set F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  set η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app F
  have : Mono η := mono_unit_app_of_surjective Λ ν ν.surjective F
  -- the source and the target of the unit are constructible, hence so is its cokernel `Q`
  have hF : IsConstructibleSheaf F :=
    ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩
  have : IsConstructibleSheaf ((𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj F) :=
    hF
  have : IsConstructibleSheaf
      (((ν)^*[ModuleCat.{u + 1} Λ] ⋙ (ν)_*[ModuleCat.{u + 1} Λ]).obj F) :=
    have := IsConstructibleSheaf.upperStar ν F
    Scheme.IsConstructibleSheaf.lowerStar_of_isFinite ν _
  have := IsConstructibleSheaf.cokernel η
  -- the cokernel `Q` of the unit is supported on `Z`
  have hjQ : IsZero ((j)^*[ModuleCat.{u + 1} Λ].obj (cokernel η)) := by
    have := isIso_upperStar_map_unit_of_isIso_pullbackSnd ν j hν F
    exact (isZero_cokernel_of_epi ((j)^*[ModuleCat.{u + 1} Λ].map η)).of_iso
      (PreservesCokernel.iso (j)^*[ModuleCat.{u + 1} Λ] η)
  obtain ⟨G, ⟨e⟩⟩ := mem_essImage_lowerStar_of_isZero_upperStar i
    (by rw [hij, compl_compl]) hjQ
  have hG : IsConstructibleSheaf G := by
    have := IsConstructibleSheaf.upperStar i (cokernel η)
    exact IsConstructibleSheaf.of_iso ((i)^*[ModuleCat.{u + 1} Λ].mapIso e.symm ≪≫
      asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app G))
  -- the triangle `Rf_* F ⟶ Rf_* ν_* ν^* F ⟶ Rf_* Q ⟶`
  let Sc := ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
  have hSc : Sc.ShortExact := { exact := ShortComplex.exact_cokernel η }
  let T := (R((f)_*[ModuleCat.{u + 1} Λ])).mapTriangle.obj hSc.singleTriangle
  have hT : T ∈ distTriang _ :=
    (R((f)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hSc.singleTriangle_distinguished
  let e₃ : T.obj₃ ≅ (R((i ≫ f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj G) :=
    (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso ((singleFunctor _ 0).mapIso e.symm) ≪≫
      rightDerivedLowerStarSingleLowerStarIso i f G
  have h₃ : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S T.obj₃ :=
    (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso e₃.symm
      (boundedConstructible_rightDerivedLowerStar_of_isFinite Λ (i ≫ f)
        (DerivedCategory.boundedConstructible_singleFunctor_obj G 0)).2
  have h₂ : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S T.obj₂ :=
    (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
      (rightDerivedLowerStarSingleLowerStarIso ν f _).symm hv
  have hz (q : ℤ) (hq : q ≠ 0) : IsZero ((homologyFunctor _ q).obj T.obj₃) :=
    (isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite (i ≫ f) G q hq).of_iso
      ((homologyFunctor _ q).mapIso e₃)
  refine ⟨(Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
    ).ext_of_isTriangulatedClosed₁ T hT h₂ h₃, fun q hq ↦ ?_⟩
  -- in degrees `q ≥ 2`, the adjacent homology sheaves of `Rf_* Q` vanish
  have : IsIso ((homologyFunctor _ q).map ((R((f)_*[ModuleCat.{u + 1} Λ])).map
      ((singleFunctor _ 0).map η))) :=
    isIso_homologyMap_mor₁ T hT (q - 1) q (by lia) (hz _ (by lia)) (hz _ (by lia))
  rw [rightDerivedLowerStarUnitComparison, Functor.map_comp]
  infer_instance


end Etale

end AlgebraicGeometry
