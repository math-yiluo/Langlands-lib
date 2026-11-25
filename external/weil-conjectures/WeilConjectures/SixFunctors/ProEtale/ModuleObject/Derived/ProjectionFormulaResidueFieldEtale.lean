/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryFactors
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginTensor

/-!
# Étale projection formulas for module objects over `𝔽̲_E`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with residue field `T = 𝔽_E`, `Λ = 𝔽̲_E` the
condensed ring `C(-, 𝔽_E)` and, on a scheme `X`, `Φ_X` the comparison
(`ProEtale.finiteCoefficientDerivedEquivalence`) of the derived category of module objects over
`Λ_X` with the derived category of pro-étale sheaves of `𝔽_E`-modules. This file transports
projection formulas for complexes of étale sheaves of `𝔽_E`-modules to module objects over `Λ`.

Let `f : Z ⟶ Y` be quasi-compact and quasi-separated, `K` on `Z` and `L` on `Y` module complexes
with `Φ_Z K ≅ ν^* M` and `Φ_Y L ≅ ν^* N` for complexes `M`, `N` of étale sheaves, `M` and
`M ⊗ᴸ Lf^* N` bounded below. If the étale projection map `Rf_* M ⊗ᴸ N ⟶ Rf_*(M ⊗ᴸ Lf^* N)` is an
isomorphism, so is the projection morphism `Rf_* K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^* L)` of module objects
(`ProEtale.CondensedRing.isIso_projectionMorphism_residueField_of_etale`). The proof chains

* the comparison `ν^*` (`ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived`),
  which gives the pro-étale projection formula at `(Φ_Z K, Φ_Y L)`;
* the isomorphism `D(G) ≅ Φ` of the reading `G = ProEtale.residueFieldModuleSheaf` of module
  objects as sheaves of `𝔽_E`-modules with `Φ`
  (`ProEtale.residueFieldModuleSheafIsoOfSection`), and the transport along `D(G)`
  (`ProEtale.CondensedRing.isIso_projectionMap_residueField_of_moduleCat`).

Since `𝔽_E` is a field, `M ⊗ᴸ Lf^* N` is bounded below as soon as `M` and `N` are, so the
statement applies to all module complexes bounded below of étale origin
(`ProEtale.CondensedRing.isIso_projectionMorphism_residueField_of_plusEtaleOrigin`). We deduce:

* the **relative Künneth formula** over a field `k`: for `W = X ×_k Y` with projections `p₁`,
  `p₂`, the projection morphism `Rp₂_*(Lp₁^* A) ⊗ᴸ B ⟶ Rp₂_*(Lp₁^* A ⊗ᴸ Lp₂^* B)` is an
  isomorphism
  (`ProEtale.CondensedRing.isIso_projectionMorphism_residueField_leftDerivedUpperStar`),
  from `Etale.isIso_rightDerivedLowerStarProjectionMap_leftDerivedUpperStar`;
* the **projection formula over a separably closed point** `a_Y : Y ⟶ Spec k`
  (`ProEtale.CondensedRing.isIso_projectionMorphism_residueField_of_isSepClosed`), from
  `Etale.isIso_rightDerivedLowerStarProjectionMap_app_app`, in particular at
  `C = Ra_{X*} A`
  (`ProEtale.CondensedRing.isIso_projectionMorphism_residueField_rightDerivedLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {Z Y : Scheme.{u}}

/-- The derived pullback `Lf^*` of étale sheaves of `Λ`-modules preserves bounded below
complexes. -/
lemma plus_leftDerivedUpperStar_obj (f : Z ⟶ Y)
    {N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : DerivedCategory.TStructure.t.plus N) :
    DerivedCategory.TStructure.t.plus ((L(upperStar (ModuleCat.{u + 1} Λ) f)).obj N) := by
  obtain ⟨b, hb⟩ := hN
  have : N.IsGE b := hb
  have := (upperStar (ModuleCat.{u + 1} Λ) f).isGE_mapDerivedCategory_obj N b
  exact ⟨b, DerivedCategory.TStructure.t.isGE_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).app N).symm b⟩

/-- Over a field `Λ`, for bounded below complexes `M` on `Z_ét` and `N` on `Y_ét` and any
`f : Z ⟶ Y`, the complex `M ⊗ᴸ Lf^* N` is bounded below: `Lf^* N` is bounded below, and every
étale sheaf of `Λ`-modules is flat (`AlgebraicGeometry.Etale.flat_of_isField`). -/
lemma plus_derivedTensor_leftDerivedUpperStar_of_isField (hΛ : IsField Λ) (f : Z ⟶ Y)
    {M : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.TStructure.t.plus M) (hN : DerivedCategory.TStructure.t.plus N) :
    DerivedCategory.TStructure.t.plus
      (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj M).obj
        ((L(upperStar (ModuleCat.{u + 1} Λ) f)).obj N)) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := plus_leftDerivedUpperStar_obj f hN
  exact ⟨a + b, DerivedCategory.isGE_tensor_of_torAmplitudeGE
    (DerivedCategory.torAmplitudeGE_of_isGE_of_forall_flat (flat_of_isField hΛ) M a) _ b⟩

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The derived reading `D(G)` of module objects over `𝔽̲_{E,X}` as pro-étale sheaves of
`𝔽_E`-modules is the comparison `Φ_X = ProEtale.finiteCoefficientDerivedEquivalence`: derive the
isomorphism `G ≅ ProEtale.finiteCoefficientModEquivalence` of
`ProEtale.residueFieldModuleSheafIsoOfSection`. -/
noncomputable def residueFieldModuleSheafMapDerivedCategoryIso (X : Scheme.{u}) :
    (residueFieldModuleSheaf X ℓ E).mapDerivedCategory ≅
      (finiteCoefficientDerivedEquivalence X (integersResidueField ℓ E)).functor :=
  have := Functor.additive_of_iso
    (residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E))
  Functor.mapDerivedCategoryNatIso
    (residueFieldModuleSheafIsoOfSection X ℓ E (residueFieldSectionFac X ℓ E))

variable {Z Y : Scheme.{u}} (f : Z ⟶ Y)

/-- The projection morphism of module objects over `𝔽̲_E` at `(K, L)` is an isomorphism as soon
as the projection map of pro-étale sheaves of `𝔽_E`-modules is an isomorphism at
`(Φ_Z K, Φ_Y L)`. -/
lemma isIso_projectionMorphism_residueField_of_finiteCoefficient
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Z)))
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y)))
    (h : IsIso (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f).app
        ((finiteCoefficientDerivedEquivalence Z (integersResidueField ℓ E)).functor.obj K)).app
        ((finiteCoefficientDerivedEquivalence Y (integersResidueField ℓ E)).functor.obj L))) :
    IsIso ((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f).projectionMorphism K L) :=
  have := NatTrans.isIso_app_app_of_iso
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)
    ((residueFieldModuleSheafMapDerivedCategoryIso ℓ E Z).app K).symm
    ((residueFieldModuleSheafMapDerivedCategoryIso ℓ E Y).app L).symm
  isIso_projectionMap_residueField_of_moduleCat ℓ E f K L this

/-- **The étale projection formula transported to module objects over `𝔽̲_E`.** Let
`f : Z ⟶ Y` be quasi-compact and quasi-separated, `K` on `Z` and `L` on `Y` module complexes over
`𝔽̲_E`, and `M`, `N` complexes of étale sheaves of `𝔽_E`-modules with `ν^* M ≅ Φ_Z K` and
`ν^* N ≅ Φ_Y L`, such that `M` and `M ⊗ᴸ Lf^* N` are bounded below. If the étale projection map
`Rf_* M ⊗ᴸ N ⟶ Rf_*(M ⊗ᴸ Lf^* N)` is an isomorphism, so is the projection morphism
`Rf_* K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^* L)`. -/
theorem isIso_projectionMorphism_residueField_of_etale [QuasiCompact f] [QuasiSeparated f]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Z))}
    {L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y))}
    {M : DerivedCategory (Sheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)))}
    {N : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)))}
    (eK : D(ν^*(Z)[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]).obj M ≅
      (finiteCoefficientDerivedEquivalence Z (integersResidueField ℓ E)).functor.obj K)
    (eL : D(ν^*(Y)[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]).obj N ≅
      (finiteCoefficientDerivedEquivalence Y (integersResidueField ℓ E)).functor.obj L)
    (hM : DerivedCategory.TStructure.t.plus M)
    (hMN : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Z).obj M).obj
        ((L(Etale.upperStar (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)).obj N)))
    (h : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f).app M).app N)) :
    IsIso ((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f).projectionMorphism
        K L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived
    (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f M N hM hMN
  refine isIso_projectionMorphism_residueField_of_finiteCoefficient ℓ E f K L ?_
  exact NatTrans.isIso_app_app_of_iso
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)
    ((ν^*(Z)[ModuleCat.{u + 1}
      (ResidueFieldCoeff.{u} ℓ E)]).leftDerivedFunctorIsoMapDerivedCategory.app
      M ≪≫ eK)
    ((ν^*(Y)[ModuleCat.{u + 1}
      (ResidueFieldCoeff.{u} ℓ E)]).leftDerivedFunctorIsoMapDerivedCategory.app
      N ≪≫ eL)

/-- **The étale projection formula transported to module objects of étale origin.** For
`f : Z ⟶ Y` quasi-compact and quasi-separated and module complexes `K` on `Z`, `L` on `Y` over
`𝔽̲_E` with `Φ_Z K` and `Φ_Y L` bounded below of étale origin, the projection morphism
`Rf_* K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^* L)` is an isomorphism as soon as the étale projection map is an
isomorphism at all pairs of bounded below complexes. Since `𝔽_E` is a field, `M ⊗ᴸ Lf^* N` is
bounded below for `M`, `N` bounded below
(`AlgebraicGeometry.Etale.plus_derivedTensor_leftDerivedUpperStar_of_isField`). -/
theorem isIso_projectionMorphism_residueField_of_plusEtaleOrigin [QuasiCompact f]
    [QuasiSeparated f]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Z))}
    {L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y))}
    (hK : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) Z
      ((finiteCoefficientDerivedEquivalence Z (integersResidueField ℓ E)).functor.obj K))
    (hL : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersResidueField ℓ E)).functor.obj L))
    (h : ∀ (M : DerivedCategory (Sheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))))
      (N : DerivedCategory (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)))),
      DerivedCategory.TStructure.t.plus M → DerivedCategory.TStructure.t.plus N →
        IsIso (((Etale.rightDerivedLowerStarProjectionMap
          (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f).app M).app N)) :
    IsIso ((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f).projectionMorphism
        K L) := by
  obtain ⟨M, hM, ⟨eK⟩⟩ := hK
  obtain ⟨N, hN, ⟨eL⟩⟩ := hL
  exact isIso_projectionMorphism_residueField_of_etale ℓ E f eK eL hM
    (Etale.plus_derivedTensor_leftDerivedUpperStar_of_isField (isField_residueFieldCoeff ℓ E) f
      hM hN) (h M N hM hN)

/-- A quasi-compact morphism locally of finite type to the spectrum of a field is quasi-separated:
its source is noetherian (`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`). -/
lemma _root_.AlgebraicGeometry.quasiSeparated_of_locallyOfFiniteType_spec_field {k : Type u}
    [Field k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] : QuasiSeparated aX :=
  have := isNoetherian_of_locallyOfFiniteType aX
  (quasiSeparated_iff_quasiSeparatedSpace aX).2 inferInstance

/-- **The relative Künneth formula for module objects over `𝔽̲_E`.** Let `k` be a field in which
the characteristic of `𝔽_E` is invertible, `W = X ×_k Y` with `X`, `Y` quasi-compact and locally of
finite type over `k`, and `A` on `X`, `B` on `Y` module complexes over `𝔽̲_E` bounded below of
étale origin. Then the projection morphism `Rp₂_*(Lp₁^* A) ⊗ᴸ B ⟶ Rp₂_*(Lp₁^* A ⊗ᴸ Lp₂^* B)` is
an isomorphism: this is the étale relative projection formula
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_leftDerivedUpperStar`, transported
along `ν^*` and `Φ`. -/
theorem isIso_projectionMorphism_residueField_leftDerivedUpperStar {k : Type u} [Field k]
    [HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k))] {X Y W : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] {p₁ : W ⟶ X} {p₂ : W ⟶ Y}
    (sq : IsPullback p₁ p₂ aX aY)
    {A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) X))}
    {B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y))}
    (hA : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) X
      ((finiteCoefficientDerivedEquivalence X (integersResidueField ℓ E)).functor.obj A))
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersResidueField ℓ E)).functor.obj B)) :
    IsIso ((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) p₂).projectionMorphism
        (L((p₁)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj A) B) := by
  have := quasiSeparated_of_locallyOfFiniteType_spec_field aX
  have : QuasiCompact p₂ := MorphismProperty.of_isPullback sq ‹_›
  have : QuasiSeparated p₂ := MorphismProperty.of_isPullback sq ‹_›
  obtain ⟨M, hM, ⟨eA⟩⟩ := hA
  obtain ⟨N, hN, ⟨eB⟩⟩ := hB
  have hM' := Etale.plus_leftDerivedUpperStar_obj p₁ hM
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_leftDerivedUpperStar
    (ResidueFieldCoeff.{u} ℓ E) aX aY p₁ p₂ sq M N
  refine isIso_projectionMorphism_residueField_of_etale ℓ E p₂ ?_ eB hM'
    (Etale.plus_derivedTensor_leftDerivedUpperStar_of_isField (isField_residueFieldCoeff ℓ E) p₂
      hM' hN) this
  exact ((ν^*(W)[ModuleCat.{u + 1}
      (ResidueFieldCoeff.{u} ℓ E)]).leftDerivedFunctorIsoMapDerivedCategory.app
      _).symm ≪≫
    ((leftDerivedComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p₁).app M).symm ≪≫
    (L(ProEtale.upperStar (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p₁)).mapIso
      ((ν^*(X)[ModuleCat.{u + 1}
      (ResidueFieldCoeff.{u} ℓ E)]).leftDerivedFunctorIsoMapDerivedCategory.app
        M ≪≫ eA) ≪≫
    ((leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso p₁
      (integersResidueField ℓ E)).app A).symm

/-- **The projection formula over a separably closed point for module objects over `𝔽̲_E`.**
Let `k` be separably closed, `a_Y : Y ⟶ Spec k` quasi-compact and locally of finite type, and
`B` on `Y`, `C` on `Spec k` module complexes over `𝔽̲_E` bounded below of étale origin. Then the
projection morphism `Ra_{Y*} B ⊗ᴸ C ⟶ Ra_{Y*}(B ⊗ᴸ La_Y^* C)` is an isomorphism: this is the
étale projection formula over a separably closed point
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app`), transported along
`ν^*` and `Φ`. -/
theorem isIso_projectionMorphism_residueField_of_isSepClosed {k : Type u} [Field k]
    [IsSepClosed k] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY]
    {B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y))}
    {C : DerivedCategory (Mod (Sheaf (ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E))
        (Spec (.of k))))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersResidueField ℓ E)).functor.obj B))
    (hC : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) (Spec (.of k))
      ((finiteCoefficientDerivedEquivalence (Spec (.of k)) (integersResidueField ℓ E)).functor.obj
        C)) :
    IsIso ((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) aY).projectionMorphism
        B C) :=
  have := quasiSeparated_of_locallyOfFiniteType_spec_field aY
  isIso_projectionMorphism_residueField_of_plusEtaleOrigin ℓ E aY hB hC fun M N _ _ ↦
    Etale.isIso_rightDerivedLowerStarProjectionMap_app_app (ResidueFieldCoeff.{u} ℓ E) aY M N

/-- **The projection formula over a separably closed point at a direct image**: for `k`
separably closed, `a_X : X ⟶ Spec k`, `a_Y : Y ⟶ Spec k` quasi-compact and locally of finite
type, and module complexes `A` on `X`, `B` on `Y` over `𝔽̲_E` bounded below of étale origin, the
projection morphism `Ra_{Y*} B ⊗ᴸ Ra_{X*} A ⟶ Ra_{Y*}(B ⊗ᴸ La_Y^* Ra_{X*} A)` is an isomorphism.
The direct image `Ra_{X*} A` is bounded below of étale origin
(`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj`). -/
theorem isIso_projectionMorphism_residueField_rightDerivedLowerStar {k : Type u} [Field k]
    [IsSepClosed k] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    {A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) X))}
    {B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) Y))}
    (hA : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) X
      ((finiteCoefficientDerivedEquivalence X (integersResidueField ℓ E)).functor.obj A))
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E))) Y
      ((finiteCoefficientDerivedEquivalence Y (integersResidueField ℓ E)).functor.obj B)) :
    IsIso ((derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) aY).projectionMorphism B
        (R((aX)_*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧).obj A)) :=
  have := quasiSeparated_of_locallyOfFiniteType_spec_field aX
  isIso_projectionMorphism_residueField_of_isSepClosed ℓ E aY hB
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj _ aX hA)

end AlgebraicGeometry.ProEtale.CondensedRing
