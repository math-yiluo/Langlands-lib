/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatWeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Dualizability is local on the small pro-étale site

Let `Λ` be a commutative ring and `X` a scheme. For a weakly étale morphism `g : W ⟶ X`, the
derived pullback `Lg^*` preserves dualizable objects of `D(X_proét, Λ)`
(`AlgebraicGeometry.ProEtale.isDualizable_leftDerivedUpperStar_obj`), and an object whose
derived pullbacks to the members of a pro-étale covering family are dualizable is dualizable
(`AlgebraicGeometry.ProEtale.isDualizable_of_cover`).

## Strategy

The pullback `g^*` along a weakly étale morphism is an exact monoidal functor, which commutes
with internal homs (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`), preserves flat
sheaves (`AlgebraicGeometry.ProEtale.preservesFlat_upperStar_of_weaklyEtale`) and has an exact
left adjoint (the left Kan extension along the localization functor, followed by
sheafification). So the chain-level dualizability criterion transfers along `g^*`
(`DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_map_iff`): there is a morphism `φ` of
`D(X_proét)` such that `K` is dualizable if and only if `φ` is an isomorphism, and `Lg^*K` is
dualizable if and only if `Lg^*φ` is an isomorphism, for every weakly étale `g`. The derived
pullbacks along a pro-étale covering family are jointly conservative.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- **The derived pullbacks along a pro-étale covering family are jointly conservative.** A
morphism of `D(X_proét)` whose derived pullbacks to the members of a pro-étale covering family
are isomorphisms is an isomorphism: the pullbacks commute with the cohomology sheaves, and the
restrictions of sheaves along a covering family are jointly conservative. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_cover {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((L((g i)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_localizationRestriction (ModuleCat.{u + 1} Λ) _ g hg fun i ↦ ?_
  have := h i
  have : IsIso (((g i)^*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso _ (g i) n) φ).2
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((L((g i)^*[ModuleCat.{u + 1} Λ])).map φ))))
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) (g i) inferInstance) _).1 this

section Transfer

variable {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]

/-- A left adjoint of the pullback `g^*` along a weakly étale morphism: the left Kan extension
along the localization functor `W_proét ⥤ X_proét` followed by sheafification. -/
noncomputable def upperStarLeftAdjoint :
    Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)) (ModuleCat.{u + 1} Λ)
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology X)

/-- The adjunction between `upperStarLeftAdjoint g` and `g^*`. -/
noncomputable def upperStarLeftAdjointAdjunction :
    upperStarLeftAdjoint (Λ := Λ) g ⊣ (g)^*[ModuleCat.{u + 1} Λ] :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)) (ModuleCat.{u + 1} Λ)
    (Scheme.ProEt.topology W) (Scheme.ProEt.topology X)).ofNatIsoRight
    (upperStarIsoSheafPushforward (ModuleCat.{u + 1} Λ) g inferInstance).symm

instance : PreservesFiniteLimits (upperStarLeftAdjoint (Λ := Λ) g) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) := inferInstance
  have := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian
    (ModuleCat.{u + 1} Λ) (P := @WeaklyEtale) (inferInstance : WeaklyEtale g)
  exact comp_preservesFiniteLimits (sheafToPresheaf _ _)
    (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).op.lan) ⋙
      presheafToSheaf _ _)

end Transfer

/-- **A single model for dualizability and its pullbacks.** For `K ∈ D(X_proét)` there is a
morphism `φ` of `D(X_proét)` such that `K` is dualizable if and only if `φ` is an isomorphism,
and, for every weakly étale `g : W ⟶ X`, `Lg^*K` is dualizable if and only if `Lg^*φ` is an
isomorphism. The morphism `φ` is the image of the chain-level model `χ` of the comparison
`[K, 𝟙] ⊗ K ⟶ [K, K]` (`DerivedCategory.DualizabilityDatum`), for a flat resolution of `K`. -/
theorem exists_isDualizable_iff_isIso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    ∃ (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (φ : M ⟶ N), (IsDualizable K ↔ IsIso φ) ∧
      ∀ ⦃W : Scheme.{u}⦄ (g : W ⟶ X) [WeaklyEtale g],
        (IsDualizable ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ↔
          IsIso ((L((g)^*[ModuleCat.{u + 1} Λ])).map φ)) := by
  let R := (inferInstance : Abelian.HasFunctorialFlatResolution
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))).some.reduced
  have hι := (ObjectProperty.flat
    (A := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))).essImage_ι_le
  let K₀ := DerivedCategory.Q.objPreimage K
  let P := R.resolutionFunctor.obj K₀
  have : IsIso (DerivedCategory.Q.map (R.resolutionNatTrans.app K₀)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e : K ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (R.resolutionNatTrans.app K₀))).symm
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).2 (R.kFlat_resolutionFunctor_obj hι K₀)
  obtain ⟨d⟩ := DerivedCategory.DualizabilityDatum.nonempty P hP
  refine ⟨_, _, DerivedCategory.Q.map d.χ, ?_, fun W g _ ↦ ?_⟩
  · rw [DerivedCategory.isIso_Q_map_iff_quasiIso, ← d.isDualizable_Q_obj_iff hP]
    exact ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩
  · let G := (g)^*[ModuleCat.{u + 1} Λ]
    have := preservesFlat_upperStar_of_weaklyEtale (Λ := Λ) g
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).leftAdjoint_preservesColimits
    have := (upperStarLeftAdjointAdjunction (Λ := Λ) g).leftAdjoint_preservesColimits
    have := Adjunction.left_adjoint_additive (upperStarLeftAdjointAdjunction (Λ := Λ) g)
    have (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
        IsIso (Functor.LaxMonoidal.ihomComparison G F) :=
      isIso_ihomComparison_upperStar _ g F
    have hGP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
        ((HomotopyCategory.quotient _ (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) :=
      G.kFlatMap_quotient_obj_resolutionFunctor_obj R K₀
    let eG : DerivedCategory.Q ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ g) ≪≫
        G.mapDerivedCategoryFactors
    refine Iff.trans ?_ (NatIso.isIso_map_iff eG d.χ).symm
    rw [Functor.comp_map, DerivedCategory.isIso_Q_map_iff_quasiIso,
      ← d.isDualizable_Q_obj_map_iff G (upperStarLeftAdjointAdjunction (Λ := Λ) g) hGP]
    let e' := (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ eG.app P
    exact ⟨fun h ↦ h.of_iso e', fun h ↦ h.of_iso e'.symm⟩

/-- **Derived pullback along a weakly étale morphism preserves dualizability.** -/
theorem isDualizable_leftDerivedUpperStar_obj {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) : IsDualizable ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨M, N, φ, h, hg⟩ := exists_isDualizable_iff_isIso K
  have := h.1 hK
  exact (hg g).2 inferInstance

/-- **Dualizability is local for the pro-étale topology.** An object of `D(X_proét)` whose
derived pullbacks to the members of a pro-étale covering family are dualizable is
dualizable. -/
theorem isDualizable_of_cover {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, WeaklyEtale (g i)] (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (h : ∀ i, IsDualizable ((L((g i)^*[ModuleCat.{u + 1} Λ])).obj K)) : IsDualizable K := by
  obtain ⟨M, N, φ, hK, hg'⟩ := exists_isDualizable_iff_isIso K
  rw [hK]
  exact isIso_of_isIso_leftDerivedUpperStar_map_of_cover g hg φ fun i ↦ (hg' (g i)).1 (h i)

end AlgebraicGeometry.ProEtale
