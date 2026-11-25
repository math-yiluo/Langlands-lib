/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.DualizableDetection
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!
# Pro-étale local properties of complexes of module objects

Let `Λ` be a commutative condensed ring, `X` a scheme and `{gᵢ : Uᵢ ⟶ X}` a pro-étale cover.
For complexes `K` of module objects over `Λ_X`:

* a cohomology sheaf `Hⁿ(K)` vanishes, resp. is pro-étale locally finitely presented, as soon as
  the cohomology sheaves `Hⁿ(Lgᵢ^* K) ≅ gᵢ^* Hⁿ(K)` do
  (`ProEtale.CondensedRing.isZero_homology_of_cover`,
  `ProEtale.CondensedRing.isLocallyFinitelyPresented_homology_of_cover`);
* the derived pullbacks `Lgᵢ^*` jointly reflect isomorphisms
  (`ProEtale.CondensedRing.isIso_of_forall_isIso_leftDerivedUpperStar_map`);
* a complex with cohomology concentrated in a finite interval and pro-étale locally finitely
  presented cohomology sheaves is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_of_isLocallyFinitelyPresented_homology_of_le`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- **Common refinement of two pro-étale covers.** Let `Q₁` and `Q₂` be properties of morphisms
to `X` which are stable under precomposition. If `Q₁` holds for the members of a pro-étale cover
`𝒰` and `Q₂` for those of a pro-étale cover `𝒱`, both hold for the members of a common
refinement. -/
lemma exists_cover_forall_and {X : Scheme.{u}} (Q₁ Q₂ : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hQ₁ : ∀ ⦃Y W : Scheme.{u}⦄ (a : Y ⟶ W) (f : W ⟶ X), Q₁ W f → Q₁ Y (a ≫ f))
    (hQ₂ : ∀ ⦃Y W : Scheme.{u}⦄ (a : Y ⟶ W) (f : W ⟶ X), Q₂ W f → Q₂ Y (a ≫ f))
    (𝒰 𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage X) (h𝒰 : ∀ i, Q₁ (𝒰.X i) (𝒰.f i))
    (h𝒱 : ∀ j, Q₂ (𝒱.X j) (𝒱.f j)) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Q₁ (𝒲.X k) (𝒲.f k) ∧ Q₂ (𝒲.X k) (𝒲.f k) := by
  refine ⟨𝒰.bind fun i ↦ 𝒱.pullback₁ (𝒰.f i), ?_⟩
  rintro ⟨i, j⟩
  have hb : (𝒱.pullback₁ (𝒰.f i)).f j ≫ 𝒰.f i = pullback.snd (𝒰.f i) (𝒱.f j) ≫ 𝒱.f j :=
    pullback.condition
  refine ⟨hQ₁ _ _ (h𝒰 i), ?_⟩
  have := hQ₂ (pullback.snd (𝒰.f i) (𝒱.f j)) _ (h𝒱 j)
  rw [← hb] at this
  exact this

/-- A module object over `Λ_X` vanishes if its pullbacks to the members of a pro-étale cover
vanish. -/
lemma isZero_of_forall_isZero_upperStar_cover {X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ∀ i, IsZero ((𝒰.f i)^*⟦Λ⟧.obj M)) : IsZero M := by
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  refine isZero_of_isZero_X Λ ?_
  have : IsIso (0 : M.X ⟶ 0) := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} (0 : M.X ⟶ 0) 𝒰.f 𝒰.mem₀
      fun i ↦ ?_
    have h₁ : IsZero ((𝒰.f i)^*[Ab.{u + 1}].obj M.X) :=
      ((Mod.forget _).map_isZero (h i)).of_iso (upperStarObjXIso Λ _ M).symm
    have h₂ : IsZero ((𝒰.f i)^*[Ab.{u + 1}].obj 0) := Functor.map_isZero _ (isZero_zero _)
    have : IsIso ((𝒰.f i)^*[Ab.{u + 1}].map (0 : M.X ⟶ 0)) :=
      isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) _).1 this
  exact (isZero_zero _).of_iso (asIso (0 : M.X ⟶ 0))

/-- The `n`-th cohomology sheaf of a complex `K` vanishes if the `n`-th cohomology sheaves of its
derived pullbacks to the members of a pro-étale cover vanish. -/
lemma isZero_homology_of_cover {X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (n : ℤ)
    (h : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ n).obj ((L((𝒰.f i)^*⟦Λ⟧)).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj K) :=
  isZero_of_forall_isZero_upperStar_cover 𝒰 fun i ↦
    (h i).of_iso ((leftDerivedUpperStarHomologyIso Λ (𝒰.f i) n).app K)

/-- The `n`-th cohomology sheaf of a complex `K` is pro-étale locally finitely presented if the
`n`-th cohomology sheaves of its derived pullbacks to the members of a pro-étale cover are. -/
lemma isLocallyFinitelyPresented_homology_of_cover {X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (n : ℤ)
    (h : ∀ i, IsLocallyFinitelyPresented (condensedRingObj Λ (𝒰.X i))
      ((DerivedCategory.homologyFunctor _ n).obj ((L((𝒰.f i)^*⟦Λ⟧)).obj K))) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj K) :=
  isLocallyFinitelyPresented_of_cover 𝒰 fun i ↦
    (h i).of_iso ((leftDerivedUpperStarHomologyIso Λ (𝒰.f i) n).app K).symm

/-- The derived pullbacks to the members of a pro-étale cover jointly reflect isomorphisms: the
cone of a morphism whose pullbacks are isomorphisms has vanishing cohomology sheaves. -/
lemma isIso_of_forall_isIso_leftDerivedUpperStar_map {X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    {K K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (φ : K ⟶ K')
    (h : ∀ i, IsIso ((L((𝒰.f i)^*⟦Λ⟧)).map φ)) : IsIso φ := by
  obtain ⟨M, g, g', hT⟩ := distinguished_cocone_triangle φ
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  refine isZero_of_forall_isZero_homology Λ fun n ↦ isZero_homology_of_cover 𝒰 M n fun i ↦ ?_
  -- `Lgᵢ^*` is identified with the triangulated functor induced by the exact functor `gᵢ^*`
  have hi : IsIso (((𝒰.f i)^*⟦Λ⟧).mapDerivedCategory.map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ (𝒰.f i)) φ).1 (h i)
  exact ((DerivedCategory.homologyFunctor _ n).map_isZero
    ((Triangle.isZero₃_iff_isIso₁ _
      (((𝒰.f i)^*⟦Λ⟧).mapDerivedCategory.map_distinguished _ hT)).2 hi)).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ (𝒰.f i)).app M))

/-- A pro-étale locally finitely presented module object over `Λ_X` is constructible, with respect
to the trivial stratification of `X`. -/
lemma isConstructibleModuleObject_of_isLocallyFinitelyPresented {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M :=
  ⟨Scheme.Stratification.trivial X, fun _ ↦
    (isLocallyFinitelyPresented_mapMod_iff Λ (𝟙 X) M).2
      (IsLocallyFinitelyPresented.upperStar Λ (𝟙 X) hM)⟩

/-- A complex whose cohomology sheaves vanish outside `[a, b]` and are pro-étale locally finitely
presented is bounded constructible. -/
lemma boundedConstructible_of_isLocallyFinitelyPresented_homology_of_le {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (a b : ℤ)
    (hab : ∀ n, (n < a ∨ b < n) → IsZero ((DerivedCategory.homologyFunctor _ n).obj K))
    (hK : ∀ n, IsLocallyFinitelyPresented (condensedRingObj Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) :
    boundedConstructible (condensedRingObj Λ X) K :=
  (mem_boundedConstructible_iff _ K).2 ⟨⟨a, b, hab⟩, fun n ↦
    isConstructibleModuleObject_of_isLocallyFinitelyPresented (hK n)⟩

variable (Λ) in
/-- The derived pullback of a module object placed in degree `q` is the pullback, placed in
degree `q`. -/
noncomputable def leftDerivedUpperStarSingleFunctorIso {W X : Scheme.{u}} (g : W ⟶ X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (q : ℤ) :
    (L((g)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ q).obj F) ≅
      (DerivedCategory.singleFunctor _ q).obj ((g)^*⟦Λ⟧.obj F) :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _ ≪≫
    (((g)^*⟦Λ⟧).mapDerivedCategorySingleFunctor q).app F

/-- **Dualizability is pro-étale local.** A complex of module objects over `Λ_X` whose derived
pullbacks to the members of a pro-étale cover are dualizable is dualizable: the derived pullbacks
are monoidal, jointly conservative and commute with internal homs, the members of the cover being
weakly étale. -/
theorem isDualizable_of_cover {X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (h : ∀ i, IsDualizable ((L((𝒰.f i)^*⟦Λ⟧)).obj K)) : IsDualizable K := by
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  let _ (i : 𝒰.I₀) : BraidedCategory (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (𝒰.X i))
      Ab.{u + 1}) (condensedRingObj Λ (𝒰.X i)))) :=
    (DerivedCategory.nonempty_braidedCategory _).some
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have (i : 𝒰.I₀) := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale Λ (𝒰.f i) K
  exact isDualizable_of_isDualizable_map (fun i ↦ L((𝒰.f i)^*⟦Λ⟧))
    (fun _ _ φ hφ ↦ isIso_of_forall_isIso_leftDerivedUpperStar_map 𝒰 φ hφ) h

/-- The derived pullback `Lg^*` sends a left dual `Y` of `K` to a left dual of `Lg^* K`: any left
dual of `Lg^* K` is isomorphic to `Lg^* Y`. -/
lemma nonempty_leftDerivedUpperStar_obj_iso_of_exactPairing {W X : Scheme.{u}} (g : W ⟶ X)
    {K Y : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (pY : ExactPairing Y K)
    {Y' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))} (p : ExactPairing Y' ((L((g)^*⟦Λ⟧)).obj K)) :
    Nonempty ((L((g)^*⟦Λ⟧)).obj Y ≅ Y') :=
  letI := monoidal_leftDerivedUpperStar Λ g
  ⟨leftDualIso (ExactPairing.map L((g)^*⟦Λ⟧) Y K) p⟩

end AlgebraicGeometry.ProEtale.CondensedRing
