/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition

/-!
# Smooth duality is local: descent and composition

Tools for the proof of orientation-free smooth duality (blueprint
`proposition-exceptional-inverse-image-smooth-morphism`), whose statement is local on the source:
the canonical tensor map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`) is an isomorphism and `ω_f` is a shifted
locally constant sheaf of free rank-one modules.

* Isomorphisms, and the vanishing of cohomology sheaves, descend along jointly surjective families
  of étale morphisms.
* A shifted locally constant sheaf of free rank-one modules pulls back to one, and the property
  descends along jointly surjective families of étale morphisms
  (`AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem`).
* The canonical tensor maps compose: if `θ_a` is invertible everywhere, `θ_b` is invertible at
  `K` and `ω_b` is invertible, then `θ_{a ≫ b}` is invertible at `K`; and
  `ω_{a ≫ b} ≅ ω_a ⊗ᴸ La^* ω_b` as soon as `θ_a` is invertible at `ω_b`.
* The canonical tensor maps descend along jointly surjective families of étale morphisms `u_i`
  with `θ_{u_i}` invertible and `ω_{u_i}` invertible.

## Main definitions

- `AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem`

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective`
- `AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem.of_jointlySurjective`
- `AlgebraicGeometry.Etale.nonempty_dualizingComplex_comp_iso_of_isIso`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp_of_forall`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_jointlySurjective`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Descent

variable {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X)
  (hu : ∀ x : X, ∃ (i : ι) (y : U i), (u i).base y = x)
include hu

/-- Isomorphisms of `D(X_ét, Λ)` descend along a jointly surjective family of étale morphisms
`u_i : U_i ⟶ X`: a morphism `φ` with every `Lu_i^* φ` invertible is invertible. The pullbacks
are exact, so they commute with the cohomology sheaves, and the pullbacks along a jointly
surjective family reflect isomorphisms of sheaves. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : ∀ i, IsIso ((L((u i)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) u hu _
    fun i ↦ ?_
  have h' : IsIso (D((u i)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ (u i)) φ).1 (h i)
  exact (NatIso.isIso_map_iff
    (((u i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((u i)^*[ModuleCat.{u + 1} Λ]).map φ))

/-- The vanishing of a sheaf descends along a jointly surjective family of morphisms. -/
theorem isZero_of_isZero_upperStar_obj_of_jointlySurjective
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ i, IsZero (((u i)^*[ModuleCat.{u + 1} Λ]).obj F)) : IsZero F := by
  have : IsIso (0 : F ⟶ F) :=
    Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) u hu _
      fun i ↦ by
        rw [Functor.map_zero]
        exact ⟨0, (h i).eq_of_src _ _, (h i).eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : F ⟶ F), zero_comp]

/-- The vanishing of an object of `D(X_ét, Λ)` in a given cohomological degree descends along a
jointly surjective family of morphisms. -/
theorem isZero_homology_of_jointlySurjective
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (h : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((L((u i)^*[ModuleCat.{u + 1} Λ])).obj M))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj M) :=
  isZero_of_isZero_upperStar_obj_of_jointlySurjective Λ u hu _ fun i ↦ (h i).of_iso
    ((((u i)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app M ≪≫
      (_root_.DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ (u i)).app M).symm)

end Descent

section LocalSystem

variable {Λ}

/-- The étale cover of `X` given by a jointly surjective family of étale morphisms. -/
def etaleCoverOfJointlySurjective {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ X) [∀ i, _root_.AlgebraicGeometry.Etale (u i)]
    (hu : ∀ x : X, ∃ (i : ι) (y : U i), (u i).base y = x) : Cover.{u} etalePrecoverage X where
  I₀ := ι
  X := U
  f := u
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    obtain ⟨i, y, hy⟩ := hu x
    exact ⟨i, y, hy⟩

/-- An object `M ∈ D(X_ét, Λ)` is a *shifted rank-one local system* in degree `-n` if
`M ≅ L[n]` for a locally constant sheaf `L` of `Λ`-modules placed in degree zero, whose stalk at
every geometric point is free of rank one. This is the shape of the dualizing complex of a smooth
morphism of relative dimension `d`, with `n = 2d` (blueprint
`proposition-exceptional-inverse-image-smooth-morphism`). -/
def IsShiftedRankOneLocalSystem {X : Scheme.{u}}
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    Prop :=
  ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
    Nonempty (M ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦n⟧)

namespace IsShiftedRankOneLocalSystem

variable {X Y : Scheme.{u}}
  {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {n : ℤ}

lemma of_iso (e : M ≅ M') (h : IsShiftedRankOneLocalSystem M n) :
    IsShiftedRankOneLocalSystem M' n := by
  obtain ⟨L, hL, hs, ⟨e'⟩⟩ := h
  exact ⟨L, hL, hs, ⟨e.symm ≪≫ e'⟩⟩

/-- A shifted rank-one local system is ⊗-invertible. -/
lemma isInvertible (h : IsShiftedRankOneLocalSystem M n) :
    DerivedCategory.isInvertible Λ X M := by
  obtain ⟨L, hL, hs, ⟨e⟩⟩ := h
  exact DerivedCategory.isInvertible.of_iso e.symm
    (isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf L hs n)

/-- The derived pullback of `L[n]` is `(g^* L)[n]`. -/
noncomputable def leftDerivedUpperStarShiftSingleIso (g : Y ⟶ X)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℤ) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj (((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦n⟧) ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (((g)^*[ModuleCat.{u + 1} Λ]).obj L))⟦n⟧ :=
  ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) g).app L)

/-- A shifted rank-one local system pulls back to a shifted rank-one local system. -/
lemma leftDerivedUpperStar (g : Y ⟶ X) (h : IsShiftedRankOneLocalSystem M n) :
    IsShiftedRankOneLocalSystem ((L((g)^*[ModuleCat.{u + 1} Λ])).obj M) n := by
  obtain ⟨L, hL, hs, ⟨e⟩⟩ := h
  refine ⟨((g)^*[ModuleCat.{u + 1} Λ]).obj L, IsLocallyConstantSheaf.upperStar g L,
    fun Ω _ _ s ↦ ⟨((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g s).app L) ≪≫
      (hs Ω (s ≫ g)).some⟩,
    ⟨(L((g)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫ leftDerivedUpperStarShiftSingleIso g L n⟩⟩

/-- Shifted rank-one local systems descend along jointly surjective families of étale
morphisms: the cohomology sheaves of `M` outside degree `-n` vanish after pullback, hence vanish,
so `M ≅ L[n]` for a sheaf `L`; the pullbacks of `L` are locally constant with free rank-one
stalks, hence so is `L`. -/
theorem of_jointlySurjective {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X)
    [∀ i, _root_.AlgebraicGeometry.Etale (u i)]
    (hu : ∀ x : X, ∃ (i : ι) (y : U i), (u i).base y = x)
    (h : ∀ i, IsShiftedRankOneLocalSystem ((L((u i)^*[ModuleCat.{u + 1} Λ])).obj M) n) :
    IsShiftedRankOneLocalSystem M n := by
  choose L hL hs e using h
  -- the pullbacks are concentrated in degree `-n`
  let e' (i : ι) : (L((u i)^*[ModuleCat.{u + 1} Λ])).obj M ≅
      (_root_.DerivedCategory.singleFunctor _ (-n)).obj (L i) :=
    (e i).some ≪≫ ((_root_.DerivedCategory.singleFunctors _).shiftIso n (-n) 0
      (add_neg_cancel n)).app (L i)
  have hz (k : ℤ) (hk : k ≠ -n) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ k).obj M) := by
    refine isZero_homology_of_jointlySurjective Λ u hu M k fun i ↦ ?_
    refine IsZero.of_iso ?_ ((_root_.DerivedCategory.homologyFunctor _ k).mapIso (e' i))
    rcases lt_or_gt_of_ne hk with hk | hk
    · exact _root_.DerivedCategory.isZero_of_isGE _ (-n) k hk
    · exact _root_.DerivedCategory.isZero_of_isLE _ (-n) k hk
  have : M.IsGE (-n) := by
    rw [_root_.DerivedCategory.isGE_iff]
    exact fun k hk ↦ hz k hk.ne
  have : M.IsLE (-n) := by
    rw [_root_.DerivedCategory.isLE_iff]
    exact fun k hk ↦ hz k hk.ne'
  obtain ⟨F, ⟨eF⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M (-n)
  let eF' : M ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj F)⟦n⟧ :=
    eF ≪≫ (((_root_.DerivedCategory.singleFunctors _).shiftIso n (-n) 0
      (add_neg_cancel n)).app F).symm
  -- the pullbacks of `F` are the `L i`
  let φ (i : ι) : ((u i)^*[ModuleCat.{u + 1} Λ]).obj F ≅ L i :=
    (_root_.DerivedCategory.singleFunctor _ 0).preimageIso
      ((shiftFunctor _ n).preimageIso
        ((leftDerivedUpperStarShiftSingleIso (u i) F n).symm ≪≫
          (L((u i)^*[ModuleCat.{u + 1} Λ])).mapIso eF'.symm ≪≫ (e i).some))
  have : ∀ i, IsLocallyConstantSheaf (Etale.upperStar (ModuleCat.{u + 1} Λ)
      ((etaleCoverOfJointlySurjective u hu).f i) |>.obj F) := fun i ↦
    have := hL i
    IsLocallyConstantSheaf.of_iso (φ i).symm
  refine ⟨F, IsLocallyConstantSheaf.of_cover (etaleCoverOfJointlySurjective u hu) F,
    fun Ω _ _ s ↦ ?_, ⟨eF'⟩⟩
  obtain ⟨i, y, hy⟩ := hu (s.base (IsLocalRing.closedPoint _))
  obtain ⟨s', rfl⟩ := Scheme.exists_comp_eq_of_etale (u i) s ⟨y, hy⟩
  exact ⟨((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (u i) s').app F).symm ≪≫
    (pointSmallEtale s').sheafFiber.mapIso (φ i) ≪≫ (hs i Ω s').some⟩

end IsShiftedRankOneLocalSystem

end LocalSystem

section Composition

variable [Finite Λ] {X Y Z : Scheme.{u}}

/-- The dualizing complex of a composite `h = a ≫ b`: if `θ_a` is invertible at `ω_b`, then
`ω_h ≅ Ra^! ω_b ≅ ω_a ⊗ᴸ La^* ω_b`, by the composition law for the exceptional inverse image
(`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`). -/
theorem nonempty_dualizingComplex_comp_iso_of_isIso (a : X ⟶ Y) (b : Y ⟶ Z) (h : X ⟶ Z)
    (w : a ≫ b = h) [HasCompactification a] [HasCompactification b] [HasCompactification h]
    (ha : IsIso (dualizingComplexTensorMap Λ a (dualizingComplex Λ b))) :
    Nonempty (dualizingComplex Λ h ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex Λ a)).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ b))) := by
  obtain ⟨E, -, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  exact ⟨(Adjunction.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction _ h).ofNatIsoLeft (E a b h w))
    ((rightDerivedUpperShriekAdjunction _ a).comp
      (rightDerivedUpperShriekAdjunction _ b))).app (𝟙_ _) ≪≫
    (@asIso _ _ _ _ (dualizingComplexTensorMap Λ a _) ha).symm⟩

/-- The dualizing complex of a composite `h = a ≫ b` with `ω_a` trivial: if `θ_a` is invertible
at `ω_b` and `ω_a ≅ Λ_X`, then `ω_h ≅ La^* ω_b`. -/
theorem nonempty_dualizingComplex_comp_iso_leftDerivedUpperStar (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : X ⟶ Z) (w : a ≫ b = h) [HasCompactification a] [HasCompactification b]
    [HasCompactification h]
    (ha : IsIso (dualizingComplexTensorMap Λ a (dualizingComplex Λ b)))
    (hωa : Nonempty (dualizingComplex Λ a ≅ 𝟙_ _)) :
    Nonempty (dualizingComplex Λ h ≅
      (L((a)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ b)) := by
  obtain ⟨e⟩ := nonempty_dualizingComplex_comp_iso_of_isIso Λ a b h w ha
  obtain ⟨e'⟩ := hωa
  exact ⟨e ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e').app _ ≪≫
    derivedTensorLeftUnitor _ X _⟩

/-- The dualizing complex of a composite `h = a ≫ b` with `ω_b` trivial: if `θ_a` is invertible
at `ω_b` and `ω_b ≅ Λ_Y`, then `ω_h ≅ ω_a`. -/
theorem nonempty_dualizingComplex_comp_iso_of_unit (a : X ⟶ Y) (b : Y ⟶ Z) (h : X ⟶ Z)
    (w : a ≫ b = h) [HasCompactification a] [HasCompactification b] [HasCompactification h]
    (ha : IsIso (dualizingComplexTensorMap Λ a (dualizingComplex Λ b)))
    (hωb : Nonempty (dualizingComplex Λ b ≅ 𝟙_ _)) :
    Nonempty (dualizingComplex Λ h ≅
      dualizingComplex Λ a) := by
  obtain ⟨e⟩ := nonempty_dualizingComplex_comp_iso_of_isIso Λ a b h w ha
  obtain ⟨e'⟩ := hωb
  exact ⟨e ≪≫ ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).mapIso
    ((L((a)^*[ModuleCat.{u + 1} Λ])).mapIso e' ≪≫ leftDerivedUpperStarUnitIso _ a) ≪≫
    derivedTensorRightUnitor _ X _⟩

/-- **Composition of the canonical tensor maps.** For `h = a ≫ b` admitting compactifications:
if `θ_a` is invertible at every object, `ω_b` is invertible and `θ_b` is invertible at `K`, then
`θ_h` is invertible at `K` (`lem-pur-co-smooth-composition`, for all coefficients `K`). -/
theorem isIso_dualizingComplexTensorMap_comp_of_forall (a : X ⟶ Y) (b : Y ⟶ Z) (h : X ⟶ Z)
    (w : a ≫ b = h) [HasCompactification a] [HasCompactification b] [HasCompactification h]
    (ha : ∀ P, IsIso (dualizingComplexTensorMap Λ a P))
    (hω : DerivedCategory.isInvertible Λ Y (dualizingComplex Λ b))
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hb : IsIso (dualizingComplexTensorMap Λ b K)) :
    IsIso (dualizingComplexTensorMap Λ h K) := by
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  exact isIso_lowerShriekRightAdjointUnitTensorMap_comp w (rightDerivedUpperShriekAdjunction Λ a)
    (rightDerivedUpperShriekAdjunction Λ b) (rightDerivedUpperShriekAdjunction Λ h) (E a b h w)
    (hPF a b h w) (projectionMapAssociativity Λ a) K (ha _) hb
    ((isInvertible_iff_exists_derivedTensor _).2 hω)

/-- **Descent of the canonical tensor maps.** Let `u_i : U_i ⟶ X` be a jointly surjective family
of étale morphisms with `θ_{u_i}` invertible at every object and `ω_{u_i}` invertible, and let
`f : X ⟶ Y`. If every `θ_{u_i ≫ f, K}` is invertible, then so is `θ_{f, K}`: through the
composition law `θ_{u_i ≫ f, K}` determines `Ru_i^! θ_{f, K}`, hence `Lu_i^* θ_{f, K}`, and
isomorphisms descend along the family. -/
theorem isIso_dualizingComplexTensorMap_of_jointlySurjective {ι : Type u} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ X) [∀ i, _root_.AlgebraicGeometry.Etale (u i)]
    (hu : ∀ x : X, ∃ (i : ι) (y : U i), (u i).base y = x) [∀ i, HasCompactification (u i)]
    (f : X ⟶ Y) [HasCompactification f] [∀ i, HasCompactification (u i ≫ f)]
    (hθ : ∀ i P, IsIso (dualizingComplexTensorMap Λ (u i) P))
    (hω : ∀ i, DerivedCategory.isInvertible Λ (U i) (dualizingComplex Λ (u i)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ i, IsIso (dualizingComplexTensorMap Λ (u i ≫ f) K)) :
    IsIso (dualizingComplexTensorMap Λ f K) := by
  obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ u hu _ fun i ↦ ?_
  exact isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
    (rightDerivedUpperShriekAdjunction Λ (u i)) (hθ i)
    ((isInvertible_iff_exists_derivedTensor _).2 (hω i)) _
    (isIso_map_lowerShriekRightAdjointUnitTensorMap_of_comp rfl
      (rightDerivedUpperShriekAdjunction Λ (u i)) (rightDerivedUpperShriekAdjunction Λ f)
      (rightDerivedUpperShriekAdjunction Λ (u i ≫ f)) (E (u i) f _ rfl) (hPF (u i) f _ rfl)
      (projectionMapAssociativity Λ (u i)) (hθ i) K (hK i))

end Composition

end Etale

end AlgebraicGeometry
