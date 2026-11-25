/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic
public import WeilConjectures.TraceFormula.Specialization.FiniteSupportConservative
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal

/-!

# Base change of dualizing complexes: global sections and finite schemes

Inputs for the invertibility of the comparison `φ : π^* ω_X ⟶ ω_{X_L}` of dualizing complexes
along a change of base field (`ProEtale.CondensedRing.dualizingComplexBaseChange`):

* the duality map `F RHom(𝟙, ω) ⟶ RHom(F 𝟙, ω')` of a lax monoidal functor `F` with dualizing map
  `θ : F ω ⟶ ω'` is `θ` up to isomorphisms
  (`CategoryTheory.Verdier.map_unitNatIso_hom_app_comp_nearbyDualityMap_comp_pre`);
* the derived pushforward along a finite morphism reflects isomorphisms of bounded constructible
  complexes (`ProEtale.CondensedRing.isIso_of_isIso_map_boundedConstructibleLowerStar_of_isFinite`);
* the pullback along a morphism of points is monoidal between rigid categories, so it commutes
  with duals (`ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_point`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### The duality map at the unit -/

namespace CategoryTheory.Verdier

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']

/-- The tensor–Hom adjoint of the identification `X ≅ RHom(𝟙, X)` is the left unitor. -/
lemma uncurry_unitNatIso_hom_app' (X : C) :
    uncurry (unitNatIso.hom.app X) = (λ_ X).hom := by
  rw [uncurry_eq]
  have := conjugateEquiv_counit (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  simpa [unitNatIso] using this

/-- **The duality map at the unit is the dualizing map**: for a lax monoidal functor `F` and
`θ : F ω ⟶ ω'`, the duality map `F RHom(𝟙, ω) ⟶ RHom(F 𝟙, ω')`, read through `ω ≅ RHom(𝟙, ω)`,
`RHom(F 𝟙, ω') ⟶ RHom(𝟙, ω')` (precomposition with the unit map of `F`) and
`ω' ≅ RHom(𝟙, ω')`, is `θ`. -/
lemma map_unitNatIso_hom_app_comp_nearbyDualityMap_comp_pre (F : C ⥤ C') [F.LaxMonoidal]
    {ω : C} {ω' : C'} (θ : F.obj ω ⟶ ω') :
    F.map (unitNatIso.hom.app ω) ≫
        nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B) θ (𝟙_ C) ≫
          (pre (Functor.LaxMonoidal.ε F)).app ω' =
      θ ≫ unitNatIso.hom.app ω' := by
  apply uncurry_injective
  rw [← Category.assoc, uncurry_pre_app, uncurry_natural_left, uncurry_nearbyDualityMap,
    uncurry_natural_left, uncurry_unitNatIso_hom_app']
  have h₁ := Functor.LaxMonoidal.μ_natural_right F (𝟙_ C) (unitNatIso.hom.app ω)
  have h₂ : 𝟙_ C ◁ unitNatIso.hom.app ω ≫ (ihom.ev (𝟙_ C)).app ω = (λ_ ω).hom := by
    rw [← uncurry_eq, uncurry_unitNatIso_hom_app']
  rw [reassoc_of% h₁, ← F.map_comp_assoc, h₂]
  dsimp only [Functor.id_obj]
  rw [← Functor.LaxMonoidal.left_unitality_assoc]
  simp

/-- The precomposition `RHom(A, -) ⟶ RHom(B, -)` with an isomorphism `B ⟶ A` is invertible. -/
lemma isIso_pre_app_of_isIso {A B : C} (f : B ⟶ A) [IsIso f] (Z : C) : IsIso ((pre f).app Z) :=
  ⟨(pre (inv f)).app Z, by rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id, pre_id,
    NatTrans.id_app], by rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id,
    NatTrans.id_app]⟩

/-- If the duality map at the unit of a lax monoidal functor with invertible unit map is
invertible, so is the dualizing map. -/
lemma isIso_of_isIso_nearbyDualityMap_unit (F : C ⥤ C') [F.LaxMonoidal]
    [IsIso (Functor.LaxMonoidal.ε F)] {ω : C} {ω' : C'} (θ : F.obj ω ⟶ ω')
    (h : IsIso (nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B) θ (𝟙_ C))) :
    IsIso θ := by
  have := isIso_pre_app_of_isIso (Functor.LaxMonoidal.ε F) ω'
  have e := map_unitNatIso_hom_app_comp_nearbyDualityMap_comp_pre F θ
  have : IsIso (θ ≫ unitNatIso.hom.app ω') := by
    rw [← e]
    infer_instance
  exact IsIso.of_isIso_comp_right θ (unitNatIso.hom.app ω')

/-- For a functor `G` and a lax monoidal functor `F` with invertible unit map, if `G` inverts the
duality map at the unit, it inverts the dualizing map. -/
lemma isIso_map_of_isIso_map_nearbyDualityMap_unit {D : Type*} [Category* D] (G : C' ⥤ D)
    (F : C ⥤ C') [F.LaxMonoidal] [IsIso (Functor.LaxMonoidal.ε F)] {ω : C} {ω' : C'}
    (θ : F.obj ω ⟶ ω')
    (h : IsIso (G.map (nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B) θ (𝟙_ C)))) :
    IsIso (G.map θ) := by
  have := isIso_pre_app_of_isIso (Functor.LaxMonoidal.ε F) ω'
  have e := G.congr_map (map_unitNatIso_hom_app_comp_nearbyDualityMap_comp_pre F θ)
  simp only [Functor.map_comp] at e
  have : IsIso (G.map θ ≫ G.map (unitNatIso.hom.app ω')) := by
    rw [← e]
    infer_instance
  exact IsIso.of_isIso_comp_right (G.map θ) (G.map (unitNatIso.hom.app ω'))

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-! ### Finite pushforward is conservative -/

section Conservative

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Finite pushforward is conservative on bounded constructible complexes**: for a finite
morphism `q : Y ⟶ B`, a morphism `f` of bounded constructible complexes on `Y` with `Rq_* f`
invertible is invertible. Its cone is bounded constructible with vanishing pushforward, hence
vanishes (`ProEtale.CondensedRing.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`). -/
theorem isIso_of_isIso_map_boundedConstructibleLowerStar_of_isFinite {Y B : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (q : Y ⟶ B)
    [IsFinite q.left] {K L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K ⟶ L)
    (h : IsIso ((boundedConstructibleLowerStar ℓ q).map f)) : IsIso f := by
  have : (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).IsTriangulated :=
    isTriangulated_boundedConstructible_padicAlgClRingObj _ ℓ
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle f.hom
  have hC := (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT K.property L.property
  have h' : IsIso ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map f.hom) :=
    inferInstanceAs (IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleLowerStar ℓ q).map f)))
  have hq : IsZero ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_distinguished _ hT)).2 h'
  have : IsFinite (𝟙 Y.left ≫ q.left) := by
    rw [Category.id_comp]
    infer_instance
  have hZ := isZero_of_isZero_rightDerivedLowerStar_of_isFinite q (𝟙 Y.left) ⟨C, hC⟩
    (fun y hy ↦ absurd ⟨y, rfl⟩ hy) hq
  have : IsIso f.hom := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ
  have : IsIso ((boundedConstructible _).ι.map f) := this
  exact isIso_of_reflects_iso f (boundedConstructible _).ι

end Conservative

/-! ### Pullback between points commutes with duals -/

section Point

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]

/-- **Pullback between points commutes with duals**: for `πₛ : Spec k₂ ⟶ Spec k₁` and an
isomorphism `e : πₛ^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, the duality map `πₛ^* RHom(N, ℚ̄_ℓ) ⟶ RHom(πₛ^* N, ℚ̄_ℓ)` of the
monoidal functor `πₛ^*` with dualizing map `e` is invertible: every `N` is dualizable
(`ProEtale.CondensedRing.nonempty_hasLeftDual_point`) and monoidal functors commute with duals
(`CategoryTheory.Verdier.isIso_nearbyDualityMap_of_monoidal`). -/
theorem isIso_nearbyDualityMap_upperStarOfMap_point (πₛ : Spec (.of k₂) ⟶ Spec (.of k₁))
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] (N : Dᵇc((point k₁).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ) A B) e N) := by
  obtain ⟨hN⟩ := nonempty_hasLeftDual_point ℓ (k := k₁) N
  have h := Verdier.isIso_nearbyDualityMap_of_monoidal
    (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ) (ᘁN) N
  have e₂ : e = Functor.OplaxMonoidal.η
      (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ) ≫
        (Functor.LaxMonoidal.ε
          (boundedConstructibleUpperStarOfMap ℓ (X := point k₁) (Y := point k₂) πₛ) ≫ e) := by
    rw [Functor.Monoidal.η_ε_assoc]
  rw [e₂, ← Verdier.nearbyDualityMap_comp_ihom_map]
  infer_instance

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
