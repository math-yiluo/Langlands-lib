/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageAlgebra

/-!
# Change of the base of a system of stages, and maps of elementwise colimits

For `b : B' ⟶ B` and a stage `(T, S, g, π, w)` over `B`, the stage `(T, S, g, b ≫ π, w)` over `B'`
computes the pullback along `b` (`AlgebraicGeometry.Etale.LimitStage.comapBIso`), compatibly with
the transition maps; consequently stalkwise colimit systems are stable under change of base
(`AlgebraicGeometry.Etale.LimitStageSystem.isStalkColimit_comapB`).

A map of elementwise colimit systems which is bijective at every stage is bijective at the
colimit (`ModuleCat.IsElementwiseColimit.bijective_of_bijective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace ModuleCat.IsElementwiseColimit

variable {R : Type*} [Ring R] {I : Type*} [Category I]

/-- A map between two elementwise colimit systems over the same index category, compatible with
the structure maps and bijective at every stage, is bijective at the colimit. -/
lemma bijective_of_bijective {A A' : I → ModuleCat R} {B B' : ModuleCat R}
    {σ : ∀ i, A i ⟶ B} {σ' : ∀ i, A' i ⟶ B'} {τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)}
    {τ' : ∀ {i j : I}, (i ⟶ j) → (A' j ⟶ A' i)} (φ : ∀ i, A i ⟶ A' i) (φB : B ⟶ B')
    (hσ : ∀ i, φ i ≫ σ' i = σ i ≫ φB) (hτ : ∀ {i j : I} (f : i ⟶ j), τ f ≫ φ i = φ j ≫ τ' f)
    (hστ : ∀ {i j : I} (f : i ⟶ j), τ f ≫ σ i = σ j)
    (hφ : ∀ i, Function.Bijective (φ i).hom) (h : IsElementwiseColimit A B σ τ)
    (h' : IsElementwiseColimit A' B' σ' τ') : Function.Bijective φB.hom := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun b' ↦ ?_⟩
  · obtain ⟨i, a, rfl⟩ := h.1 b
    have h0 : (σ' i).hom ((φ i).hom a) = 0 := by rw [← ModuleCat.comp_apply, hσ]; exact hb
    obtain ⟨j, f, hf⟩ := h'.2 i _ h0
    have h1 : (φ j).hom ((τ f).hom a) = 0 := by rw [← ModuleCat.comp_apply, hτ]; exact hf
    have h2 : (τ f).hom a = 0 := (hφ j).1 (by rw [h1, map_zero])
    rw [← hστ f, ModuleCat.comp_apply, h2, map_zero]
  · obtain ⟨i, a', rfl⟩ := h'.1 b'
    obtain ⟨a, rfl⟩ := (hφ i).2 a'
    exact ⟨(σ i).hom a, by rw [← ModuleCat.comp_apply, ← hσ]; rfl⟩

end ModuleCat.IsElementwiseColimit

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace LimitStage

variable {B B' W : Scheme.{u}} (b : B' ⟶ B)

/-- Change of base: the stage `(T, S, g, b ≫ π, w)` over `B'`. -/
abbrev comapB (α : LimitStage B W) : LimitStage B' W := ⟨α.T, α.S, α.g, b ≫ α.π, α.w⟩

/-- Change of base for morphisms of stages. -/
abbrev Hom.comapB {α β : LimitStage B W} (φ : Hom α β) : Hom (α.comapB b) (β.comapB b) :=
  ⟨φ.t, φ.s, φ.wg, by rw [Category.assoc, φ.wπ], φ.ww⟩

/-- `b^* π^* Rg_* w^* K ≅ (b ≫ π)^* Rg_* w^* K`. -/
noncomputable def comapBIso (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((b)^*[ModuleCat.{u + 1} Λ]).obj ((functor Λ α).obj K) ≅ (functor Λ (α.comapB b)).obj K :=
  ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b α.π (b ≫ α.π) rfl).app
    (R+((α.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((α.w)^*[ModuleCat.{u + 1} Λ]).obj K))).symm

lemma transition_comapB {α β : LimitStage B W} (φ : Hom α β)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((b)^*[ModuleCat.{u + 1} Λ]).map ((transition Λ φ).app K) ≫ (comapBIso Λ b α K).hom =
      (comapBIso Λ b β K).hom ≫ (transition Λ (φ.comapB b)).app K := by
  have hA := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    b α.π φ.s (b ≫ α.π) β.π (b ≫ β.π) rfl φ.wπ.symm (by rw [Category.assoc, φ.wπ]))
    (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hA
  have hA' : D+((b)^*[ModuleCat.{u + 1} Λ]).map
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) α.π φ.s β.π φ.wπ.symm).hom.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))) ≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b α.π (b ≫ α.π) rfl).inv.app
        (D+((φ.s)^*[ModuleCat.{u + 1} Λ]).obj
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))) =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b β.π (b ≫ β.π) rfl).inv.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)) ≫
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (b ≫ α.π) φ.s (b ≫ β.π)
          (φ.comapB b).wπ.symm).hom.app
          (R+((β.g)_*[ModuleCat.{u + 1} Λ]).obj (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
    rw [← cancel_epi ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b β.π (b ≫ β.π)
      rfl).hom.app _), Iso.hom_inv_id_app_assoc, reassoc_of% hA, Iso.hom_inv_id_app,
      Category.comp_id]
  have n := (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) b α.π (b ≫ α.π) rfl).inv.naturality
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((α.g)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.t β.w α.w φ.ww.symm).inv.app K))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at n
  simp only [transition_app, comapBIso, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [n]
  simp only [Functor.comp_obj]
  rw [reassoc_of% hA']

end LimitStage

namespace LimitStageSystem

variable {B B' W : Scheme.{u}} {I : Type u} [Category.{u} I] (b : B' ⟶ B)

/-- Change of base of a system of stages along `b : B' ⟶ B`. -/
@[simps]
def comapB (𝒮 : LimitStageSystem B W I) : LimitStageSystem B' W I where
  obj i := (𝒮.obj i).comapB b
  map f := (𝒮.map f).comapB b
  map_id i := LimitStage.Hom.ext (by rw [𝒮.map_id]) (by rw [𝒮.map_id])
  map_comp f g := LimitStage.Hom.ext (by rw [𝒮.map_comp]) (by rw [𝒮.map_comp])
  pt := 𝒮.pt.comapB b
  π i := (𝒮.π i).comapB b
  w f := LimitStage.Hom.ext (by rw [← 𝒮.w f]) (by rw [← 𝒮.w f])

variable {Λ}

/-- Stalkwise colimit systems are stable under change of base. -/
lemma isStalkColimit_comapB [IsCofiltered I] (𝒮 : LimitStageSystem B W I)
    {K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {q : ℤ}
    (h : 𝒮.IsStalkColimit Λ K q) : (𝒮.comapB b).IsStalkColimit Λ K q := by
  have hcol := isColimitOfPreserves ((b)^*[ModuleCat.{u + 1} Λ]) (𝒮.isColimitOfIsStalkColimit Λ h)
  intro x
  let e (α : LimitStage B W) :=
    (((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).app
      ((LimitStage.functor Λ α).obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso (LimitStage.comapBIso Λ b α K)
  have he {α β : LimitStage B W} (φ : LimitStage.Hom α β) :
      ((b)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ φ).app K)) ≫ (e α).hom =
      (e β).hom ≫ (DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ (φ.comapB b)).app K) := by
    have n :=
      (((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.naturality
      ((LimitStage.transition Λ φ).app K)
    simp only [Functor.comp_map] at n
    simp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
      LimitStage.functor_obj]
    rw [reassoc_of% n, ← Functor.map_comp, LimitStage.transition_comapB, Functor.map_comp]
  have he' {α β : LimitStage B W} (φ : LimitStage.Hom α β) :
      (e β).inv ≫ ((b)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ φ).app K)) =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        ((LimitStage.transition Λ (φ.comapB b)).app K) ≫ (e α).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ ((B'.uliftPointSmallEtale x).sheafFiber.mapIso (e (𝒮.obj i))).symm)
    ((B'.uliftPointSmallEtale x).sheafFiber.mapIso (e 𝒮.pt)).symm (fun i ↦ ?_) (fun f ↦ ?_)
    (isElementwiseColimit_sheafFiber_of_isColimit hcol x)
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Functor.mapCocone_ι_app, cocone_ι_app,
      stalkHomology, Functor.comp_map, ← Functor.map_comp]
    exact congrArg (B'.uliftPointSmallEtale x).sheafFiber.map (he' (𝒮.π i))
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Functor.comp_map, diagram_map,
      Quiver.Hom.unop_op, stalkHomology, ← Functor.map_comp]
    exact congrArg (B'.uliftPointSmallEtale x).sheafFiber.map (he' (𝒮.map f))

end LimitStageSystem

lemma _root_.CategoryTheory.isIso_of_isIso_comp_comp {C : Type*} [Category C] {X Y Z T : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T) [IsIso a] [IsIso c] (h : IsIso (a ≫ b ≫ c)) :
    IsIso b := by
  have : b = inv a ≫ (a ≫ b ≫ c) ≫ inv c := by simp
  rw [this]
  infer_instance

namespace LimitStage

variable {B W : Scheme.{u}}

lemma isIso_homology_upperStar_map_iff {X Y : Scheme.{u}} (π : X ⟶ Y) (q : ℤ)
    {L L' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : L ⟶ L') :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map (D+((π)^*[ModuleCat.{u + 1} Λ]).map f)) ↔
      IsIso (((π)^*[ModuleCat.{u + 1} Λ]).map ((DerivedCategory.Plus.homologyFunctor _ q).map f)) :=
  (NatIso.isIso_map_iff (((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q)
    f).symm

/-- The transition map of a morphism of stages is an isomorphism in degree `q` as soon as the
derived base-change map of its square is. -/
lemma isIso_homology_transition_of_isIso {α β : LimitStage B W} (φ : Hom α β) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
        (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map ((transition Λ φ).app K)) := by
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map (D+((α.π)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
        (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)))) :=
    (isIso_homology_upperStar_map_iff Λ α.π q _).2 inferInstance
  rw [transition_app, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Conversely, for a stage with `π = 𝟙`, an isomorphism in degree `q` of the transition map
forces one of the derived base-change map of its square. -/
lemma isIso_homology_baseChange_of_isIso {S T W' : Scheme.{u}} {g : T ⟶ S} {w : T ⟶ W'}
    {β : LimitStage S W'} (φ : Hom ⟨T, S, g, 𝟙 S, w⟩ β) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf W'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map ((transition Λ φ).app K))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
        (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K))) := by
  rw [transition_app, Functor.map_comp, Functor.map_comp, Functor.map_comp] at h
  have h2 := isIso_of_isIso_comp_comp _ _ _ h
  have h3 := (isIso_homology_upperStar_map_iff Λ (𝟙 S) q _).1 h2
  have n := (Etale.upperStarId (ModuleCat.{u + 1} Λ) S).hom.naturality
    ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) ⟨φ.wg⟩).app
        (D+((β.w)^*[ModuleCat.{u + 1} Λ]).obj K)))
  exact (NatIso.isIso_map_iff (Etale.upperStarId (ModuleCat.{u + 1} Λ) S) _).1 h3

end LimitStage

/-- The degree-`q` base-change map at a pulled back sheaf `w^* G` is an isomorphism if and only
if the degree-`q` homology of the derived base-change map at the derived pullback `w^*(G[0])`
is. -/
lemma isIso_baseChangeHomologyMap_iff_upperStar {X S T Y : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ) {W : Scheme.{u}}
    (w : T ⟶ W) (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q (((w)^*[ModuleCat.{u + 1} Λ]).obj G)) ↔
      IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          (D+((w)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :=
    by
  let ι := (((w)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G
  have n : (DerivedCategory.Plus.homologyFunctor _ q).map (D+((p)^*[ModuleCat.{u + 1} Λ]).map
        (R+((g)_*[ModuleCat.{u + 1} Λ]).map ι.hom)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (((w)^*[ModuleCat.{u + 1} Λ]).obj G))) =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          (D+((w)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map ι.hom)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).naturality ι.hom)
  change IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((w)^*[ModuleCat.{u + 1} Λ]).obj G)))) ↔ _
  constructor
  · intro _
    have : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          (D+((w)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map ι.hom))) := by
      rw [← n]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.homologyFunctor _ q).map
      (R+((h)_*[ModuleCat.{u + 1} Λ]).map (D+((e)^*[ModuleCat.{u + 1} Λ]).map ι.hom)))
  · intro _
    have : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map (D+((p)^*[ModuleCat.{u + 1} Λ]).map
        (R+((g)_*[ModuleCat.{u + 1} Λ]).map ι.hom)) ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (((w)^*[ModuleCat.{u + 1} Λ]).obj G)))) :=
    by
      rw [n]
      infer_instance
    exact IsIso.of_isIso_comp_left ((DerivedCategory.Plus.homologyFunctor _ q).map
      (D+((p)^*[ModuleCat.{u + 1} Λ]).map (R+((g)_*[ModuleCat.{u + 1} Λ]).map ι.hom))) _

end AlgebraicGeometry.Etale
