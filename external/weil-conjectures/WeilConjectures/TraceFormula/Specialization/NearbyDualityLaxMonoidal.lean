/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
public import WeilConjectures.TraceFormula.FieldDualizable
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal

/-!

# Nearby duality and global sections: lax monoidal structures

Inputs for `TraceFormula.Specialization.NearbyDualityGlobal`:

* the lax tensor maps of a right adjoint are adjoint to the tensor product of the counits
  (`CategoryTheory.Verdier.map_rightAdjointLaxMonoidal_μ_comp_counit`), and the duality map of a
  right adjoint read through an exceptional adjunction is the Verdier exchange morphism
  (`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`);
* the abstract proper identity for the duality map
  (`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper'`);
* the duality map of a monoidal functor between rigid categories is invertible
  (`CategoryTheory.Verdier.isIso_nearbyDualityMap_of_monoidal`);
* the restriction of a lax monoidal functor to full monoidal subcategories
  (`CategoryTheory.ObjectProperty.laxMonoidalLift`);
* the lax monoidal structure of `Rf_*` on bounded constructible complexes, the right adjoint of
  the monoidal functor `Lf^*` (`ProEtale.CondensedRing.boundedConstructibleLowerStarLaxMonoidal`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemmas -/

namespace CategoryTheory

namespace Verdier

section Abstract

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]

/-- The lax tensor map of the right adjoint `G` of an oplax monoidal functor `F` is adjoint to the
tensor product of the counits. -/
lemma map_rightAdjointLaxMonoidal_μ_comp_counit {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    [F.OplaxMonoidal] (A B : C) :
    F.map (letI := adj.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ G A B) ≫
        adj.counit.app (A ⊗ B) =
      Functor.OplaxMonoidal.δ F _ _ ≫ (adj.counit.app A ⊗ₘ adj.counit.app B) := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ]
  exact (adj.homEquiv_counit (g := _)).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)

/-- The compatibility of a pushforward exchange `χ : Rg ⋙ Ψ₁ ⟶ Ψ ⋙ Rg'` with the lax tensor maps
of `Ψ`, `Ψ₁` and of the right adjoints `Rg`, `Rg'`, in abstract categories: the Künneth
computation `ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux` for the diagonal,
from the monoidality of the pullback exchange `α : Ψ₁ ⋙ g' ⟶ g ⋙ Ψ` whose mate is `χ`. -/
lemma pushforwardExchange_tensor_aux {DX DX1 SX SX1 : Type*} [Category* DX] [Category* DX1]
    [Category* SX] [Category* SX1] [MonoidalCategory DX] [MonoidalCategory DX1]
    [MonoidalCategory SX] [MonoidalCategory SX1] {Ψ : DX ⥤ SX} {Ψ₁ : DX1 ⥤ SX1}
    {g : DX1 ⥤ DX} {g' : SX1 ⥤ SX} {Rg : DX ⥤ DX1} {Rg' : SX ⥤ SX1}
    [g.OplaxMonoidal] [g'.OplaxMonoidal] (ag : g ⊣ Rg) (ag' : g' ⊣ Rg')
    (μ : ∀ U V, Ψ.obj U ⊗ Ψ.obj V ⟶ Ψ.obj (U ⊗ V))
    (μ₁ : ∀ U V, Ψ₁.obj U ⊗ Ψ₁.obj V ⟶ Ψ₁.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : DX} (x : U ⟶ U') (y : V ⟶ V'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ U' V' = μ U V ≫ Ψ.map (x ⊗ₘ y))
    (α : Ψ₁ ⋙ g' ⟶ g ⋙ Ψ) (χ : Rg ⋙ Ψ₁ ⟶ Ψ ⋙ Rg')
    (hχ : ∀ A, g'.map (χ.app A) ≫ ag'.counit.app (Ψ.obj A) =
      α.app (Rg.obj A) ≫ Ψ.map (ag.counit.app A))
    (hα : ∀ U V, g'.map (μ₁ U V) ≫ α.app (U ⊗ V) ≫ Ψ.map (Functor.OplaxMonoidal.δ g U V) =
      Functor.OplaxMonoidal.δ g' _ _ ≫ (α.app U ⊗ₘ α.app V) ≫ μ (g.obj U) (g.obj V))
    (A B : DX) :
    (χ.app A ⊗ₘ χ.app B) ≫
        (letI := ag'.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg' _ _) ≫
          Rg'.map (μ A B) =
      μ₁ _ _ ≫ Ψ₁.map (letI := ag.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg A B) ≫
        χ.app (A ⊗ B) := by
  have h := AlgebraicGeometry.ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux
    (f₁ := 𝟭 DX) (f₂ := 𝟭 DX) (e₁ := 𝟭 DX1) (e₂ := 𝟭 DX1) (f₁' := 𝟭 SX) (f₂' := 𝟭 SX)
    (e₁' := 𝟭 SX1) (e₂' := 𝟭 SX1) ag ag ag ag' ag' ag' μ μ₁ hμ (𝟙 Ψ) (𝟙 Ψ) (𝟙 Ψ₁) (𝟙 Ψ₁)
    α α α χ χ χ hχ hχ hχ (𝟙 g) (𝟙 g) (𝟙 g') (𝟙 g') (𝟙 Rg) (𝟙 Rg) (𝟙 Rg') (𝟙 Rg')
    (fun _ ↦ by simp) (fun _ ↦ by simp) (fun _ ↦ by simp) (fun _ ↦ by simp)
    (letI := ag.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg)
    (letI := ag'.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ Rg')
    (map_rightAdjointLaxMonoidal_μ_comp_counit ag) (map_rightAdjointLaxMonoidal_μ_comp_counit ag')
    (fun _ ↦ by simp) (fun _ ↦ by simp) hα A B
  simpa using h

variable [MonoidalClosed C] [MonoidalClosed D]

/-- **Global Verdier duality as a duality map**, in abstract categories: let `F ⊣ G` (for
`Lf^* ⊣ Rf_*`, `F` oplax monoidal) and `P ⊣ S` (for `Rf_! ⊣ Rf^!`), with an isomorphism
`e : P ≅ G` and a projection morphism `pf` which is the projection morphism of the adjunction
`F ⊣ P` transported along `e`. Then the duality map of `(G, μ_G, tr)`, `μ_G` the lax structure of
the right adjoint and `tr = ε' ∘ e⁻¹ : G S L ⟶ L`, read through `e`, is the Verdier exchange
morphism `G RHom(K, S L) ⟶ RHom(P K, L)`. -/
lemma nearbyDualityMap_comp_pre_eq_exchange {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    [F.OplaxMonoidal] {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S) (e : P ≅ G)
    (pf : curriedTensorInsertFunctor₁ P ⟶
      curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)
    (hpf : ∀ (T : C) (B : D), F.map ((pf.app T).app B) ≫
        (adj.ofNatIsoRight e.symm).counit.app (T ⊗ F.obj B) =
      Functor.OplaxMonoidal.δ F (P.obj T) B ≫
        (adj.ofNatIsoRight e.symm).counit.app T ▷ F.obj B)
    (K : C) (L : D) :
    nearbyDualityMap (letI := adj.rightAdjointLaxMonoidal; Functor.LaxMonoidal.μ G)
        (e.inv.app (S.obj L) ≫ adj'.counit.app L) K ≫ (pre (e.hom.app K)).app L =
      exchange adj adj' pf K L := by
  let := adj.rightAdjointLaxMonoidal
  have hc (Z : C) : (adj.ofNatIsoRight e.symm).counit.app Z =
      F.map (e.hom.app Z) ≫ adj.counit.app Z := by
    rw [← Adjunction.homEquiv_symm_id, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
      Adjunction.homEquiv_counit]
    simp
  -- the key identity: `pf` followed by the counit is `e_K ⊗ 1` followed by `μ_G`, through `e`
  have key (B : C) : e.hom.app K ▷ G.obj B ≫ Functor.LaxMonoidal.μ G K B =
      (pf.app K).app (G.obj B) ≫ P.map (K ◁ adj.counit.app B) ≫ e.hom.app (K ⊗ B) := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, F.map_comp, Category.assoc,
      map_rightAdjointLaxMonoidal_μ_comp_counit, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
      F.map_comp, F.map_comp, Category.assoc, Category.assoc, ← hc,
      Adjunction.counit_naturality]
    erw [reassoc_of% (hpf K (G.obj B))]
    rw [hc K, comp_whiskerRight, Category.assoc]
    simp [MonoidalCategory.tensorHom_def]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_nearbyDualityMap, uncurry_exchange, exchangePairing,
    reassoc_of% (key _), ← e.hom.naturality_assoc]
  simp

end Abstract

section Proper

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']
  {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]
  {D' : Type*} [Category* D'] [MonoidalCategory D'] [MonoidalClosed D']
  {ΨX : C ⥤ C'} {ΨY : D ⥤ D'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μY : ∀ A B : D, ΨY.obj A ⊗ ΨY.obj B ⟶ ΨY.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωY : D} {ωY' : D'} (θX : ΨX.obj ωX ⟶ ωX') (θY : ΨY.obj ωY ⟶ ωY')
  {G : C ⥤ D} {G' : C' ⥤ D'} (μG : ∀ A B : C, G.obj A ⊗ G.obj B ⟶ G.obj (A ⊗ B))
  (μG' : ∀ A B : C', G'.obj A ⊗ G'.obj B ⟶ G'.obj (A ⊗ B))
  (tr : G.obj ωX ⟶ ωY) (tr' : G'.obj ωX' ⟶ ωY')
  (χ : ∀ A : C, ΨY.obj (G.obj A) ⟶ G'.obj (ΨX.obj A))

/-- `CategoryTheory.Verdier.nearbyDualityMap_proper` for lax tensor maps `μ_G`, `μ_{G'}` given
explicitly (not through `Functor.LaxMonoidal` instances), `μ_{G'}` natural in its second
variable. -/
theorem nearbyDualityMap_proper'
    (hμG' : ∀ (A : C') {B B' : C'} (y : B ⟶ B'),
      G'.obj A ◁ G'.map y ≫ μG' A B' = μG' A B ≫ G'.map (A ◁ y))
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y))
    (hχ : ∀ {A B : C} (g : A ⟶ B), ΨY.map (G.map g) ≫ χ B = χ A ≫ G'.map (ΨX.map g))
    (hμ : ∀ A B : C, (χ A ⊗ₘ χ B) ≫ μG' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (μG A B) ≫ χ (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ ωX ≫ G'.map θX ≫ tr') (M : C) :
    ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M) =
      χ _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
        nearbyDualityMap μG' tr' (ΨX.obj M) ≫ (pre (χ M)).app ωY' := by
  apply uncurry_injective
  have hL : uncurry (ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M)) =
      μY _ _ ≫ ΨY.map (μG _ _) ≫ ΨY.map (G.map ((ihom.ev M).app ωX)) ≫ ΨY.map tr ≫ θY := by
    have hl : ΨY.obj (G.obj M) ◁ ΨY.map (nearbyDualityMap μG tr M) ≫ μY _ _ =
        μY _ _ ≫ ΨY.map (G.obj M ◁ nearbyDualityMap μG tr M) := by
      have := hμY (𝟙 (G.obj M)) (nearbyDualityMap μG tr M)
      rwa [ΨY.map_id, id_tensorHom, id_tensorHom] at this
    rw [uncurry_natural_left, uncurry_nearbyDualityMap, reassoc_of% hl, ← ΨY.map_comp_assoc,
      ← uncurry_eq, uncurry_nearbyDualityMap]
    simp only [Functor.map_comp, Category.assoc]
  have hR : uncurry (χ _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
      nearbyDualityMap μG' tr' (ΨX.obj M) ≫ (pre (χ M)).app ωY') =
      (χ M ⊗ₘ χ _) ≫ μG' _ _ ≫ G'.map (μX _ _) ≫
        G'.map (ΨX.map ((ihom.ev M).app ωX)) ≫ G'.map θX ≫ tr' := by
    rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_left,
      uncurry_nearbyDualityMap, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% (hμG' _ (nearbyDualityMap μX θX M)), ← G'.map_comp_assoc, ← uncurry_eq,
      uncurry_nearbyDualityMap, MonoidalCategory.tensorHom_def]
    simp only [Functor.map_comp, Category.assoc]
  rw [hL, hR, reassoc_of% (hμ M _),
    ← reassoc_of% (hχ (A := M ⊗ (ihom M).obj ωX) (B := ωX) ((ihom.ev M).app ωX)), ← hθ]

/-- `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` for lax tensor maps `μ_G`,
`μ_{G'}` given explicitly, with the invertibility hypotheses as explicit arguments. -/
theorem isIso_map_nearbyDualityMap_of_proper'
    (hμG' : ∀ (A : C') {B B' : C'} (y : B ⟶ B'),
      G'.obj A ◁ G'.map y ≫ μG' A B' = μG' A B ≫ G'.map (A ◁ y))
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y))
    (hχ : ∀ {A B : C} (g : A ⟶ B), ΨY.map (G.map g) ≫ χ B = χ A ≫ G'.map (ΨX.map g))
    (hμ : ∀ A B : C, (χ A ⊗ₘ χ B) ≫ μG' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (μG A B) ≫ χ (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ ωX ≫ G'.map θX ≫ tr') (M : C)
    (h₁ : IsIso (χ M)) (h₂ : IsIso (χ ((ihom M).obj ωX)))
    (h₃ : IsIso (nearbyDualityMap μG tr M)) (h₄ : IsIso (nearbyDualityMap μG' tr' (ΨX.obj M)))
    (h₅ : IsIso (nearbyDualityMap μY θY (G.obj M))) :
    IsIso (G'.map (nearbyDualityMap μX θX M)) := by
  have e := nearbyDualityMap_proper' μX μY θX θY μG μG' tr tr' χ hμG' hμY hχ hμ hθ M
  have : IsIso ((pre (χ M)).app ωY') :=
    ⟨(pre (inv (χ M))).app ωY', by rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id,
      pre_id, NatTrans.id_app], by rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id,
      NatTrans.id_app]⟩
  have h : G'.map (nearbyDualityMap μX θX M) =
      inv (χ _) ≫ (ΨY.map (nearbyDualityMap μG tr M) ≫ nearbyDualityMap μY θY (G.obj M)) ≫
        inv ((pre (χ M)).app ωY') ≫ inv (nearbyDualityMap μG' tr' (ΨX.obj M)) := by
    rw [e]
    simp
  rw [h]
  infer_instance

/-- `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper'` for an exchange given as a
natural transformation `χ : G ⋙ Ψ_Y ⟶ Ψ_X ⋙ G'`, its compatibility with the lax tensor maps
stated with the components `χ.app A` and given first. The categories and their monoidal
structures are implicit, found by unification from that compatibility rather than by instance
synthesis: for bounded constructible complexes, instances synthesized in different contexts agree
only up to proof irrelevance, and the kernel cannot compare the components of `χ` at such
differently presented objects without unfolding them. -/
theorem isIso_map_nearbyDualityMap_of_proper_natTrans {C : Type*} {_ : Category C}
    {_ : MonoidalCategory C} {_ : MonoidalClosed C} {C' : Type*} {_ : Category C'}
    {_ : MonoidalCategory C'} {_ : MonoidalClosed C'} {D : Type*} {_ : Category D}
    {_ : MonoidalCategory D} {_ : MonoidalClosed D} {D' : Type*} {_ : Category D'}
    {_ : MonoidalCategory D'} {_ : MonoidalClosed D'} {ΨX : C ⥤ C'} {ΨY : D ⥤ D'}
    {μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B)}
    {μY : ∀ A B : D, ΨY.obj A ⊗ ΨY.obj B ⟶ ΨY.obj (A ⊗ B)} {ωX : C} {ωX' : C'} {ωY : D}
    {ωY' : D'} {θX : ΨX.obj ωX ⟶ ωX'} {θY : ΨY.obj ωY ⟶ ωY'} {G : C ⥤ D} {G' : C' ⥤ D'}
    {μG : ∀ A B : C, G.obj A ⊗ G.obj B ⟶ G.obj (A ⊗ B)}
    {μG' : ∀ A B : C', G'.obj A ⊗ G'.obj B ⟶ G'.obj (A ⊗ B)} {tr : G.obj ωX ⟶ ωY}
    {tr' : G'.obj ωX' ⟶ ωY'} {χ : G ⋙ ΨY ⟶ ΨX ⋙ G'}
    (hμ : ∀ A B : C, (χ.app A ⊗ₘ χ.app B) ≫ μG' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (μG A B) ≫ χ.app (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ.app ωX ≫ G'.map θX ≫ tr')
    (hμG' : ∀ (A : C') {B B' : C'} (y : B ⟶ B'),
      G'.obj A ◁ G'.map y ≫ μG' A B' = μG' A B ≫ G'.map (A ◁ y))
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y)) (M : C)
    (h₁ : IsIso (χ.app M)) (h₂ : IsIso (χ.app ((ihom M).obj ωX)))
    (h₃ : IsIso (nearbyDualityMap μG tr M)) (h₄ : IsIso (nearbyDualityMap μG' tr' (ΨX.obj M)))
    (h₅ : IsIso (nearbyDualityMap μY θY (G.obj M))) :
    IsIso (G'.map (nearbyDualityMap μX θX M)) :=
  isIso_map_nearbyDualityMap_of_proper' μX μY θX θY μG μG' tr tr' (fun A ↦ χ.app A) hμG' hμY
    (fun g ↦ χ.naturality g) hμ hθ M h₁ h₂ h₃ h₄ h₅

end Proper

section Rigid

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type*} [Category* C'] [MonoidalCategory C'] [MonoidalClosed C']

omit [MonoidalClosed C] [MonoidalClosed C'] in
/-- A monoidal functor carries the counit `X ⊗ (Y ⊗ K) ⟶ K` of the adjunction
`tensorLeft X ⊣ tensorLeft Y` of an exact pairing to the counit of the image exact pairing
(`CategoryTheory.ExactPairing.map`), up to the tensor maps. -/
lemma μ_comp_map_tensorLeftAdjunction_counit_app (F : C ⥤ C') [F.Monoidal] (Y X K : C)
    [ExactPairing Y X] :
    Functor.LaxMonoidal.μ F X (Y ⊗ K) ≫ F.map ((tensorLeftAdjunction Y X).counit.app K) =
      F.obj X ◁ Functor.OplaxMonoidal.δ F Y K ≫
        (@tensorLeftAdjunction C' _ _ (F.obj Y) (F.obj X)
          (ExactPairing.map F Y X)).counit.app (F.obj K) := by
  let := ExactPairing.map F Y X
  rw [tensorLeftAdjunction_counit_app, tensorLeftAdjunction_counit_app]
  change _ = _ ≫ (α_ _ _ _).inv ≫ (Functor.LaxMonoidal.μ F X Y ≫ F.map (ε_ Y X) ≫
    Functor.OplaxMonoidal.η F) ▷ F.obj K ≫ (λ_ _).hom
  simp only [Functor.map_comp, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, comp_whiskerRight, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [Functor.Monoidal.map_leftUnitor F K, Functor.Monoidal.μ_δ_assoc]

/-- **Monoidal functors commute with duals**: for a monoidal functor `F` (lax tensor maps `μ`,
dualizing map the inverse `η` of the unit map) and an object `X` with a left dual `Y`, the duality
map `F RHom(X, 𝟙) ⟶ RHom(F X, 𝟙)` is an isomorphism. Both internal homs are identified with
tensoring with the duals `Y` and `F Y` (`CategoryTheory.ExactPairing.map`), and under these
identifications the duality map is `F (Y ⊗ 𝟙) ≅ F Y ⊗ F 𝟙 ≅ F Y ⊗ 𝟙`. -/
theorem isIso_nearbyDualityMap_of_monoidal (F : C ⥤ C') [F.Monoidal] (Y X : C)
    [ExactPairing Y X] :
    IsIso (nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B)
      (Functor.OplaxMonoidal.η F) X) := by
  let := ExactPairing.map F Y X
  let s := (tensorLeftAdjunction Y X).rightAdjointUniq (ihom.adjunction X)
  let s' := (tensorLeftAdjunction (F.obj Y) (F.obj X)).rightAdjointUniq
    (ihom.adjunction (F.obj X))
  have e1 : X ◁ s.hom.app (𝟙_ C) ≫ (ihom.ev X).app (𝟙_ C) =
      (tensorLeftAdjunction Y X).counit.app (𝟙_ C) :=
    (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) (𝟙_ C)
  have e2 : F.obj X ◁ s'.hom.app (𝟙_ C') ≫ (ihom.ev (F.obj X)).app (𝟙_ C') =
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (𝟙_ C') :=
    (tensorLeftAdjunction (F.obj Y) (F.obj X)).rightAdjointUniq_hom_app_counit
      (ihom.adjunction (F.obj X)) (𝟙_ C')
  have e3 : F.obj X ◁ F.obj Y ◁ Functor.OplaxMonoidal.η F ≫
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (𝟙_ C') =
      (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.app (F.obj (𝟙_ C)) ≫
        Functor.OplaxMonoidal.η F :=
    (tensorLeftAdjunction (F.obj Y) (F.obj X)).counit.naturality (Functor.OplaxMonoidal.η F)
  have h : F.map (s.hom.app (𝟙_ C)) ≫ nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ F A B)
      (Functor.OplaxMonoidal.η F) X =
      Functor.OplaxMonoidal.δ F Y (𝟙_ C) ≫ F.obj Y ◁ Functor.OplaxMonoidal.η F ≫
        s'.hom.app (𝟙_ C') := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_nearbyDualityMap, Functor.LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp_assoc, e1]
    erw [reassoc_of% (μ_comp_map_tensorLeftAdjunction_counit_app F Y X (𝟙_ C))]
    rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Category.assoc, e2, e3]
  have : IsIso (F.map (s.hom.app (𝟙_ C)) ≫ nearbyDualityMap
      (fun A B ↦ Functor.LaxMonoidal.μ F A B) (Functor.OplaxMonoidal.η F) X) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (s.hom.app (𝟙_ C))) _

end Rigid

section Lift

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]

/-- The restriction `Q.lift (P.ι ⋙ F) hF` of a lax monoidal functor `F` to full monoidal
subcategories is lax monoidal, with the tensor maps and the unit map of `F`. It is not an
instance. -/
@[instance_reducible]
noncomputable def _root_.CategoryTheory.ObjectProperty.laxMonoidalLift (F : C ⥤ D)
    [F.LaxMonoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) :
    (Q.lift (P.ι ⋙ F) hF).LaxMonoidal where
  ε := ObjectProperty.homMk (Functor.LaxMonoidal.ε F)
  μ X Y := ObjectProperty.homMk (Functor.LaxMonoidal.μ F X.obj Y.obj)
  μ_natural_left f X := ObjectProperty.hom_ext _ (Functor.LaxMonoidal.μ_natural_left F f.hom X.obj)
  μ_natural_right X f :=
    ObjectProperty.hom_ext _ (Functor.LaxMonoidal.μ_natural_right F X.obj f.hom)
  associativity X Y Z :=
    ObjectProperty.hom_ext _ (Functor.LaxMonoidal.associativity F X.obj Y.obj Z.obj)
  left_unitality X := ObjectProperty.hom_ext _ (Functor.LaxMonoidal.left_unitality F X.obj)
  right_unitality X := ObjectProperty.hom_ext _ (Functor.LaxMonoidal.right_unitality F X.obj)


/-- The unit map of a composite `F ⋙ R ⋙ I` of lax monoidal functors, `R` the lax monoidal right
adjoint of an oplax monoidal functor `L`, is invertible if those of `F` and `I` and the counit of
`L` are, and `I` inverts the unit of `L ⊣ R` at the tensor unit. -/
lemma _root_.CategoryTheory.Adjunction.isIso_ε_comp_rightAdjointLaxMonoidal
    {C D T S : Type*} [Category* C] [Category* D] [Category* T] [Category* S]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory T] [MonoidalCategory S]
    (F : C ⥤ D) {L : T ⥤ D} {R : D ⥤ T} (I : T ⥤ S) [F.LaxMonoidal] [L.OplaxMonoidal]
    [I.LaxMonoidal] (adj : L ⊣ R) [IsIso (Functor.LaxMonoidal.ε F)]
    [IsIso (Functor.OplaxMonoidal.η L)] [IsIso (Functor.LaxMonoidal.ε I)]
    [IsIso (I.map (adj.unit.app (𝟙_ T)))] :
    IsIso (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (F ⋙ R ⋙ I)
      (@Functor.LaxMonoidal.comp _ _ _ _ _ _ _ _ _ F (R ⋙ I) _
        (@Functor.LaxMonoidal.comp _ _ _ _ _ _ _ _ _ R I adj.rightAdjointLaxMonoidal _))) := by
  simp only [Functor.LaxMonoidal.comp_ε, Adjunction.rightAdjointLaxMonoidal_ε,
    Adjunction.homEquiv_unit, Functor.comp_map, Functor.map_comp]
  infer_instance
end Lift

end Verdier

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-! ### The lax monoidal structure of the direct image -/

section LaxMonoidal

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

variable (ℓ) in
/-- The lax monoidal structure of the derived direct image `Rf_*` on bounded constructible
complexes: the right adjoint of the monoidal functor `Lf^*`. Its tensor maps are adjoint to the
tensor products of the counits (`CategoryTheory.Verdier.map_rightAdjointLaxMonoidal_μ_comp_counit`).
It is not an instance. -/
noncomputable abbrev boundedConstructibleLowerStarLaxMonoidal :
    (boundedConstructibleLowerStar ℓ f).LaxMonoidal :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).rightAdjointLaxMonoidal

end LaxMonoidal

end AlgebraicGeometry.ProEtale.CondensedRing
