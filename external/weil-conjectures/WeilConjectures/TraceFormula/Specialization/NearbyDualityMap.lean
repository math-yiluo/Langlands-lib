/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!

# The duality map of nearby cycles

Let `Ψ : C ⥤ C'` be a functor between monoidal closed categories with a lax tensor map
`μ_{A,B} : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` (natural in `A` and `B`), and let `θ : Ψ ω ⟶ ω'` be a morphism
from the image of an object `ω` of `C` to an object `ω'` of `C'`. Write `D = RHom(-, ω)` and
`D' = RHom(-, ω')`. The *duality map* (blueprint
`proposition-nearby-cycles-commute-verdier-duality`)
```
δ_M : Ψ D M ⟶ D' Ψ M
```
(`CategoryTheory.Verdier.nearbyDualityMap`) is the tensor–Hom adjoint of the pairing
```
Ψ M ⊗ Ψ D M --μ--> Ψ (M ⊗ D M) --Ψ ev--> Ψ ω --θ--> ω'.
```
In the application `Ψ = S_X = RΨ_{X/S}` is the nearby cycles functor of a scheme `X` over a
strictly henselian trait, `ω`, `ω'` are the dualizing complexes of the generic and special
fibres and `θ = θ_X = β_{a_X}(A)` is the dualizing map of the exceptional exchange; Gabber's
theorem says that `δ_M` is an isomorphism.

The construction is formal, and so are its compatibilities with the operations (blueprint
`lemma-nearby-duality-proper-direct-image`), which only use the defining properties of the exchange
maps:

* the same construction applied to a lax monoidal functor `G` with a trace `G ω_X ⟶ ω_Y` gives
  the map `G D_X ⟶ D_Y G` of Verdier duality for a proper direct image `G = Rf_*` (with the
  trace `Rf_* ω_X = Rf_! Rf^! ω_Y ⟶ ω_Y`), and the comparison `F D_X ⟶ D_U F` of the duality
  functors for an open restriction `F = j^*` (with `j^* ω_X ≅ ω_U`);
* **proper direct image** (`CategoryTheory.Verdier.nearbyDualityMap_proper`, part (1)): if the
  lax tensor maps commute with the proper exchange `χ : Ψ_Y G ⟶ G' Ψ_X` and the dualizing maps
  satisfy `θ_Y ∘ Ψ_Y(tr) = tr' ∘ G'(θ_X) ∘ χ` (the ordinary-adjoint form of
  `θ_X = f_s^! θ_Y ∘ β_f(ω_Y)`), then `δ_{Y, G M}` and `G' δ_{X,M}` agree under `χ` and the
  Verdier duality maps of `G` and `G'`;
* **open restriction** (`CategoryTheory.Verdier.nearbyDualityMap_restrict`, part (2)): the same
  for a pullback exchange `α : F' Ψ_X ⟶ Ψ_U F` which is monoidal and compatible with `θ`;
* **normalization** (part (3)): on the trait itself nearby cycles are the identity, and the
  duality map with `μ = 𝟙`, `θ = 𝟙` is the identity
  (`CategoryTheory.Verdier.nearbyDualityMap_id`). Combined with part (1) for the structure map
  of a proper scheme this gives that `RΓ(X_s, δ_{X,M})` is an isomorphism as soon as the
  exchange maps and the global Verdier duality maps are
  (`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper`).

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory.Verdier

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {C' : Type u₂} [Category.{v₂} C'] [MonoidalCategory C'] [MonoidalClosed C']

section Definition

variable {Ψ : C ⥤ C'} (μ : ∀ A B : C, Ψ.obj A ⊗ Ψ.obj B ⟶ Ψ.obj (A ⊗ B)) {ω : C} {ω' : C'}
  (θ : Ψ.obj ω ⟶ ω')

/-- The pairing `Ψ M ⊗ Ψ D M ⟶ Ψ (M ⊗ D M) ⟶ Ψ ω ⟶ ω'`, `D = RHom(-, ω)`: the lax tensor map,
`Ψ` of the evaluation, and `θ`. -/
noncomputable def nearbyDualityPairing (M : C) : Ψ.obj M ⊗ Ψ.obj ((ihom M).obj ω) ⟶ ω' :=
  μ _ _ ≫ Ψ.map ((ihom.ev M).app ω) ≫ θ

/-- The **duality map** `δ_M : Ψ D M ⟶ D' Ψ M` (blueprint
`proposition-nearby-cycles-commute-verdier-duality`), `D = RHom(-, ω)` and `D' = RHom(-, ω')`: the
tensor–Hom adjoint of the pairing `θ ∘ Ψ(ev) ∘ μ : Ψ M ⊗ Ψ D M ⟶ ω'`. -/
noncomputable def nearbyDualityMap (M : C) :
    Ψ.obj ((ihom M).obj ω) ⟶ (ihom (Ψ.obj M)).obj ω' :=
  curry (nearbyDualityPairing μ θ M)

lemma uncurry_nearbyDualityMap (M : C) :
    uncurry (nearbyDualityMap μ θ M) = μ _ _ ≫ Ψ.map ((ihom.ev M).app ω) ≫ θ :=
  uncurry_curry _

/-- The duality map composed with the evaluation is the defining pairing. -/
@[reassoc]
lemma whiskerLeft_nearbyDualityMap_comp_ev (M : C) :
    Ψ.obj M ◁ nearbyDualityMap μ θ M ≫ (ihom.ev (Ψ.obj M)).app ω' =
      μ _ _ ≫ Ψ.map ((ihom.ev M).app ω) ≫ θ :=
  whiskerLeft_curry_ihom_ev_app _ _ _

/-- Precomposition with a map `f : ω'₁ ⟶ ω'₂` of the target dualizing objects. -/
lemma nearbyDualityMap_comp_ihom_map {ω'₂ : C'} (f : ω' ⟶ ω'₂) (M : C) :
    nearbyDualityMap μ θ M ≫ (ihom (Ψ.obj M)).map f = nearbyDualityMap μ (θ ≫ f) M := by
  rw [nearbyDualityMap, ← curry_natural_right, nearbyDualityMap, nearbyDualityPairing,
    nearbyDualityPairing, Category.assoc, Category.assoc]

omit [MonoidalClosed C] [MonoidalClosed C'] in
/-- The lax tensor map is natural in its second variable (a consequence of naturality). -/
private lemma μ_whiskerLeft_aux
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    (A : C) {B B' : C} (y : B ⟶ B') :
    Ψ.obj A ◁ Ψ.map y ≫ μ A B' = μ A B ≫ Ψ.map (A ◁ y) := by
  have := hμ (𝟙 A) y
  rwa [Ψ.map_id, id_tensorHom, id_tensorHom] at this

omit [MonoidalClosed C] [MonoidalClosed C'] in
/-- The lax tensor map is natural in its first variable (a consequence of naturality). -/
private lemma μ_whiskerRight_aux
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    {A A' : C} (x : A ⟶ A') (B : C) :
    Ψ.map x ▷ Ψ.obj B ≫ μ A' B = μ A B ≫ Ψ.map (x ▷ B) := by
  have := hμ x (𝟙 B)
  rwa [Ψ.map_id, tensorHom_id, tensorHom_id] at this

/-- **Naturality of the duality map** in `M`: for `g : M ⟶ N`, the square
`Ψ D N ⟶ Ψ D M ⟶ D' Ψ M` and `Ψ D N ⟶ D' Ψ N ⟶ D' Ψ M` commutes. -/
theorem map_pre_comp_nearbyDualityMap
    (hμ : ∀ {A A' B B' : C} (x : A ⟶ A') (y : B ⟶ B'),
      (Ψ.map x ⊗ₘ Ψ.map y) ≫ μ A' B' = μ A B ≫ Ψ.map (x ⊗ₘ y))
    {M N : C} (g : M ⟶ N) :
    Ψ.map ((pre g).app ω) ≫ nearbyDualityMap μ θ M =
      nearbyDualityMap μ θ N ≫ (pre (Ψ.map g)).app ω' := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_nearbyDualityMap, uncurry_nearbyDualityMap,
    reassoc_of% (μ_whiskerLeft_aux μ hμ M ((pre g).app ω)),
    reassoc_of% (μ_whiskerRight_aux μ hμ g _), ← Ψ.map_comp_assoc, ← Ψ.map_comp_assoc,
    id_tensor_pre_app_comp_ev]

end Definition

/-! ### Normalization -/

section Normalization

/-- **Normalization** (blueprint `lemma-nearby-duality-proper-direct-image` (3)): for the identity
functor, with the identity as lax tensor map and as dualizing map, the duality map is the
identity. -/
@[simp]
theorem nearbyDualityMap_id (ω : C) (M : C) :
    nearbyDualityMap (Ψ := 𝟭 C) (fun A B ↦ 𝟙 (A ⊗ B)) (𝟙 ω) M = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_nearbyDualityMap]
  change 𝟙 _ ≫ (ihom.ev M).app ω ≫ 𝟙 ω = uncurry (𝟙 ((ihom M).obj ω))
  erw [Category.id_comp, Category.comp_id, uncurry_id_eq_ev]

end Normalization

/-! ### Proper direct image -/

section Proper

variable {D : Type u₃} [Category.{v₃} D] [MonoidalCategory D] [MonoidalClosed D]
  {D' : Type u₄} [Category.{v₄} D'] [MonoidalCategory D'] [MonoidalClosed D']
  {ΨX : C ⥤ C'} {ΨY : D ⥤ D'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μY : ∀ A B : D, ΨY.obj A ⊗ ΨY.obj B ⟶ ΨY.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωY : D} {ωY' : D'} (θX : ΨX.obj ωX ⟶ ωX') (θY : ΨY.obj ωY ⟶ ωY')
  {G : C ⥤ D} {G' : C' ⥤ D'} [G.LaxMonoidal] [G'.LaxMonoidal]
  (tr : G.obj ωX ⟶ ωY) (tr' : G'.obj ωX' ⟶ ωY')
  (χ : ∀ A : C, ΨY.obj (G.obj A) ⟶ G'.obj (ΨX.obj A))

/-- **Nearby duality and proper direct image** (blueprint `lemma-nearby-duality-proper-direct-image`
(1)). Let `G = Rf_{η*}` and `G' = Rf_{s*}` be lax monoidal with traces `tr : G ω_X ⟶ ω_Y` and
`tr' : G' ω_{X_s} ⟶ ω_{Y_s}`, so that the duality maps of `(G, μ_G, tr)` and `(G', μ_{G'}, tr')`
are the maps `Rf_* D ⟶ D Rf_*` of Verdier duality, and let `χ : Ψ_Y G ⟶ G' Ψ_X` be natural. If
* the lax tensor maps commute with `χ`: `G'(μ_X) ∘ μ_{G'} ∘ (χ ⊗ χ) = χ ∘ Ψ_Y(μ_G) ∘ μ_Y`, and
* the dualizing maps are compatible: `θ_Y ∘ Ψ_Y(tr) = tr' ∘ G'(θ_X) ∘ χ`,

then `δ_{Y, G M} ∘ Ψ_Y(G D_X M ⟶ D_Y G M)` is
`D(χ_M) ∘ (G' D Ψ_X M ⟶ D G' Ψ_X M) ∘ G'(δ_{X,M}) ∘ χ_{D_X M}`. -/
theorem nearbyDualityMap_proper
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y))
    (hχ : ∀ {A B : C} (g : A ⟶ B), ΨY.map (G.map g) ≫ χ B = χ A ≫ G'.map (ΨX.map g))
    (hμ : ∀ A B : C, (χ A ⊗ₘ χ B) ≫ Functor.LaxMonoidal.μ G' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (Functor.LaxMonoidal.μ G A B) ≫ χ (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ ωX ≫ G'.map θX ≫ tr') (M : C) :
    ΨY.map (nearbyDualityMap (Functor.LaxMonoidal.μ G) tr M) ≫
        nearbyDualityMap μY θY (G.obj M) =
      χ _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
        nearbyDualityMap (Functor.LaxMonoidal.μ G') tr' (ΨX.obj M) ≫ (pre (χ M)).app ωY' := by
  apply uncurry_injective
  have hL : uncurry (ΨY.map (nearbyDualityMap (Functor.LaxMonoidal.μ G) tr M) ≫
      nearbyDualityMap μY θY (G.obj M)) = μY _ _ ≫ ΨY.map (Functor.LaxMonoidal.μ G _ _) ≫
        ΨY.map (G.map ((ihom.ev M).app ωX)) ≫ ΨY.map tr ≫ θY := by
    rw [uncurry_natural_left, uncurry_nearbyDualityMap,
      reassoc_of% (μ_whiskerLeft_aux μY hμY (G.obj M) (nearbyDualityMap _ tr M)),
      ← ΨY.map_comp_assoc, ← uncurry_eq, uncurry_nearbyDualityMap]
    simp only [Functor.map_comp, Category.assoc]
  have hR : uncurry (χ _ ≫ G'.map (nearbyDualityMap μX θX M) ≫
      nearbyDualityMap (Functor.LaxMonoidal.μ G') tr' (ΨX.obj M) ≫ (pre (χ M)).app ωY') =
      (χ M ⊗ₘ χ _) ≫ Functor.LaxMonoidal.μ G' _ _ ≫ G'.map (μX _ _) ≫
        G'.map (ΨX.map ((ihom.ev M).app ωX)) ≫ G'.map θX ≫ tr' := by
    rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_left,
      uncurry_nearbyDualityMap, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← G'.map_comp_assoc, ← uncurry_eq,
      uncurry_nearbyDualityMap, tensorHom_def]
    simp only [Functor.map_comp, Category.assoc]
  rw [hL, hR, reassoc_of% (hμ M _), 
    ← reassoc_of% (hχ (A := M ⊗ (ihom M).obj ωX) (B := ωX) ((ihom.ev M).app ωX)), ← hθ]

/-- **Global duality kills the cone** (blueprint `lemma-nearby-duality-proper-direct-image` (3),
formal part): in the situation of `nearbyDualityMap_proper`, if `χ` is invertible at `M` and
`D_X M`, the Verdier duality maps of `G` at `M` and of `G'` at `Ψ_X M` are isomorphisms, and the
duality map `δ_{Y, G M}` is an isomorphism (for `Y` the trait, `δ_Y` is the identity by the
normalization `nearbyDualityMap_id`), then `G' δ_{X,M}` is an isomorphism. For `X` proper over
the trait and `G' = RΓ(X_s, -)`, this says that `RΓ(X_s, -)` kills the cone of `δ_{X,M}`. -/
theorem isIso_map_nearbyDualityMap_of_proper
    (hμY : ∀ {A A' B B' : D} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨY.map x ⊗ₘ ΨY.map y) ≫ μY A' B' = μY A B ≫ ΨY.map (x ⊗ₘ y))
    (hχ : ∀ {A B : C} (g : A ⟶ B), ΨY.map (G.map g) ≫ χ B = χ A ≫ G'.map (ΨX.map g))
    (hμ : ∀ A B : C, (χ A ⊗ₘ χ B) ≫ Functor.LaxMonoidal.μ G' _ _ ≫ G'.map (μX A B) =
      μY _ _ ≫ ΨY.map (Functor.LaxMonoidal.μ G A B) ≫ χ (A ⊗ B))
    (hθ : ΨY.map tr ≫ θY = χ ωX ≫ G'.map θX ≫ tr') (M : C)
    [IsIso (χ M)] [IsIso (χ ((ihom M).obj ωX))]
    [IsIso (nearbyDualityMap (Functor.LaxMonoidal.μ G) tr M)]
    [IsIso (nearbyDualityMap (Functor.LaxMonoidal.μ G') tr' (ΨX.obj M))]
    [IsIso (nearbyDualityMap μY θY (G.obj M))] :
    IsIso (G'.map (nearbyDualityMap μX θX M)) := by
  have e := nearbyDualityMap_proper μX μY θX θY tr tr' χ hμY hχ hμ hθ M
  have : IsIso ((pre (χ M)).app ωY') :=
    ⟨(pre (inv (χ M))).app ωY', by rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id,
      pre_id, NatTrans.id_app], by rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id,
      NatTrans.id_app]⟩
  have h : G'.map (nearbyDualityMap μX θX M) =
      inv (χ _) ≫ (ΨY.map (nearbyDualityMap (Functor.LaxMonoidal.μ G) tr M) ≫
        nearbyDualityMap μY θY (G.obj M)) ≫ inv ((pre (χ M)).app ωY') ≫
          inv (nearbyDualityMap (Functor.LaxMonoidal.μ G') tr' (ΨX.obj M)) := by
    rw [e]
    simp
  rw [h]
  infer_instance

end Proper

/-! ### Open restriction -/

section Restriction

variable {U : Type u₃} [Category.{v₃} U] [MonoidalCategory U] [MonoidalClosed U]
  {U' : Type u₄} [Category.{v₄} U'] [MonoidalCategory U'] [MonoidalClosed U']
  {ΨX : C ⥤ C'} {ΨU : U ⥤ U'} (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
  (μU : ∀ A B : U, ΨU.obj A ⊗ ΨU.obj B ⟶ ΨU.obj (A ⊗ B))
  {ωX : C} {ωX' : C'} {ωU : U} {ωU' : U'} (θX : ΨX.obj ωX ⟶ ωX') (θU : ΨU.obj ωU ⟶ ωU')
  {F : C ⥤ U} {F' : C' ⥤ U'} [F.LaxMonoidal] [F'.LaxMonoidal]
  (ρ : F.obj ωX ⟶ ωU) (ρ' : F'.obj ωX' ⟶ ωU')
  (α : ∀ A : C, F'.obj (ΨX.obj A) ⟶ ΨU.obj (F.obj A))

/-- **Nearby duality and open restriction** (blueprint `lemma-nearby-duality-proper-direct-image`
(2)). Let `F = j_η^*` and `F' = j_s^*` be (lax) monoidal with maps `ρ : F ω_X ⟶ ω_U` and
`ρ' : F' ω_{X_s} ⟶ ω_{U_s}` (the identifications `j^* ω_X ≅ ω_U`), so that the duality maps of
`(F, μ_F, ρ)` and `(F', μ_{F'}, ρ')` are the comparisons `j^* D_X ⟶ D_U j^*`, and let
`α : F' Ψ_X ⟶ Ψ_U F` be the (natural) pullback exchange. If `α` is monoidal,
`Ψ_U(μ_F) ∘ μ_U ∘ (α ⊗ α) = α ∘ F'(μ_X) ∘ μ_{F'}`, and compatible with the dualizing maps,
`ρ' ∘ F'(θ_X) = θ_U ∘ Ψ_U(ρ) ∘ α`, then `(F' D Ψ_X M ⟶ D F' Ψ_X M) ∘ F'(δ_{X,M})` is
`D(α_M) ∘ δ_{U, F M} ∘ Ψ_U(F D_X M ⟶ D_U F M) ∘ α_{D_X M}`. -/
theorem nearbyDualityMap_restrict
    (hμU : ∀ {A A' B B' : U} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨU.map x ⊗ₘ ΨU.map y) ≫ μU A' B' = μU A B ≫ ΨU.map (x ⊗ₘ y))
    (hα : ∀ {A B : C} (g : A ⟶ B), F'.map (ΨX.map g) ≫ α B = α A ≫ ΨU.map (F.map g))
    (hμ : ∀ A B : C, (α A ⊗ₘ α B) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F A B) =
      Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX A B) ≫ α (A ⊗ B))
    (hθ : F'.map θX ≫ ρ' = α ωX ≫ ΨU.map ρ ≫ θU) (M : C) :
    F'.map (nearbyDualityMap μX θX M) ≫
        nearbyDualityMap (Functor.LaxMonoidal.μ F') ρ' (ΨX.obj M) =
      α _ ≫ ΨU.map (nearbyDualityMap (Functor.LaxMonoidal.μ F) ρ M) ≫
        nearbyDualityMap μU θU (F.obj M) ≫ (pre (α M)).app ωU' := by
  apply uncurry_injective
  have hL : uncurry (F'.map (nearbyDualityMap μX θX M) ≫
      nearbyDualityMap (Functor.LaxMonoidal.μ F') ρ' (ΨX.obj M)) =
      Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX _ _) ≫ F'.map (ΨX.map ((ihom.ev M).app ωX)) ≫
        F'.map θX ≫ ρ' := by
    rw [uncurry_natural_left, uncurry_nearbyDualityMap,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← F'.map_comp_assoc, ← uncurry_eq,
      uncurry_nearbyDualityMap]
    simp only [Functor.map_comp, Category.assoc]
  have hR : uncurry (α _ ≫ ΨU.map (nearbyDualityMap (Functor.LaxMonoidal.μ F) ρ M) ≫
      nearbyDualityMap μU θU (F.obj M) ≫ (pre (α M)).app ωU') =
      (α M ⊗ₘ α _) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F _ _) ≫
        ΨU.map (F.map ((ihom.ev M).app ωX)) ≫ ΨU.map ρ ≫ θU := by
    rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_left,
      uncurry_nearbyDualityMap, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% (μ_whiskerLeft_aux μU hμU (F.obj M) (nearbyDualityMap _ ρ M)),
      ← ΨU.map_comp_assoc, ← uncurry_eq, uncurry_nearbyDualityMap, tensorHom_def]
    simp only [Functor.map_comp, Category.assoc]
  rw [hL, hR, reassoc_of% (hμ M _), 
    ← reassoc_of% (hα (A := M ⊗ (ihom M).obj ωX) (B := ωX) ((ihom.ev M).app ωX)), ← hθ]

variable {μX μU} in
/-- An exchange `α : Ψ_X ⋙ F' ⟶ F ⋙ Ψ_U` is *monoidal* for the lax tensor maps `μ_X`, `μ_U` of
`Ψ_X`, `Ψ_U` and those of `F`, `F'`:
`Ψ_U(μ_F) ∘ μ_U ∘ (α ⊗ α) = α ∘ F'(μ_X) ∘ μ_{F'}`. -/
def IsMonoidalExchange (α : ΨX ⋙ F' ⟶ F ⋙ ΨU) : Prop :=
  ∀ A B : C, (α.app A ⊗ₘ α.app B) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F A B) =
    Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX A B) ≫ α.app (A ⊗ B)

/-- `CategoryTheory.Verdier.nearbyDualityMap_restrict` for an exchange given as a natural
transformation `α : Ψ_X ⋙ F' ⟶ F ⋙ Ψ_U`. -/
theorem nearbyDualityMap_restrict_natTrans
    (hμU : ∀ {A A' B B' : U} (x : A ⟶ A') (y : B ⟶ B'),
      (ΨU.map x ⊗ₘ ΨU.map y) ≫ μU A' B' = μU A B ≫ ΨU.map (x ⊗ₘ y))
    (α : ΨX ⋙ F' ⟶ F ⋙ ΨU) (hμ : IsMonoidalExchange (μX := μX) (μU := μU) α)
    (hθ : F'.map θX ≫ ρ' = α.app ωX ≫ ΨU.map ρ ≫ θU) (M : C) :
    F'.map (nearbyDualityMap μX θX M) ≫
        nearbyDualityMap (Functor.LaxMonoidal.μ F') ρ' (ΨX.obj M) =
      α.app _ ≫ ΨU.map (nearbyDualityMap (Functor.LaxMonoidal.μ F) ρ M) ≫
        nearbyDualityMap μU θU (F.obj M) ≫ (pre (α.app M)).app ωU' :=
  nearbyDualityMap_restrict μX μU θX θU ρ ρ' (fun A ↦ α.app A) hμU (fun g ↦ α.naturality g) hμ
    hθ M

end Restriction

end CategoryTheory.Verdier
