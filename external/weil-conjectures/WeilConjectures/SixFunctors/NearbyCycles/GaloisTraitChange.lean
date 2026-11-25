/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait on the invariant summands of nearby cycles

Let `τ : N₂ ⟶ N₁` be a morphism of models over `Spec l : Spec L₂ ⟶ Spec L₁`, and `ω : Ω₁ ⟶ Ω₂` a
homomorphism of extensions `Ωᵢ/Lᵢ` over `l`, with change of Galois layers
`τ' : N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`). The pullback exchanges of the square
```
N₂_{Ω₂} ──τ'──→ N₁_{Ω₁}
   │σ₂             │σ₁
   ↓               ↓
   N₂ ─────τ─────→ N₁
```
satisfy `α_{τ'} ∘ τ'^* α_{σ₁} = α_{σ₂} ∘ σ₂^* α_τ` up to the composition isomorphisms
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`). By SGA 4½, [Th. finitude],
Lemme 3.4, `α_{σᵢ}` is the inclusion of the direct summand `Ψ_{Nᵢ} = (Ψ_{Nᵢ_{Ωᵢ}})^{Pᵢ}` of
invariants under `Pᵢ = Aut(Ωᵢ/Lᵢ)`. This file proves that if `α_{τ'}` is invertible, `α_τ` is
invertible: `α_{τ'}` is equivariant along the restriction `P₂ ⟶ P₁`
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`), and when every
element of `P₁` is a restriction, it identifies the two invariant summands
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`). This is the step "take the
invariants under a pro-`p` group" in the induction of Deligne's proof of Th. finitude 3.7 (3.8).

The identification of the summands uses that the projector `r₁ ≫ α_{σ₁}` of the first summand is
the projector onto *all* the invariants, in the form: on cohomology sheaves (after pullback to the
special fibre of `N₂`), every map out of `Hᵠ(Ψ_{N₁_{Ω₁}})` which is invariant under `P₁` is fixed
by the projector. Of the second projector, only the invariance `ρ_σ ≫ (r₂ ≫ α_{σ₂}) = r₂ ≫ α_{σ₂}`
is used. The abstract statement is `CategoryTheory.isIso_of_comp_eq_comp_of_coinvariant`, in a
category with a jointly conservative family of functors (the cohomology functors).

## Main results

- `NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`: the square of pullback exchanges.
- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`: the change of trait is
  invertible on the invariant summands once it is invertible on the Galois layers.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} (Ω₁ Ω₂ : Type u) [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} (ω : Ω₁ →+* Ω₂)
  (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)

/-- `x ≫ m₁ = p₁ ≫ p₂ ≫ p₃` and `x ≫ m₂ = q₁ ≫ q₂ ≫ q₃` with `m₁`, `m₂` split by `m₁'`, `m₂'`
give `p₁ ≫ p₂ ≫ p₃ ≫ m₁' = q₁ ≫ q₂ ≫ q₃ ≫ m₂'`. -/
private lemma comp_eq_comp_of_comp_eq_aux {C : Type*} [Category C] {P Q Y₁ Y₂ P₁ P₂ Q₁ Q₂ : C}
    {x : P ⟶ Q} {m₁ : Q ⟶ Y₁} {m₂ : Q ⟶ Y₂} {m₁' : Y₁ ⟶ Q} {m₂' : Y₂ ⟶ Q} {p₁ : P ⟶ P₁}
    {p₂ : P₁ ⟶ P₂} {p₃ : P₂ ⟶ Y₁} {q₁ : P ⟶ Q₁} {q₂ : Q₁ ⟶ Q₂} {q₃ : Q₂ ⟶ Y₂}
    (hA : x ≫ m₁ = p₁ ≫ p₂ ≫ p₃) (hB : x ≫ m₂ = q₁ ≫ q₂ ≫ q₃) (h₁ : m₁ ≫ m₁' = 𝟙 _)
    (h₂ : m₂ ≫ m₂' = 𝟙 _) :
    p₁ ≫ p₂ ≫ p₃ ≫ m₁' = q₁ ≫ q₂ ≫ q₃ ≫ m₂' := by
  simp only [← Category.assoc] at hA hB ⊢
  rw [← hA, ← hB, Category.assoc, h₁, Category.assoc, h₂]

/-- `F (e.hom.app X) ≫ F (e.inv.app X) = 𝟙`, with all data as variables. -/
private lemma map_hom_app_comp_map_inv_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : D ⥤ E) {G G' : C ⥤ D} (e : G ≅ G') (X : C) :
    F.map (e.hom.app X) ≫ F.map (e.inv.app X) = 𝟙 _ := by
  rw [← F.map_comp, Iso.hom_inv_id_app, F.map_id]

/-- The diagonal `N₂_{Ω₂} ⟶ N₁` of the square of the change of Galois layers, over `f, f'`: the
morphism `τ` on total spaces and `τ ∘ σ₂` on generic fibres. -/
@[simps]
noncomputable def galoisLayerMapDiagonal (τ : N₂.Hom N₁ f f') :
    (N₂.galoisLayer h₂ Ω₂).Hom N₁ f f' where
  total := τ.total
  generic := pullback.fst _ _ ≫ τ.generic
  comm_j := by simp only [galoisLayer, Category.assoc, τ.comm_j]
  comm_i := τ.comm_i
  comm_ε := by simp only [galoisLayer, Category.assoc, τ.comm_ε]

/-- **The square of pullback exchanges of a change of Galois layers** (with `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ`
the projections and `τ'` the change of Galois layers):
`σ₂^* α_τ ≫ α_{σ₂} = τ'^* α_{σ₁} ≫ α_{τ'}` up to the composition isomorphisms `c`, as morphisms
`Lf'^* Ψ_{N₁} C ⟶ Ψ_{N₂_{Ω₂}} (Lf^* C)`. -/
theorem pullbackExchange_galoisLayerMap_square (τ : N₂.Hom N₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁))) :
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f')).hom.app ((N₁.nearbyCycles Λ).obj C) ≫
        L((𝟙 X₂')^*⟦Λ⟧).map ((τ.pullbackExchange Λ).app C) ≫
        ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app (L((f)^*⟦Λ⟧).obj C) ≫
        ((N₂.galoisLayer h₂ Ω₂).nearbyCycles Λ).map
          ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp f)).inv.app C) =
      (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f')).hom.app ((N₁.nearbyCycles Λ).obj C) ≫
        L((f')^*⟦Λ⟧).map (((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C) ≫
        ((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app (L((𝟙 X₁)^*⟦Λ⟧).obj C) ≫
        ((N₂.galoisLayer h₂ Ω₂).nearbyCycles Λ).map
          ((leftDerivedUpperStarCompOfEq Λ (Category.comp_id f)).inv.app C) := by
  have hA := (N₂.galoisLayerHom h₂ Ω₂).pullbackExchange_comp_app_of_eq Λ τ
    (galoisLayerMapDiagonal Ω₂ τ) (Category.id_comp f) (Category.id_comp f')
    (by simp) (by simp) C
  have hB := (galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange_comp_app_of_eq Λ
    (N₁.galoisLayerHom h₁ Ω₁) (galoisLayerMapDiagonal Ω₂ τ) (Category.comp_id f)
    (Category.comp_id f') (Category.comp_id _) (by simp) C
  have key := comp_eq_comp_of_comp_eq_aux hA hB (map_hom_app_comp_map_inv_app _ _ _)
    (map_hom_app_comp_map_inv_app _ _ _)
  convert key using 3

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}
  {hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l}

/-- The diagram chase for the square of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`. -/
private lemma sq_aux {C : Type*} [Category C] {P Q R S T U P₁ B₁ B₂ : C} {α : P ⟶ Q} {i' : Q ⟶ R}
    {i : P ⟶ S} {Lα : S ⟶ R} {a : R ⟶ T} {m : T ⟶ U} {cA' : P ⟶ S} {c : P ⟶ P₁} {g : P₁ ⟶ B₁}
    {β : B₁ ⟶ B₂} {n : B₂ ⟶ U} {n' : U ⟶ B₂} (hnat : α ≫ i' = i ≫ Lα) (hI : cA' = i)
    (hsq : cA' ≫ Lα ≫ a ≫ m = c ≫ g ≫ β ≫ n) (hn : n ≫ n' = 𝟙 _) :
    α ≫ i' ≫ a ≫ m ≫ n' = (c ≫ g) ≫ β := by
  subst hI
  rw [reassoc_of% hnat]
  simp only [← Category.assoc] at hsq ⊢
  rw [hsq]
  simp [hn]

/-- `F (e.inv.app X) ≫ F (e.hom.app X) = 𝟙`, with all data as variables. -/
private lemma map_inv_app_comp_map_hom_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : D ⥤ E) {G G' : C ⥤ D} (e : G ≅ G') (X : C) :
    F.map (e.inv.app X) ≫ F.map (e.hom.app X) = 𝟙 _ := by
  rw [← F.map_comp, Iso.inv_hom_id_app, F.map_id]

/-- Transport split invariant summands through the composition isomorphisms of a square.
The diagram chase is carried out with abstract functors, before specializing to derived
pullbacks and nearby cycles. -/
private lemma isIso_of_invariant_summands_square {D E₁ E : Type*} [Category D]
    [Category E₁] [Category E] {ι : Type*} {A : ι → Type*} [∀ q, Category (A q)]
    (F : E₁ ⥤ E) (Ψ : D ⥤ E) (H : ∀ q, E ⥤ A q)
    (hcons : ∀ {X Y : E} (g : X ⟶ Y), (∀ q, IsIso ((H q).map g)) → IsIso g)
    {P Q R S : E} {A₁ B₁ : E₁} {T U V : D}
    (α : P ⟶ Q) (α₁ : A₁ ⟶ B₁) (r₁ : B₁ ⟶ A₁) (hr₁ : α₁ ≫ r₁ = 𝟙 _)
    (α₂ : R ⟶ Ψ.obj U) (r₂ : Ψ.obj U ⟶ R) (hr₂ : α₂ ≫ r₂ = 𝟙 _)
    (cA : T ≅ U) (cB : T ≅ V) (cB' : P ≅ F.obj A₁) (I' : R ≅ Q)
    (i : P ⟶ S) (Lα : S ⟶ R) (cA' : P ⟶ S)
    (hnat : α ≫ I'.inv = i ≫ Lα) (hIA : cA' = i)
    (β : F.obj B₁ ⟶ Ψ.obj V) [IsIso β]
    (hsq : cA' ≫ Lα ≫ α₂ ≫ Ψ.map cA.inv =
      cB'.hom ≫ F.map α₁ ≫ β ≫ Ψ.map cB.inv)
    {κ : Type*} (ρ₁ : κ → (B₁ ⟶ B₁)) (ρ₂ : κ → (Ψ.obj V ⟶ Ψ.obj V))
    (ρ₂' : κ → (Ψ.obj U ⟶ Ψ.obj U))
    (hβ : ∀ k, F.map (ρ₁ k) ≫ β = β ≫ ρ₂ k)
    (hn : ∀ k, ρ₂ k ≫ Ψ.map (cB.inv ≫ cA.hom) =
      Ψ.map (cB.inv ≫ cA.hom) ≫ ρ₂' k)
    (he₂ : ∀ k, ρ₂' k ≫ (r₂ ≫ α₂) = r₂ ≫ α₂)
    (he₁ : ∀ q {W : A q} (φ : (H q).obj (F.obj B₁) ⟶ W),
      (∀ k, (H q).map (F.map (ρ₁ k)) ≫ φ = φ) →
      (H q).map (F.map (r₁ ≫ α₁)) ≫ φ = φ) : IsIso α := by
  refine isIso_of_comp_eq_comp_of_coinvariant H hcons α
    (cB'.hom ≫ F.map α₁) (F.map r₁ ≫ cB'.inv) ?_
    (I'.inv ≫ α₂ ≫ Ψ.map (cA.inv ≫ cB.hom))
    (Ψ.map (cB.inv ≫ cA.hom) ≫ r₂ ≫ I'.hom) ?_ β ?_
    (fun k ↦ F.map (ρ₁ k)) ρ₂ (fun k ↦ ⟨k, hβ k⟩) (fun k ↦ ?_) (fun q W φ hφ ↦ ?_)
  · simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hr₁]
    simp
  · simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, show (cA.inv ≫ cB.hom) ≫ cB.inv ≫ cA.hom = 𝟙 _ by simp]
    simp [reassoc_of% hr₂]
  · rw [Functor.map_comp]
    exact sq_aux hnat hIA hsq (by rw [← Ψ.map_comp, cB.inv_hom_id, Ψ.map_id])
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% (hn k), reassoc_of% (he₂ k)]
  · have h : (F.map r₁ ≫ cB'.inv) ≫ cB'.hom ≫ F.map α₁ = F.map (r₁ ≫ α₁) := by
      rw [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
    rw [h]
    exact he₁ q φ hφ

/-- **Change of trait on the invariant summands** (SGA 4½, [Th. finitude], proof of 3.7, 3.8). Let
`τ : N₂ ⟶ N₁` be a morphism of models over `Spec l`, `ω : Ω₁ ⟶ Ω₂` a homomorphism of extensions
over `l`, `τ'` the change of Galois layers, and `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ` the projections. Assume
* the exchanges `α_{σᵢ}` have retractions `rᵢ` (Lemme 3.4: `Ψ_{Nᵢ}` is a direct summand of
  `Ψ_{Nᵢ_{Ωᵢ}}`), the projector `r₂ ≫ α_{σ₂}` being invariant under the Galois action of
  `Aut(Ω₂/L₂)`;
* the projector `r₁ ≫ α_{σ₁}` is the projector onto the invariants of the family `(σ k).1` of
  elements of `Aut(Ω₁/L₁)`: on cohomology sheaves of the pullback to `X₂'`, every map invariant
  under the `(σ k).1` is fixed by it;
* each `(σ k).1` is the restriction of `(σ k).2 ∈ Aut(Ω₂/L₂)` along `ω`.
If the change of Galois layers `α_{τ'}` is invertible, so is the change of trait `α_τ`. -/
theorem Hom.isIso_pullbackExchange_app_of_galoisLayerMap (τ : N₂.Hom N₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁)))
    {κ : Type*} (σ : κ → (Ω₁ ≃ₐ[L₁] Ω₁) × (Ω₂ ≃ₐ[L₂] Ω₂))
    (hσ : ∀ k x, ω ((σ k).1 x) = (σ k).2 (ω x))
    (h₁split : ∃ r₁, ((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C ≫ r₁ = 𝟙 _ ∧
      ∀ (q : ℤ) {W : Mod (Sheaf (Scheme.ProEt.topology X₂') Ab.{u + 1})
        (condensedRingObj Λ X₂')}
      (φ : (DerivedCategory.homologyFunctor _ q).obj (L((f')^*⟦Λ⟧).obj
        (((N₁.galoisLayer h₁ Ω₁).nearbyCycles Λ).obj (L((𝟙 X₁)^*⟦Λ⟧).obj C))) ⟶ W),
      (∀ k, (DerivedCategory.homologyFunctor _ q).map (L((f')^*⟦Λ⟧).map
        (N₁.galoisLayerAction Λ h₁ Ω₁ (σ k).1 (L((𝟙 X₁)^*⟦Λ⟧).obj C))) ≫ φ = φ) →
      (DerivedCategory.homologyFunctor _ q).map (L((f')^*⟦Λ⟧).map
        (r₁ ≫ ((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C)) ≫ φ = φ)
    (C₂ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₂) Ab.{u + 1})
      (condensedRingObj Λ X₂))) (hC₂ : L((f)^*⟦Λ⟧).obj C = C₂)
    (h₂split : ∃ r₂, ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app C₂ ≫ r₂ = 𝟙 _ ∧
      ∀ σ₂ : Ω₂ ≃ₐ[L₂] Ω₂, N₂.galoisLayerAction Λ h₂ Ω₂ σ₂ (L((𝟙 X₂)^*⟦Λ⟧).obj C₂) ≫
          (r₂ ≫ ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app C₂) =
        r₂ ≫ ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app C₂)
    (hβ : IsIso (((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app
      (L((𝟙 X₁)^*⟦Λ⟧).obj C))) :
    IsIso ((τ.pullbackExchange Λ).app C) := by
  obtain ⟨r₁, hr₁, he₁⟩ := h₁split
  have := hβ
  subst hC₂
  obtain ⟨r₂, hr₂, he₂⟩ := h₂split
  -- the composition isomorphisms
  let cA := (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f)).app C
  let cB := (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f)).app C
  let cB' := (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f')).app ((N₁.nearbyCycles Λ).obj C)
  let I' := (leftDerivedUpperStarId Λ X₂').app ((N₂.nearbyCycles Λ).obj (L((f)^*⟦Λ⟧).obj C))
  let Ψ₂Ω := (N₂.galoisLayer h₂ Ω₂).nearbyCycles Λ
  let α₁ := ((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C
  let α₂ := ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app (L((f)^*⟦Λ⟧).obj C)
  let β := ((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app (L((𝟙 X₁)^*⟦Λ⟧).obj C)
  have hsq := pullbackExchange_galoisLayerMap_square Λ Ω₁ Ω₂ ω hω τ hτ C
  have hA' := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId_self Λ
    (Category.id_comp f') ((N₁.nearbyCycles Λ).obj C)
  -- Use the inverse characterization directly, without a cancellation rewrite.
  have hIA := (Iso.comp_hom_eq_id ((leftDerivedUpperStarId Λ X₂').app _)).1 hA'
  have hnat := (leftDerivedUpperStarId Λ X₂').inv.naturality ((τ.pullbackExchange Λ).app C)
  dsimp only [Functor.id_obj, Functor.id_map] at hnat
  let α := (τ.pullbackExchange Λ).app C
  let A := Mod (Sheaf (Scheme.ProEt.topology X₂') Ab.{u + 1}) (condensedRingObj Λ X₂')
  let H := DerivedCategory.homologyFunctor A
  have hcons {X Y : DerivedCategory A} (g : X ⟶ Y) :
      (∀ q, IsIso ((H q).map g)) → IsIso g := (DerivedCategory.isIso_iff A g).2
  -- Infer the pullback functor and the action objects from the square and retractions.
  have key := isIso_of_invariant_summands_square (A := fun _ : ℤ ↦ A)
    _ Ψ₂Ω H (fun g hg ↦ hcons g hg) α α₁ r₁ hr₁ α₂ r₂ hr₂
    cA cB cB' I' _ _ _ hnat hIA β hsq
    (fun k ↦ N₁.galoisLayerAction Λ h₁ Ω₁ (σ k).1 _)
    (fun k ↦ N₂.galoisLayerAction Λ h₂ Ω₂ (σ k).2 _)
    (fun k ↦ N₂.galoisLayerAction Λ h₂ Ω₂ (σ k).2 _)
    (fun k ↦ (pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction Λ Ω₁ Ω₂ ω hω τ hτ
      (σ k).1 (σ k).2 (hσ k) _).symm)
    (fun k ↦ N₂.galoisLayerAction_naturality Λ h₂ Ω₂ (σ k).2 (cB.inv ≫ cA.hom))
    (fun k ↦ he₂ (σ k).2) he₁
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
