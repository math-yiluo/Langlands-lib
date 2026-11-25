/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethAverage

/-!

# Invariants commute with the Künneth map: the coinvariant form

The generic-slicing step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, identification (2) and projection formula (3))
compares the pullback of the Künneth map `Π` to a slice with the Künneth map `Π'` of the pullback
models, in the square of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`
```
Lρ'^* Π ≫ a = δ ≫ (u_M ⊗ u_N) ≫ Π'.
```
When `u_M` and `a` are the inclusions of the invariants of a pro-`p` group and `u_N` is invertible
(the group acting trivially on the second factor), `Lρ'^* Π` is invertible as soon as `Π'` is.
`NearbyCyclesModel.isTensorRetract_of_average` proves this when the group acts through a finite
quotient. This file proves it from the following *coinvariant* property of the projector
`e_M = r_M ≫ u_M` of the first summand, which holds for infinite pro-`p` groups by continuity
of the action (SGA 4½, [Th. finitude], Lemme 3.4): on the cohomology sheaves of
`T₁ ⊗ T₂ = Lf₁'^* Ψ_{M'} A ⊗ Lf₂'^* Ψ_{N'} B`, every map invariant under the action on the first
factor is fixed by `e_M ⊗ 𝟙`. Of the projector of the second summand `a`, only its invariance
is used.

## Main results

- `CategoryTheory.isIso_of_tensor_coinvariant`: the abstract statement, in a monoidal preadditive
  category with a jointly conservative family of functors.
- `NearbyCyclesModel.isIso_map_kunnethMap_of_coinvariant`: the statement for nearby cycles.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

omit [Preadditive C] [MonoidalPreadditive C] in
/-- **Matching invariant summands across a tensor product.** Consider a square
```
  U --δ--> S₁ ⊗ S₂ --u₁ ⊗ u₂--> T₁ ⊗ T₂
  |                                |
  x                                π
  v                                v
  V --a₀--> V₀ --------m---------> V'
```
with `δ`, `u₂`, `π`, `m` invertible, a retraction `r₁` of `u₁` and a retraction `ρ₀` of `a₀`.
Let families `e₁ i` of endomorphisms of `T₁` and `e₀ i` of `V₀` be carried into each other by `π`
and `m` (through the `e i`), with `ρ₀ ≫ a₀` invariant under the `e₀ i`. If, for a jointly
conservative family of functors `H q`, every map out of `H q (T₁ ⊗ T₂)` invariant under the
`H q (e₁ i ▷ T₂)` is fixed by `H q ((r₁ ≫ u₁) ▷ T₂)`, then `x` is an isomorphism. -/
lemma isIso_of_tensor_coinvariant {ι' : Type*} {A : ι' → Type*} [∀ q, Category (A q)]
    (H : ∀ q, C ⥤ A q) (hcons : ∀ {X Y : C} (g : X ⟶ Y), (∀ q, IsIso ((H q).map g)) → IsIso g)
    {U V V₀ V' S₁ S₂ T₁ T₂ : C} {x : U ⟶ V} {a₀ : V ⟶ V₀} {m : V₀ ⟶ V'} [IsIso m]
    {δ : U ⟶ S₁ ⊗ S₂} [IsIso δ] {u₁ : S₁ ⟶ T₁} {u₂ : S₂ ⟶ T₂} [IsIso u₂] {π : T₁ ⊗ T₂ ⟶ V'}
    [IsIso π] (hsq : x ≫ a₀ ≫ m = δ ≫ (u₁ ⊗ₘ u₂) ≫ π) (r₁ : T₁ ⟶ S₁) (ρ₀ : V₀ ⟶ V)
    (hr₁ : u₁ ≫ r₁ = 𝟙 S₁) (ha₀ : a₀ ≫ ρ₀ = 𝟙 V) {ι : Type*} (e₁ : ι → (T₁ ⟶ T₁))
    (e₀ : ι → (V₀ ⟶ V₀)) (e : ι → (V' ⟶ V')) (hnat : ∀ i, e₀ i ≫ m = m ≫ e i)
    (he : ∀ i, (e₁ i ▷ T₂) ≫ π = π ≫ e i) (hinv : ∀ i, e₀ i ≫ ρ₀ ≫ a₀ = ρ₀ ≫ a₀)
    (hcoinv : ∀ q {W : A q} (φ : (H q).obj (T₁ ⊗ T₂) ⟶ W),
      (∀ i, (H q).map (e₁ i ▷ T₂) ≫ φ = φ) → (H q).map ((r₁ ≫ u₁) ▷ T₂) ≫ φ = φ) :
    IsIso x := by
  refine isIso_of_comp_eq_comp_of_coinvariant H hcons x (δ ≫ (u₁ ⊗ₘ u₂))
    ((r₁ ⊗ₘ inv u₂) ≫ inv δ) ?_ (a₀ ≫ m) (inv m ≫ ρ₀) ?_ π (by rw [hsq, Category.assoc])
    (fun i ↦ e₁ i ▷ T₂) e (fun i ↦ ⟨i, he i⟩) (fun i ↦ ?_) (fun q W φ hφ ↦ ?_)
  · rw [Category.assoc, ← Category.assoc (u₁ ⊗ₘ u₂), tensorHom_comp_tensorHom, hr₁,
      IsIso.hom_inv_id, tensorHom_id, id_whiskerRight, Category.id_comp, IsIso.hom_inv_id]
  · rw [Category.assoc, IsIso.hom_inv_id_assoc, ha₀]
  · have h : e i = inv m ≫ e₀ i ≫ m := by rw [hnat, IsIso.inv_hom_id_assoc]
    rw [h]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, reassoc_of% hinv i]
  · have h : ((r₁ ⊗ₘ inv u₂) ≫ inv δ) ≫ δ ≫ (u₁ ⊗ₘ u₂) = (r₁ ≫ u₁) ▷ T₂ := by
      rw [Category.assoc, IsIso.inv_hom_id_assoc, tensorHom_comp_tensorHom, IsIso.inv_hom_id,
        tensorHom_id]
    rw [h]
    exact hcoinv q φ hφ

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

set_option maxHeartbeats 1600000 in
-- the Künneth maps of the two products are large terms
/-- **Invariants under a pro-`p` group commute with the Künneth map**, coinvariant form (blueprint
`prose-E-10`, in the form used in the generic-slicing step of
`proposition-external-kunneth-formula-nearby-cycles`). In the square of the Künneth maps and
pullbacks (`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) for morphisms of models
`ρ_M : M' ⟶ M`, `ρ_N : N' ⟶ N`, `ρ_P : P' ⟶ P`, let families of automorphisms `σM i`, `σN i`,
`σP i` of the pullback models act on nearby cycles, with the Künneth map `Π'` of the pullback
models equivariant and the action on the second factor trivial. Suppose:
* the exchange `α_{ρ_N}(B)` is invertible;
* the exchange `α_{ρ_M}(A)` has a retraction `r_M` whose projector `r_M ≫ α_{ρ_M}`, tensored with
  the second factor, fixes on cohomology sheaves every map invariant under the action on the first
  factor (the projector onto all the invariants);
* the exchange `α_{ρ_P}(A ⊠ B)` has a retraction `r_P` whose projector is invariant.
Then the pullback `Lρ'^* Π_{A,B}` of the Künneth map is invertible as soon as `Π'` is. -/
theorem isIso_map_kunnethMap_of_coinvariant (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁')
    (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    {ι : Type*} (σM : ι → MU.Hom MU (𝟙 XU) (𝟙 XU')) (σN : ι → NU.Hom NU (𝟙 YU) (𝟙 YU'))
    (σP : ι → PU.Hom PU (𝟙 ZU) (𝟙 ZU'))
    (hequiv : ∀ i, (L((e₁')^*⟦Λ⟧).map ((σM i).autAction Λ (L((r₁)^*⟦Λ⟧).obj A)) ⊗ₘ
        L((e₂')^*⟦Λ⟧).map ((σN i).autAction Λ (L((r₂)^*⟦Λ⟧).obj B))) ≫
          kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B) =
        kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B) ≫
          (σP i).autAction Λ (L((e₁)^*⟦Λ⟧).obj (L((r₁)^*⟦Λ⟧).obj A) ⊗
            L((e₂)^*⟦Λ⟧).obj (L((r₂)^*⟦Λ⟧).obj B)))
    (hN : ∀ i, (σN i).autAction Λ (L((r₂)^*⟦Λ⟧).obj B) = 𝟙 _)
    (hNiso : IsIso ((ρN.pullbackExchange Λ).app B))
    (rM : (L((r₁)^*⟦Λ⟧) ⋙ MU.nearbyCycles Λ).obj A ⟶ (M.nearbyCycles Λ ⋙ L((r₁')^*⟦Λ⟧)).obj A)
    (hrM : (ρM.pullbackExchange Λ).app A ≫ rM = 𝟙 _)
    (hcoinv : ∀ (q : ℤ) {W : Mod (Sheaf (Scheme.ProEt.topology ZU') Ab.{u + 1})
        (condensedRingObj Λ ZU')}
      (φ : (DerivedCategory.homologyFunctor _ q).obj
        (L((e₁')^*⟦Λ⟧).obj ((MU.nearbyCycles Λ).obj (L((r₁)^*⟦Λ⟧).obj A)) ⊗
          L((e₂')^*⟦Λ⟧).obj ((NU.nearbyCycles Λ).obj (L((r₂)^*⟦Λ⟧).obj B))) ⟶ W),
      (∀ i, (DerivedCategory.homologyFunctor _ q).map
          (L((e₁')^*⟦Λ⟧).map ((σM i).autAction Λ (L((r₁)^*⟦Λ⟧).obj A)) ▷ _) ≫ φ = φ) →
        (DerivedCategory.homologyFunctor _ q).map
          (L((e₁')^*⟦Λ⟧).map (rM ≫ (ρM.pullbackExchange Λ).app A) ▷ _) ≫ φ = φ)
    (rP : (L((r)^*⟦Λ⟧) ⋙ PU.nearbyCycles Λ).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ⟶
      (P.nearbyCycles Λ ⋙ L((r')^*⟦Λ⟧)).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B))
    (hrP : (ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) ≫ rP = 𝟙 _)
    (hinvP : ∀ i, (σP i).autAction Λ
        (L((r)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)) ≫ rP ≫
          (ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B) =
        rP ≫ (ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B))
    (hK : IsIso (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) :
    IsIso (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B)) := by
  have hsq := map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁ hgen₁ htot₂
    hgen₂ hb₁ hs₁ hb₂ hs₂ A B
  have : IsIso ((PU.nearbyCycles Λ).map (Functor.OplaxMonoidal.δ L((r)^*⟦Λ⟧) _ _ ≫
      ((pullbackSquareComparison Λ (⟨hb₁⟩ : CommSq e₁ r r₁ f₁)).hom.app A ⊗ₘ
        (pullbackSquareComparison Λ (⟨hb₂⟩ : CommSq e₂ r r₂ f₂)).hom.app B))) := inferInstance
  have : IsIso ((pullbackSquareComparison Λ (⟨hs₂⟩ : CommSq e₂' r' r₂' f₂')).hom.app
      ((N.nearbyCycles Λ).obj B) ≫ L((e₂')^*⟦Λ⟧).map ((ρN.pullbackExchange Λ).app B)) :=
    inferInstance
  refine isIso_of_tensor_coinvariant (fun q ↦ DerivedCategory.homologyFunctor _ q)
    (fun g hg ↦ (DerivedCategory.isIso_iff _ g).2 hg)
    (x := L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))
    hsq (L((e₁')^*⟦Λ⟧).map rM ≫
      (pullbackSquareComparison Λ (⟨hs₁⟩ : CommSq e₁' r' r₁' f₁')).inv.app _) rP ?_ hrP
    (fun i ↦ L((e₁')^*⟦Λ⟧).map ((σM i).autAction Λ (L((r₁)^*⟦Λ⟧).obj A)))
    (fun i ↦ (σP i).autAction Λ _) (fun i ↦ (σP i).autAction Λ _)
    (fun i ↦ Hom.autAction_naturality Λ (σP i) _) (fun i ↦ ?_) hinvP (fun q W φ hφ ↦ ?_)
  · have e := congrArg L((e₁')^*⟦Λ⟧).map hrM
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at e
    simp only [Category.assoc, reassoc_of% e, Iso.hom_inv_id_app]
    rfl
  · have h := hequiv i
    simp only [hN i, CategoryTheory.Functor.map_id, tensorHom_id] at h
    exact h
  · have h := hcoinv q φ hφ
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp]
    exact h

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
