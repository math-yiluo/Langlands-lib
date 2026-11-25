/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# Coherence of the derived pullbacks on bounded constructible complexes

Let `Λ` be a commutative condensed ring, `ℓ` a prime and `k` a field of characteristic `p ≠ ℓ`.
For separated `k`-schemes of finite type, this file defines the identity isomorphisms
`L(𝟙 X)^* ≅ 𝟭` and `R(𝟙 X)_* ≅ 𝟭` of the derived pullback and pushforward on the bounded
constructible derived categories `Dᵇc(X)⟦Λ⟧`, and shows that the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`ProEtale.CondensedRing.boundedConstructibleUpperStarComp`) satisfy,
together with the identity isomorphisms, the associativity and unit laws.

The identity isomorphism of the pullback is the restriction of the identity isomorphism
`ProEtale.CondensedRing.leftDerivedUpperStarId` of the derived pullback on `D(Mod_{Λ_X})` along
the fully faithful inclusion, as for the composition isomorphisms, so that the laws are those of
the derived pullbacks (`ProEtale.CondensedRing.leftDerivedUpperStarComp_assoc_app`,
`ProEtale.CondensedRing.leftDerivedUpperStarComp_id_left_app`,
`ProEtale.CondensedRing.leftDerivedUpperStarComp_id_right_app`). The identity isomorphism of the
pushforward is its conjugate under the adjunction `L(𝟙 X)^* ⊣ R(𝟙 X)_*`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleUpperStarId`: `L(𝟙 X)^* ≅ 𝟭`.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarId`: `R(𝟙 X)_* ≅ 𝟭`.

## Main results

- `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_assoc_app`: the associativity law.
- `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_id_left_app`,
  `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_id_right_app`: the unit laws.
- `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_cocycle_aux`,
  `CategoryTheory.PullbackFamily.transport`, `CategoryTheory.PullbackFamily.commute`: consequences
  of the laws for iterated coefficient maps `LΦ^* K ⟶ K` along endomorphisms, used for the iterates
  of Weil structures and the Frobenius transport of their stalks.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.PullbackFamily

/-! ### Families of pullback functors indexed by morphisms

The lemmas of this section concern families `U` of functors indexed by the morphisms between two
objects `W` and `X` of a category, together with composition isomorphisms
`U (a ≫ b) ≅ U b ⋙ U a` and identity isomorphisms `U (𝟙) ≅ 𝟭`, such as the derived pullbacks on
bounded constructible complexes. Stating them for an abstract family keeps the morphisms and the
functors opaque, which makes the computations cheap. -/

section Transport

variable {𝒞 : Type*} [Category 𝒞] {W X : 𝒞} {DW DX : Type*} [Category DW] [Category DX]
  (UWW : (W ⟶ W) → DW ⥤ DW) (UWX : (W ⟶ X) → DX ⥤ DW) (UXX : (X ⟶ X) → DX ⥤ DX)
  (cWW : ∀ (a : W ⟶ W) (b : W ⟶ X), UWX (a ≫ b) ≅ UWX b ⋙ UWW a)
  (cWX : ∀ (a : W ⟶ X) (b : X ⟶ X), UWX (a ≫ b) ≅ UXX b ⋙ UWX a)
  (cXX : ∀ (a b : X ⟶ X), UXX (a ≫ b) ≅ UXX b ⋙ UXX a)
  (ιW : UWW (𝟙 W) ≅ 𝟭 DW)

include cWW ιW in
/-- The inverse of the composition isomorphism `U (𝟙 ≫ b) ≅ U b ⋙ U 𝟙` is the identity isomorphism
`U 𝟙 ≅ 𝟭`, up to `𝟙 ≫ b = b`, given the left unit law. -/
lemma inv_app_id_left
    (hidl : ∀ (b : W ⟶ X) (K : DX), (cWW (𝟙 W) b).hom.app K ≫ ιW.hom.app ((UWX b).obj K) =
      eqToHom (show (UWX (𝟙 W ≫ b)).obj K = _ by rw [Category.id_comp]; rfl))
    (b : W ⟶ X) (K : DX) :
    (cWW (𝟙 W) b).inv.app K =
      ιW.hom.app ((UWX b).obj K) ≫ eqToHom (by rw [Category.id_comp]; rfl) := by
  rw [← cancel_epi ((cWW (𝟙 W) b).hom.app K), Iso.hom_inv_id_app, reassoc_of% (hidl b K)]
  simp

include cWX in
/-- The composition isomorphism `U (a ≫ b) ≅ U b ⋙ U a` is compatible with transport along an
equality `a = a'` of the first morphism. -/
@[reassoc]
lemma app_eqToHom_left {a a' : W ⟶ X} (e : a = a') (b : X ⟶ X) (K : DX) :
    (cWX a b).hom.app K ≫
        eqToHom (show (UWX a).obj ((UXX b).obj K) = (UWX a').obj ((UXX b).obj K) by rw [e]) =
      eqToHom (show (UWX (a ≫ b)).obj K = (UWX (a' ≫ b)).obj K by rw [e]) ≫
        (cWX a' b).hom.app K := by
  subst e
  simp

include cWX in
/-- The composition isomorphism `U (a ≫ b) ≅ U b ⋙ U a` is compatible with transport along an
equality `b = b'` of the second morphism. -/
@[reassoc]
lemma app_map_eqToHom_right (a : W ⟶ X) {b b' : X ⟶ X} (e : b = b') (K : DX) :
    (cWX a b).hom.app K ≫ (UWX a).map (eqToHom (show (UXX b).obj K = (UXX b').obj K by rw [e])) =
      eqToHom (show (UWX (a ≫ b)).obj K = (UWX (a ≫ b')).obj K by rw [e]) ≫
        (cWX a b').hom.app K := by
  subst e
  simp

/-- Transport along an equality `a = a'` of morphisms is natural. -/
@[reassoc]
lemma map_eqToHom {a a' : W ⟶ X} (e : a = a') {K L : DX} (f : K ⟶ L) :
    (UWX a).map f ≫ eqToHom (show (UWX a).obj L = (UWX a').obj L by rw [e]) =
      eqToHom (show (UWX a).obj K = (UWX a').obj K by rw [e]) ≫ (UWX a').map f := by
  subst e
  simp

include cWW cWX cXX ιW in
/-- The transport step for stalks of iterated coefficient maps: let `x : W ⟶ X` be fixed by an
endomorphism `M` of `X`, `x ≫ M = x`, and let `ψ : U Φ K ⟶ K` and `ψ_M : U M K ⟶ K` commute, that
is `ψ ∘ U Φ ψ_M = ψ_M ∘ U M ψ` along `U (Φ ≫ M) = U (M ≫ Φ)`. Then
`U (x ≫ Φ) K ≅ U x (U Φ K) ⟶ U x K` intertwines the maps `U 𝟙 (U y K) ⟶ U y K` induced by
`ψ_M` along `𝟙 ≫ y = y ≫ M` at `y = x ≫ Φ` and at `y = x`. -/
lemma transport
    (hidl : ∀ (b : W ⟶ X) (K : DX), (cWW (𝟙 W) b).hom.app K ≫ ιW.hom.app ((UWX b).obj K) =
      eqToHom (show (UWX (𝟙 W ≫ b)).obj K = _ by rw [Category.id_comp]; rfl))
    (hassoc : ∀ (a : W ⟶ X) (b c : X ⟶ X) (K : DX),
      (cWX (a ≫ b) c).hom.app K ≫ (cWX a b).hom.app ((UXX c).obj K) =
        eqToHom (show (UWX ((a ≫ b) ≫ c)).obj K = _ by rw [Category.assoc]) ≫
          (cWX a (b ≫ c)).hom.app K ≫ (UWX a).map ((cXX b c).hom.app K))
    {x : W ⟶ X} {Φ M : X ⟶ X} (hx : x ≫ M = x) (hc : Φ ≫ M = M ≫ Φ) {K : DX}
    (ψ : (UXX Φ).obj K ⟶ K) (ψM : (UXX M).obj K ⟶ K)
    (hψ : (cXX Φ M).hom.app K ≫ (UXX Φ).map ψM ≫ ψ =
      eqToHom (show (UXX (Φ ≫ M)).obj K = _ by rw [hc]) ≫ (cXX M Φ).hom.app K ≫
        (UXX M).map ψ ≫ ψM)
    (e₁ : (UWX (𝟙 W ≫ x)).obj K = (UWX (x ≫ M)).obj K)
    (e₄ : (UWX (𝟙 W ≫ x ≫ Φ)).obj K = (UWX ((x ≫ Φ) ≫ M)).obj K) :
    (UWW (𝟙 W)).map ((cWX x Φ).hom.app K) ≫ (UWW (𝟙 W)).map ((UWX x).map ψ) ≫
      (cWW (𝟙 W) x).inv.app K ≫ eqToHom e₁ ≫ (cWX x M).hom.app K ≫ 𝟙 _ ≫
      (UWX x).map ψM ≫ 𝟙 _ =
    (cWW (𝟙 W) (x ≫ Φ)).inv.app K ≫ eqToHom e₄ ≫ (cWX (x ≫ Φ) M).hom.app K ≫ 𝟙 _ ≫
      (UWX (x ≫ Φ)).map ψM ≫ 𝟙 _ ≫ (cWX x Φ).hom.app K ≫ (UWX x).map ψ := by
  have nI₁ := ιW.hom.naturality ((cWX x Φ).hom.app K)
  have nI₂ := ιW.hom.naturality ((UWX x).map ψ)
  simp only [Functor.id_map] at nI₁ nI₂
  simp only [Category.id_comp, Category.comp_id, inv_app_id_left UWW UWX cWW ιW hidl,
    Category.assoc]
  rw [reassoc_of% nI₂, reassoc_of% nI₁, cancel_epi, eqToHom_trans_assoc, eqToHom_trans_assoc,
    map_eqToHom_assoc UWX hx.symm ψ, (cWX x M).hom.naturality_assoc ψ,
    app_eqToHom_left_assoc UWX UXX cWX hx.symm Φ K, reassoc_of% (hassoc x M Φ K),
    (cWX x Φ).hom.naturality_assoc ψM, reassoc_of% (hassoc x Φ M K)]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [hψ]
  simp only [Functor.map_comp]
  rw [app_map_eqToHom_right_assoc UWX UXX cWX x hc K, eqToHom_trans_assoc, eqToHom_trans_assoc,
    eqToHom_trans_assoc]

include cWW cWX cXX ιW in
/-- The transport step `CategoryTheory.PullbackFamily.transport`, for maps defined on an object
`K'` and read on an equal object `K` through `eqToHom`. -/
lemma transport_eqToHom
    (hidl : ∀ (b : W ⟶ X) (K : DX), (cWW (𝟙 W) b).hom.app K ≫ ιW.hom.app ((UWX b).obj K) =
      eqToHom (show (UWX (𝟙 W ≫ b)).obj K = _ by rw [Category.id_comp]; rfl))
    (hassoc : ∀ (a : W ⟶ X) (b c : X ⟶ X) (K : DX),
      (cWX (a ≫ b) c).hom.app K ≫ (cWX a b).hom.app ((UXX c).obj K) =
        eqToHom (show (UWX ((a ≫ b) ≫ c)).obj K = _ by rw [Category.assoc]) ≫
          (cWX a (b ≫ c)).hom.app K ≫ (UWX a).map ((cXX b c).hom.app K))
    {x : W ⟶ X} {Φ M : X ⟶ X} (hx : x ≫ M = x) (hc : Φ ≫ M = M ≫ Φ) {K K' : DX}
    (hK : K = K') (ψ : (UXX Φ).obj K' ⟶ K') (ψM : (UXX M).obj K' ⟶ K')
    (hψ : (cXX Φ M).hom.app K' ≫ (UXX Φ).map ψM ≫ ψ =
      eqToHom (show (UXX (Φ ≫ M)).obj K' = _ by rw [hc]) ≫ (cXX M Φ).hom.app K' ≫
        (UXX M).map ψ ≫ ψM)
    (e₁ : (UWX (𝟙 W ≫ x)).obj K = (UWX (x ≫ M)).obj K)
    (e₄ : (UWX (𝟙 W ≫ x ≫ Φ)).obj K = (UWX ((x ≫ Φ) ≫ M)).obj K)
    (a₁ : (UWW (𝟙 W)).obj ((UWX x).obj ((UXX Φ).obj K)) =
      (UWW (𝟙 W)).obj ((UWX x).obj ((UXX Φ).obj K')))
    (a₂ : (UWW (𝟙 W)).obj ((UWX x).obj K') = (UWW (𝟙 W)).obj ((UWX x).obj K))
    (a₃ : (UWX x).obj ((UXX M).obj K) = (UWX x).obj ((UXX M).obj K'))
    (a₄ : (UWX x).obj K' = (UWX x).obj K)
    (a₅ : (UWX (x ≫ Φ)).obj ((UXX M).obj K) = (UWX (x ≫ Φ)).obj ((UXX M).obj K'))
    (a₆ : (UWX (x ≫ Φ)).obj K' = (UWX (x ≫ Φ)).obj K)
    (a₇ : (UWX x).obj ((UXX Φ).obj K) = (UWX x).obj ((UXX Φ).obj K'))
    (a₈ : (UWX x).obj K' = (UWX x).obj K) :
    (UWW (𝟙 W)).map ((cWX x Φ).hom.app K) ≫ eqToHom a₁ ≫ (UWW (𝟙 W)).map ((UWX x).map ψ) ≫
      eqToHom a₂ ≫ (cWW (𝟙 W) x).inv.app K ≫ eqToHom e₁ ≫ (cWX x M).hom.app K ≫ eqToHom a₃ ≫
      (UWX x).map ψM ≫ eqToHom a₄ =
    (cWW (𝟙 W) (x ≫ Φ)).inv.app K ≫ eqToHom e₄ ≫ (cWX (x ≫ Φ) M).hom.app K ≫ eqToHom a₅ ≫
      (UWX (x ≫ Φ)).map ψM ≫ eqToHom a₆ ≫ (cWX x Φ).hom.app K ≫ eqToHom a₇ ≫
      (UWX x).map ψ ≫ eqToHom a₈ := by
  subst hK
  simp only [eqToHom_refl, Category.id_comp]
  simpa only [Category.id_comp, Category.comp_id] using
    transport UWW UWX UXX cWW cWX cXX ιW hidl hassoc hx hc ψ ψM hψ e₁ e₄

end Transport

section Commute

variable {𝒞 : Type*} [Category 𝒞] {X : 𝒞} {DX : Type*} [Category DX]
  (UXX : (X ⟶ X) → DX ⥤ DX) (cXX : ∀ (a b : X ⟶ X), UXX (a ≫ b) ≅ UXX b ⋙ UXX a)
  (ιX : UXX (𝟙 X) ≅ 𝟭 DX)

/-- The composition isomorphism `U (a ≫ b) ≅ U b ⋙ U a` of endofunctors is compatible with
transport along an equality `b = b'` of the second morphism. -/
@[reassoc]
lemma comp_app_map_eqToHom_right (a : X ⟶ X) {b b' : X ⟶ X} (e : b = b') (K : DX) :
    (cXX a b).hom.app K ≫ (UXX a).map (eqToHom (show (UXX b).obj K = (UXX b').obj K by rw [e])) =
      eqToHom (show (UXX (a ≫ b)).obj K = (UXX (a ≫ b')).obj K by rw [e]) ≫
        (cXX a b').hom.app K := by
  subst e
  simp

include ιX in
/-- The commutation of iterated coefficient maps: if `ψ_S = ψ ∘ U Φ ψ_M` for `S = Φ ≫ M` and
`ψ_{S'} = ψ_M ∘ U M ψ_1` for `S' = M ≫ Φ_1`, where `ψ_1 = ψ ∘ U Φ ψ_0` for `Φ_1 = Φ ≫ Φ_0` and
`ψ_0 : U Φ_0 K ≅ K` is the identity isomorphism for `Φ_0 = 𝟙`, and `ψ_S` and `ψ_{S'}` agree along
`S = S'`, then `ψ ∘ U Φ ψ_M = ψ_M ∘ U M ψ` along `U (Φ ≫ M) = U (M ≫ Φ)`. -/
lemma commute
    (hidr : ∀ (a : X ⟶ X) (K : DX), (cXX a (𝟙 X)).hom.app K ≫ (UXX a).map (ιX.hom.app K) =
      eqToHom (show (UXX (a ≫ 𝟙 X)).obj K = _ by rw [Category.comp_id]; rfl))
    {Φ M Φ₀ Φ₁ S S' : X ⟶ X} (hΦ₀ : Φ₀ = 𝟙 X) (e₁ : Φ₁ = Φ ≫ Φ₀) (eS : S = Φ ≫ M)
    (eS' : S' = M ≫ Φ₁) (eSS' : S = S') (hc : Φ ≫ M = M ≫ Φ) {K : DX}
    (ψ : (UXX Φ).obj K ⟶ K) (ψM : (UXX M).obj K ⟶ K) (ψ₀ : (UXX Φ₀).obj K ⟶ K)
    (ψ₁ : (UXX Φ₁).obj K ⟶ K) (ψS : (UXX S).obj K ⟶ K) (ψS' : (UXX S').obj K ⟶ K)
    (h₀ : ψ₀ = eqToHom (show (UXX Φ₀).obj K = _ by rw [hΦ₀]) ≫ ιX.hom.app K)
    (h₁ : ψ₁ = eqToHom (show (UXX Φ₁).obj K = _ by rw [e₁]) ≫ (cXX Φ Φ₀).hom.app K ≫
      (UXX Φ).map ψ₀ ≫ ψ)
    (hS : ψS = eqToHom (show (UXX S).obj K = _ by rw [eS]) ≫ (cXX Φ M).hom.app K ≫
      (UXX Φ).map ψM ≫ ψ)
    (hS' : ψS' = eqToHom (show (UXX S').obj K = _ by rw [eS']) ≫ (cXX M Φ₁).hom.app K ≫
      (UXX M).map ψ₁ ≫ ψM)
    (hSS' : ψS = eqToHom (show (UXX S).obj K = _ by rw [eSS']) ≫ ψS') :
    (cXX Φ M).hom.app K ≫ (UXX Φ).map ψM ≫ ψ =
      eqToHom (show (UXX (Φ ≫ M)).obj K = _ by rw [hc]) ≫ (cXX M Φ).hom.app K ≫
        (UXX M).map ψ ≫ ψM := by
  subst hΦ₀ e₁ h₀ h₁ eS eS' hS hS'
  have hr := hidr Φ K
  have hψ₁ : eqToHom (show (UXX (Φ ≫ 𝟙 X)).obj K = (UXX (Φ ≫ 𝟙 X)).obj K by rfl) ≫
      (cXX Φ (𝟙 X)).hom.app K ≫ (UXX Φ).map (eqToHom (show (UXX (𝟙 X)).obj K = _ by rfl) ≫
        ιX.hom.app K) ≫ ψ =
      eqToHom (show (UXX (Φ ≫ 𝟙 X)).obj K = (UXX Φ).obj K by rw [Category.comp_id]) ≫ ψ := by
    simp only [eqToHom_refl, Category.id_comp, reassoc_of% hr]
  rw [hψ₁] at hSS'
  simp only [Functor.map_comp, Category.assoc] at hSS'
  rw [comp_app_map_eqToHom_right_assoc UXX cXX M (Category.comp_id Φ), eqToHom_trans_assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hSS'
  exact hSS'

end Commute

end CategoryTheory.PullbackFamily

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The identity isomorphisms -/

section Id

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on bounded constructible
complexes of module objects over `Λ`: the restriction of
`ProEtale.CondensedRing.leftDerivedUpperStarId` along the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarId :
    boundedConstructibleUpperStar Λ ℓ (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (𝟙 X) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarId Λ X.left) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- On the ambient derived category, the identity isomorphism of the derived pullback on bounded
constructible complexes is `ProEtale.CondensedRing.leftDerivedUpperStarId`. -/
@[simp]
lemma boundedConstructibleUpperStarId_hom_app_hom (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarId Λ ℓ X).hom.app K).hom =
      (leftDerivedUpperStarId Λ X.left).hom.app K.obj := by
  simp only [Functor.id_obj, boundedConstructibleUpperStarId, Functor.whiskeringRight_obj_obj,
    Over.id_left, boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom, Iso.refl_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.FullyFaithful.preimage_comp, NatTrans.comp_app,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.id_app, Functor.comp_obj,
    ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  exact Category.id_comp _

/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the derived pushforward on bounded constructible
complexes of module objects over `ℚ̲̄_ℓ`: the conjugate of
`ProEtale.CondensedRing.boundedConstructibleUpperStarId` under the adjunctions
`L(𝟙 X)^* ⊣ R(𝟙 X)_*` and `𝟭 ⊣ 𝟭`. -/
noncomputable def boundedConstructibleLowerStarId :
    boundedConstructibleLowerStar ℓ (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X)) Adjunction.id
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).symm

end Id

/-! ### The laws -/

section Laws

variable {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

@[simp]
lemma boundedConstructibleUpperStar_map_hom (f : X ⟶ Y) {K L : Dᵇc(Y.left)⟦Λ⟧} (φ : K ⟶ L) :
    ((boundedConstructibleUpperStar Λ ℓ f).map φ).hom = L((f.left)^*⟦Λ⟧).map φ.hom :=
  rfl

@[simp]
lemma boundedConstructibleUpperStar_obj_obj (f : X ⟶ Y) (K : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStar Λ ℓ f).obj K).obj = L((f.left)^*⟦Λ⟧).obj K.obj :=
  rfl

/-- On the ambient derived category, the composition isomorphism of the derived pullbacks on
bounded constructible complexes is `ProEtale.CondensedRing.leftDerivedUpperStarComp`. -/
@[simp]
lemma boundedConstructibleUpperStarComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Dᵇc(Z.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarComp Λ ℓ f g).hom.app K).hom =
      (leftDerivedUpperStarComp Λ f.left g.left).hom.app K.obj := by
  simp [boundedConstructibleUpperStarComp, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- **Associativity** of the composition isomorphisms of the derived pullbacks on bounded
constructible complexes: the two ways of identifying `L(f ≫ g ≫ h)^*` with
`Lh^* ⋙ Lg^* ⋙ Lf^*` agree. -/
lemma boundedConstructibleUpperStarComp_assoc_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ (f ≫ g) h).hom.app K ≫
        (boundedConstructibleUpperStarComp Λ ℓ f g).hom.app
          ((boundedConstructibleUpperStar Λ ℓ h).obj K) =
      eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ f (g ≫ h)).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ f).map
          ((boundedConstructibleUpperStarComp Λ ℓ g h).hom.app K) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStar_map_hom, ObjectProperty.eqToHom_hom]
  exact leftDerivedUpperStarComp_assoc_app Λ f.left g.left h.left K.obj

/-- **Left unit law** for the composition isomorphisms of the derived pullbacks on bounded
constructible complexes. -/
lemma boundedConstructibleUpperStarComp_id_left_app (g : X ⟶ Y) (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ (𝟙 X) g).hom.app K ≫
        (boundedConstructibleUpperStarId Λ ℓ X).hom.app
          ((boundedConstructibleUpperStar Λ ℓ g).obj K) =
      eqToHom (by rw [Category.id_comp]; rfl) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStarId_hom_app_hom, ObjectProperty.eqToHom_hom]
  exact leftDerivedUpperStarComp_id_left_app Λ g.left K.obj

/-- **Right unit law** for the composition isomorphisms of the derived pullbacks on bounded
constructible complexes. -/
lemma boundedConstructibleUpperStarComp_id_right_app (f : X ⟶ Y) (K : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ f (𝟙 Y)).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ f).map
          ((boundedConstructibleUpperStarId Λ ℓ Y).hom.app K) =
      eqToHom (by rw [Category.comp_id]; rfl) := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStarId_hom_app_hom, boundedConstructibleUpperStar_map_hom,
    ObjectProperty.eqToHom_hom]
  exact leftDerivedUpperStarComp_id_right_app Λ f.left K.obj

/-! ### Iterated coefficient maps along endomorphisms -/

/-- The cocycle step for iterated coefficient maps along endomorphisms: for endomorphisms
`Φ, P, Q, R, S, T` of `X` with `S = Φ ≫ T`, `T = Q ≫ R`, `S = P ≫ R` and `P = Φ ≫ Q`, and maps
`ψ_R : LR^* K ⟶ K`, `ψ_Q : LQ^* K ⟶ K`, `ψ : LΦ^* K ⟶ K`, the two composites `LS^* K ⟶ K`
obtained by grouping `ψ ∘ LΦ^* ψ_Q ∘ LΦ^* LQ^* ψ_R` in the two possible ways agree; here
`ψ_T : LT^* K ⟶ K` is the grouping `ψ_Q ∘ LQ^* ψ_R`. -/
lemma boundedConstructibleUpperStarComp_cocycle_aux {Φ P Q R S T : X ⟶ X} (e₁ : S = Φ ≫ T)
    (e₂ : T = Q ≫ R) (e₃ : S = P ≫ R) (e₄ : P = Φ ≫ Q) {K : Dᵇc(X.left)⟦Λ⟧}
    (ψR : (boundedConstructibleUpperStar Λ ℓ R).obj K ⟶ K)
    (ψQ : (boundedConstructibleUpperStar Λ ℓ Q).obj K ⟶ K)
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K)
    (ψT : (boundedConstructibleUpperStar Λ ℓ T).obj K ⟶ K)
    (hT : ψT = eqToHom (show (boundedConstructibleUpperStar Λ ℓ T).obj K = _ by rw [e₂]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ Q R).hom.app K ≫
      (boundedConstructibleUpperStar Λ ℓ Q).map ψR ≫ ψQ) :
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ S).obj K = _ by rw [e₁]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ Φ T).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ Φ).map ψT ≫ ψ =
      eqToHom (show (boundedConstructibleUpperStar Λ ℓ S).obj K = _ by rw [e₃]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ P R).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ P).map ψR ≫
        eqToHom (show (boundedConstructibleUpperStar Λ ℓ P).obj K = _ by rw [e₄]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ Φ Q).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ Φ).map ψQ ≫ ψ := by
  subst hT e₂ e₄ e₁
  have hn := (boundedConstructibleUpperStarComp Λ ℓ Φ Q).hom.naturality ψR
  have ha := boundedConstructibleUpperStarComp_assoc_app Λ ℓ Φ Q R K
  simp only [Functor.comp_map] at hn
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn,
    ← Category.assoc ((boundedConstructibleUpperStarComp Λ ℓ (Φ ≫ Q) R).hom.app K), ha]
  simp

/-- The unit step for iterated coefficient maps along endomorphisms: for endomorphisms `P = 𝟙 X`
and `R` of `X` and a map `ψ_R : LR^* K ⟶ K`, the composite
`LR^* K ≅ L(P ≫ R)^* K ≅ LP^* LR^* K ⟶ LP^* K ≅ K` of `LP^* ψ_R` and the identity isomorphism
`L(𝟙 X)^* ≅ 𝟭` is `ψ_R`. -/
lemma boundedConstructibleUpperStarComp_id_aux {P R : X ⟶ X} (hP : P = 𝟙 X) (e : R = P ≫ R)
    {K : Dᵇc(X.left)⟦Λ⟧} (ψR : (boundedConstructibleUpperStar Λ ℓ R).obj K ⟶ K) :
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ R).obj K = _ by rw [← e]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ P R).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ P).map ψR ≫ eqToHom (by rw [hP]) ≫
        (boundedConstructibleUpperStarId Λ ℓ X).hom.app K = ψR := by
  subst hP
  have hn := (boundedConstructibleUpperStarId Λ ℓ X).hom.naturality ψR
  have hl := boundedConstructibleUpperStarComp_id_left_app Λ ℓ R K
  simp only [Functor.id_map] at hn
  simp only [eqToHom_refl, Category.id_comp]
  rw [hn, reassoc_of% hl]
  simp

/-- The unit step for iterated coefficient maps along endomorphisms, on the right: for
endomorphisms `Φ` and `P = 𝟙 X` of `X` and a map `ψ : LΦ^* K ⟶ K`, the composite
`LΦ^* K ≅ L(Φ ≫ P)^* K ≅ LΦ^* LP^* K ≅ LΦ^* K ⟶ K` of the identity isomorphism
`L(𝟙 X)^* ≅ 𝟭` and `ψ` is `ψ`. -/
lemma boundedConstructibleUpperStarComp_id_right_aux {Φ P : X ⟶ X} (hP : P = 𝟙 X)
    (e : Φ = Φ ≫ P) {K : Dᵇc(X.left)⟦Λ⟧} (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) :
    eqToHom (show (boundedConstructibleUpperStar Λ ℓ Φ).obj K = _ by rw [← e]) ≫
        (boundedConstructibleUpperStarComp Λ ℓ Φ P).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ Φ).map (eqToHom (by rw [hP]) ≫
          (boundedConstructibleUpperStarId Λ ℓ X).hom.app K) ≫ ψ = ψ := by
  subst hP
  have hr := boundedConstructibleUpperStarComp_id_right_app Λ ℓ Φ K
  simp only [eqToHom_refl, Category.id_comp]
  rw [reassoc_of% hr]
  simp

end Laws

end AlgebraicGeometry.ProEtale.CondensedRing
