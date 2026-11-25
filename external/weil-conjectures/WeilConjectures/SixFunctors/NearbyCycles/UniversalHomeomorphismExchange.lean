/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeGenericUnit
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit

/-!

# Pullback exchanges along universal homeomorphisms of generic fibres

A morphism of models which is the identity on total spaces and special fibres and a universal
homeomorphism on geometric generic fibres has an invertible pullback exchange
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic`): the exchange
is `Li^* Rj_*` of the unit of `Lg^* ⊣ Rg_*`
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`), which is invertible for a universal
homeomorphism `g` by topological invariance. The file also records two consequences of the square
and composition laws of pullback exchanges
(`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square_of_isIso`,
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' G : Scheme.{u}}

/-- **The pullback exchange along a universal homeomorphism of generic fibres is invertible.** For
a morphism of models `φ` over the identities with `φ.total = 𝟙` and `φ.generic = g` a universal
homeomorphism, from the model with generic fibre `G`, `j = g ≫ j_N` and `ε = e`. -/
theorem Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic (N : NearbyCyclesModel X X')
    (g : G ⟶ N.generic) [IsUniversalHomeomorphism g] (e : G ⟶ X) (he : g ≫ N.ε = e)
    (φ : Hom ⟨N.total, G, g ≫ N.j, N.i, e⟩ N (𝟙 X) (𝟙 X')) (ht : φ.total = 𝟙 _)
    (hg : φ.generic = g) : IsIso (φ.pullbackExchange Λ) := by
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism Λ g
  have (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : IsIso ((φ.pullbackExchange Λ).app A) := by
    rw [Hom.pullbackExchange_app_of_total_eq_id Λ N g e he φ ht hg A]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **The pullback exchange along a universal homeomorphism of generic fibres, over any map of the
identified schemes.** Let `ρ : M ⟶ N` be a morphism of models over `f` and the identity of special
fibres, where `M` has the total space and special fibre of `N`, generic fibre `G` with
`j_M = r ≫ j_N` for a universal homeomorphism `r : G ⟶ 𝒳_{N,η̄}`, and `ρ` is the identity on total
spaces and `r` on generic fibres. Then the pullback exchange of `ρ` is invertible: `ρ` factors
through the model with `ε = r ≫ ε_N` by a morphism with invertible components and
`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic`. -/
theorem Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism' {Z : Scheme.{u}}
    (N : NearbyCyclesModel X X') (r : G ⟶ N.generic) [IsUniversalHomeomorphism r]
    {j' : G ⟶ N.total} (hj : j' = r ≫ N.j) {ε' : G ⟶ Z} {f : Z ⟶ X}
    (ρ : Hom ⟨N.total, G, j', N.i, ε'⟩ N f (𝟙 X')) (ht : ρ.total = 𝟙 _) (hg : ρ.generic = r)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((ρ.pullbackExchange Λ).app C) := by
  subst hj
  let ρ₁ : Hom ⟨N.total, G, r ≫ N.j, N.i, ε'⟩ ⟨N.total, G, r ≫ N.j, N.i, r ≫ N.ε⟩ f (𝟙 X') :=
    { total := 𝟙 _
      generic := 𝟙 _
      comm_j := by simp
      comm_i := by simp
      comm_ε := by
        have := ρ.comm_ε
        rw [hg] at this
        simpa using this }
  let ρ₂ : Hom ⟨N.total, G, r ≫ N.j, N.i, r ≫ N.ε⟩ N (𝟙 X) (𝟙 X') :=
    { total := 𝟙 _
      generic := r
      comm_j := by simp
      comm_i := by simp
      comm_ε := by simp }
  have h₁ : IsIso (ρ₁.pullbackExchange Λ) := ρ₁.isIso_pullbackExchange_of_isIso Λ
  have h₂ : IsIso (ρ₂.pullbackExchange Λ) :=
    Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic Λ N r _ rfl ρ₂ rfl rfl
  have w := ρ₁.pullbackExchange_comp_app_of_eq Λ ρ₂ ρ (Category.comp_id f) (Category.id_comp _)
    (by rw [ht]; exact Category.id_comp _) (by rw [hg]; exact Category.id_comp _) C
  have : IsIso ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X'))).hom.app
      ((N.nearbyCycles Λ).obj C) ≫ L((𝟙 X')^*⟦Λ⟧).map ((ρ₂.pullbackExchange Λ).app C) ≫
        (ρ₁.pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj C)) := inferInstance
  rw [← w] at this
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this

/-- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism'` for a source
model `M` which is only equal to the model with the total space and special fibre of `N` (so that
the statement can be applied to models which are definitionally, but not syntactically, of that
form without unifying large pullback exchanges). -/
theorem Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq {Z : Scheme.{u}}
    (N : NearbyCyclesModel X X') (r : G ⟶ N.generic) [IsUniversalHomeomorphism r]
    {ε' : G ⟶ Z} {f : Z ⟶ X} (M : NearbyCyclesModel Z X')
    (hM : M = ⟨N.total, G, r ≫ N.j, N.i, ε'⟩) (ρ : M.Hom N f (𝟙 X'))
    (ht : HEq ρ.total (𝟙 N.total)) (hg : HEq ρ.generic r)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((ρ.pullbackExchange Λ).app C) := by
  subst hM
  exact Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism' Λ N r rfl ρ (eq_of_heq ht)
    (eq_of_heq hg) C

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}

/-- **The pullback exchange through a square with invertible sides, restricted along the special
fibre map**: for a commutative square of morphisms of models `φ₀ : P ⟶ M`, `ψ : M ⟶ M₁`,
`ψ' : P ⟶ P₁`, `φ₁ : P₁ ⟶ M₁`, if the pullback exchanges of `ψ` at `C`, of `ψ'` at `Le^* C` and
of `φ₀` at `Lg^* C` are invertible, then the pullback of the exchange of `φ₁` at `C` along the
special fibre map `k'` of `ψ'` is invertible. This is the square law
(`NearbyCyclesModel.Hom.pullbackExchange_square`). -/
theorem Hom.isIso_map_pullbackExchange_app_of_square_of_isIso (φ₀ : P.Hom M f₀ f₀')
    (ψ : M.Hom M₁ g g') (ψ' : P.Hom P₁ k k') (φ₁ : P₁.Hom M₁ e e')
    (htot : φ₀.total ≫ ψ.total = ψ'.total ≫ φ₁.total)
    (hgen : φ₀.generic ≫ ψ.generic = ψ'.generic ≫ φ₁.generic) (hb : f₀ ≫ g = k ≫ e)
    (hs : f₀' ≫ g' = k' ≫ e')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁)))
    (hψ : IsIso ((ψ.pullbackExchange Λ).app C))
    (hψ' : IsIso ((ψ'.pullbackExchange Λ).app (L((e)^*⟦Λ⟧).obj C)))
    (hφ₀ : IsIso ((φ₀.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C))) :
    IsIso (L((k')^*⟦Λ⟧).map ((φ₁.pullbackExchange Λ).app C)) := by
  have w := Hom.pullbackExchange_square Λ φ₀ ψ ψ' φ₁ htot hgen hb hs C
  have h : IsIso ((pullbackSquareComparison Λ (⟨hs⟩ : CommSq f₀' k' g' e')).hom.app
      ((M₁.nearbyCycles Λ).obj C) ≫ L((f₀')^*⟦Λ⟧).map ((ψ.pullbackExchange Λ).app C) ≫
        (φ₀.pullbackExchange Λ).app (L((g)^*⟦Λ⟧).obj C)) := inferInstance
  rw [w] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h

/-- The pullback exchange of a composite of morphisms of models with invertible pullback exchanges
is invertible. -/
theorem Hom.isIso_pullbackExchange_app_comp {Y Y' : Scheme.{u}} {N : NearbyCyclesModel Y Y'}
    {f : Z ⟶ X} {f' : Z' ⟶ X'} {h : X ⟶ Y} {h' : X' ⟶ Y'} (φ : P.Hom M f f') (ψ : M.Hom N h h')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hψ : IsIso ((ψ.pullbackExchange Λ).app C))
    (hφ : IsIso ((φ.pullbackExchange Λ).app (L((h)^*⟦Λ⟧).obj C))) :
    IsIso (((φ.comp ψ).pullbackExchange Λ).app C) := by
  have h₁ := φ.pullbackExchange_comp_app Λ ψ C
  have h₂ : IsIso ((leftDerivedUpperStarComp Λ f' h').hom.app ((N.nearbyCycles Λ).obj C) ≫
      L((f')^*⟦Λ⟧).map ((ψ.pullbackExchange Λ).app C) ≫
        (φ.pullbackExchange Λ).app (L((h)^*⟦Λ⟧).obj C)) := inferInstance
  rw [← h₁] at h₂
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h₂

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
