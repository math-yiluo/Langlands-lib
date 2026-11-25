/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.EpiMono
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp

/-!

# The cartesian model of a morphism of models

Let `φ : M ⟶ N` be a morphism of models over `f : X ⟶ Y` and `f' : X' ⟶ Y'`, with morphism
`t : 𝒳_M ⟶ 𝒳_N` of total spaces. The *cartesian model* of `φ`
(`NearbyCyclesModel.Hom.cartesianModel`) has the total space and special fibre of `M`, and
generic fibre the base change `𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M` of the generic fibre of `N` along `t`.
The morphism `φ` factors as
```
M ──toCartesian──→ cartesianModel φ ──fromCartesian──→ N
```
where `toCartesian` (`NearbyCyclesModel.Hom.toCartesian`) is the identity on total spaces and
special fibres, and `fromCartesian` (`NearbyCyclesModel.Hom.fromCartesian`) has a cartesian
square of generic fibres.

By the composition law of the pullback exchanges, `α_φ` is a split monomorphism at `C` as soon
as `α_{fromCartesian}` is an isomorphism at `C` (a base change statement for `Rj_*` along the
cartesian square) and `α_{toCartesian}` is a split monomorphism at `L𝟙^* C` (a statement about
the change of generic fibres only):
`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_cartesian`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

/-- The **cartesian model** of a morphism of models `φ : M ⟶ N`: the total space and special
fibre of `M`, with generic fibre the base change `𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M` of the generic fibre of
`N` along the morphism of total spaces, identified with `Y` through `N`. -/
@[simps]
noncomputable def cartesianModel : NearbyCyclesModel Y X' where
  total := M.total
  generic := pullback N.j φ.total
  j := pullback.snd _ _
  i := M.i
  ε := pullback.fst _ _ ≫ N.ε

/-- The first factor `M ⟶ cartesianModel φ` of a morphism of models: the identity on total
spaces and special fibres, and the canonical map `𝒳_{M,η̄} ⟶ 𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M` on generic
fibres. -/
@[simps]
noncomputable def toCartesian : M.Hom φ.cartesianModel f (𝟙 X') where
  total := 𝟙 _
  generic := pullback.lift φ.generic M.j φ.comm_j
  comm_j := by simp
  comm_i := by simp
  comm_ε := by simp [φ.comm_ε]

/-- The second factor `cartesianModel φ ⟶ N` of a morphism of models: the morphism of total
spaces of `φ`, with the cartesian square of generic fibres. -/
@[simps]
noncomputable def fromCartesian : φ.cartesianModel.Hom N (𝟙 Y) f' where
  total := φ.total
  generic := pullback.fst _ _
  comm_j := pullback.condition
  comm_i := φ.comm_i
  comm_ε := by simp

/-- The square of generic fibres of `fromCartesian` is cartesian. -/
lemma isPullback_fromCartesian :
    IsPullback (pullback.fst N.j φ.total) (pullback.snd N.j φ.total) N.j φ.total :=
  IsPullback.of_hasPullback _ _

/-- **Pullback exchange through the cartesian model**: if the pullback exchange of
`fromCartesian` is an isomorphism at `C` and that of `toCartesian` is a split monomorphism at
`L𝟙^* C`, then the pullback exchange `α_φ` of `φ` is a split monomorphism at `C`. By the
composition law (`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`), `α_φ` factors, up to
the composition isomorphisms `c` of derived pullbacks, as
```
Lf'^* Ψ_N C ─────────────────────── α_φ(C) ───────────────────────→ Ψ_M (Lf^* C)
     │ c                                                                  │ Ψ_M c
     ▼                                                                    ▼
L𝟙^* Lf'^* Ψ_N C ──L𝟙^* α_from(C)──→ L𝟙^* Ψ_cart (L𝟙^* C) ──α_to(L𝟙^* C)──→ Ψ_M (Lf^* L𝟙^* C)
```
-/
lemma isSplitMono_pullbackExchange_app_of_cartesian'
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((φ.fromCartesian.pullbackExchange Λ).app C))
    (h₂ : IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app (L((𝟙 Y)^*⟦Λ⟧).obj C))) :
    IsSplitMono ((φ.pullbackExchange Λ).app C) := by
  have e := φ.toCartesian.pullbackExchange_comp_app_of_eq Λ φ.fromCartesian φ
    (Category.comp_id f) (Category.id_comp f') (Category.id_comp φ.total) (pullback.lift_fst _ _ _)
    C
  rw [← Iso.app_hom, ← Functor.mapIso_hom, ← Iso.eq_comp_inv] at e
  rw [e]
  infer_instance

/-- **Pullback exchange through the cartesian model**: if the pullback exchange of
`fromCartesian` is an isomorphism at `C` and that of `toCartesian` is a split monomorphism at
`C`, then the pullback exchange `α_φ` of `φ` is a split monomorphism at `C`: the hypothesis on
`α_to` is transported along `L𝟙^* C ≅ C` to the factorisation
```
Lf'^* Ψ_N C ─────────────────────── α_φ(C) ───────────────────────→ Ψ_M (Lf^* C)
     │ c                                                                  │ Ψ_M c
     ▼                                                                    ▼
L𝟙^* Lf'^* Ψ_N C ──L𝟙^* α_from(C)──→ L𝟙^* Ψ_cart (L𝟙^* C) ──α_to(L𝟙^* C)──→ Ψ_M (Lf^* L𝟙^* C)
```
of `NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_cartesian'`. -/
lemma isSplitMono_pullbackExchange_app_of_cartesian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((φ.fromCartesian.pullbackExchange Λ).app C))
    (h₂ : IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app C)) :
    IsSplitMono ((φ.pullbackExchange Λ).app C) :=
  φ.isSplitMono_pullbackExchange_app_of_cartesian' Λ C h₁
    (NatTrans.isSplitMono_app_of_iso (φ.toCartesian.pullbackExchange Λ) (Y := C)
      ((leftDerivedUpperStarId Λ Y).app C) h₂)

end Hom

variable {Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}

/-- **Split pullback exchange of a composite**: let `φ : M ⟶ N` factor as `τ : M ⟶ P` followed by
`σ : P ⟶ N` (over `f₁ ≫ f₂ = f` and `f₁' ≫ f₂' = f'`). If `α_τ` is an isomorphism at
`Lf₂^* C` and `α_σ` is a split monomorphism at `C`, then `α_φ` is a split monomorphism at `C`. -/
lemma Hom.isSplitMono_pullbackExchange_app_of_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {f₁ : X ⟶ Z} {f₁' : X' ⟶ Z'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} (τ : M.Hom P f₁ f₁')
    (σ : P.Hom N f₂ f₂') (φ : M.Hom N f f') (h : f₁ ≫ f₂ = f) (h' : f₁' ≫ f₂' = f')
    (htot : τ.total ≫ σ.total = φ.total) (hgen : τ.generic ≫ σ.generic = φ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((τ.pullbackExchange Λ).app (L((f₂)^*⟦Λ⟧).obj C)))
    (h₂ : IsSplitMono ((σ.pullbackExchange Λ).app C)) :
    IsSplitMono ((φ.pullbackExchange Λ).app C) := by
  have e := τ.pullbackExchange_comp_app_of_eq Λ σ φ h h' htot hgen C
  rw [← Iso.app_hom, ← Functor.mapIso_hom, ← Iso.eq_comp_inv] at e
  rw [e]
  infer_instance

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
