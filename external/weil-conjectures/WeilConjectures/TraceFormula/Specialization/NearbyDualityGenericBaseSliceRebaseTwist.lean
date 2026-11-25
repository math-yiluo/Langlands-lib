/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceRebase
public import WeilConjectures.Tactic.TransportExact

/-!

# The twist equation of the generic slice is invariant under re-basing

For a proper trait model `M` over the generic base `(F, X₁, ι)` with proper `X₁` and full generic
fibre, the twist equation of the generic slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`) for `M` follows from the
same equation for the re-based model `M'` over `(η, X₁,η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_rebase`).

* `NearbyCyclesModel.pullbackExchange_app_comp_map_compOfEq_of_rebase`: the ambient exchange
  factorization, for morphisms of models `φ : N ⟶ M`, `φ' : N ⟶ M'` and `ψ : M' ⟶ M` over the
  identity of the special fibre with `φ = φ' ≫ ψ`.
* `NearbyCyclesModel.liftExchange_comp_map_compIso_of_rebase`: its restriction to bounded
  constructible complexes, for exchanges given as equal to `NearbyCyclesModel.liftExchange`.
* `NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange_app_comp_map_rebase`: the
  exchange factorization `α ≫ Ψ_{M''}(E) = p^*(ρ) ≫ α'` of the generic slice.

## Implementation notes

The factorization is proved for arbitrary schemes over fields and arbitrary morphisms of models,
and only instantiated at the generic slice: the kernel then never compares the two presentations
`Spec (.of (FractionRing _))` (`OreLocalization.instCommRing` and `Field.toCommRing`) of the base
of the slice, nor the slices of `M` and of `M'`, inside derived categories. In the general lemma
the bounded constructible statement is reduced to the ambient one by rewriting (the goal keeps the
bounded constructible spelling of its objects) and closed by `transport_exact`. The generic slice
of `M'` is the generic slice of `M` up to the implicit arguments `M` and `M'`; the re-based slice
exchange is compared with `NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange` of
`M'` once, by `rfl` (`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseGenericSliceExchange_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Abstract

private lemma comp_eq_of_component_hom_eq {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y Y' Z : P.FullSubcategory} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ Y'} {g' : Y' ⟶ Z}
    {a : X.obj ⟶ Y.obj} {b : Y.obj ⟶ Z.obj}
    {a' : X.obj ⟶ Y'.obj} {b' : Y'.obj ⟶ Z.obj}
    (hf : f.hom = a) (hg : g.hom = b) (hf' : f'.hom = a') (hg' : g'.hom = b')
    (h : a ≫ b = a' ≫ b') : f ≫ g = f' ≫ g' := by
  apply ObjectProperty.hom_ext
  exact (congrArg₂ (· ≫ ·) hf hg).trans (h.trans (congrArg₂ (· ≫ ·) hf' hg').symm)

/-- `NearbyCyclesModel.exists_twist_of_rebase` with the twist equation for a transformation `α''`
equal to `α'`. -/
lemma exists_twist_of_rebase_of_eq {DX DXη DS Ds D₂ : Type*} [Category DX] [Category DXη]
    [Category DS] [Category Ds] [Category D₂] {ΨM : DX ⥤ DS} {ΨM' : DXη ⥤ DS}
    {Pπ : DX ⥤ DXη} {P : DS ⥤ Ds} {Ψ : D₂ ⥤ Ds} {Cc : DX ⥤ D₂} {C' : DXη ⥤ D₂} {ω : DX}
    {ωη : DXη} {ω' : DS} {W : D₂} {V Z : Ds}
    (θ : ΨM.obj ω ⟶ ω') (θ' : ΨM'.obj ωη ⟶ ω') (ρ : ΨM ⟶ Pπ ⋙ ΨM') (φ : Pπ.obj ω ⟶ ωη)
    [IsIso φ] (hθ : θ = ρ.app ω ≫ ΨM'.map φ ≫ θ') (α : ΨM ⋙ P ⟶ Cc ⋙ Ψ)
    (α' α'' : ΨM' ⋙ P ⟶ C' ⋙ Ψ) (hα' : α' = α'') (E : Cc.obj ω ≅ C'.obj (Pπ.obj ω))
    (hα : α.app ω ≫ Ψ.map E.hom = P.map (ρ.app ω) ≫ α'.app (Pπ.obj ω)) (κ : Ψ.obj W ≅ Z)
    (t : Z ⟶ V)
    (H : ∃ (u : C'.obj ωη ≅ W) (v : P.obj ω' ≅ V),
      P.map θ' ≫ v.hom = α''.app ωη ≫ Ψ.map u.hom ≫ κ.hom ≫ t) :
    ∃ (u : Cc.obj ω ≅ W) (v : P.obj ω' ≅ V),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ κ.hom ≫ t := by
  subst hα'
  exact exists_twist_of_rebase θ θ' ρ φ hθ α α' E hα κ t H

end Abstract

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z₁ Zη Z₀ Z₂ W₀ : Scheme.{u}} {M₁ : NearbyCyclesModel Z₁ Z₀} {Mη : NearbyCyclesModel Zη Z₀}
  {N₂ : NearbyCyclesModel Z₂ W₀} {c : Z₂ ⟶ Z₁} {c' : Z₂ ⟶ Zη} {π : Zη ⟶ Z₁} {p : W₀ ⟶ Z₀}

/-- **The exchange factorization of a composite** (ambient): for morphisms of models
`φ : N ⟶ M` over `c`, `φ' : N ⟶ M'` over `c'` and `ψ : M' ⟶ M` over `π` and the identity of
the special fibre, with `φ = φ' ≫ ψ` and `c = c' ≫ π`, the pullback exchange of `φ` followed by
`Lc^* ≅ Lπ^* ⋙ Lc'^*` is `p^*` of the exchange of `ψ` (through `L𝟙^* ≅ 𝟭`) followed by the
pullback exchange of `φ'`. -/
lemma pullbackExchange_app_comp_map_compOfEq_of_rebase (φ : N₂.Hom M₁ c p)
    (φ' : N₂.Hom Mη c' p) (ψ : Mη.Hom M₁ π (𝟙 Z₀)) (hc : c' ≫ π = c)
    (htot : φ'.total ≫ ψ.total = φ.total) (hgen : φ'.generic ≫ ψ.generic = φ.generic)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology Z₁) Ab.{u + 1}) (condensedRingObj Λ Z₁))) :
    (φ.pullbackExchange Λ).app C ≫
        (N₂.nearbyCycles Λ).map ((leftDerivedUpperStarCompOfEq Λ hc).hom.app C) =
      L((p)^*⟦Λ⟧).map (ψ.specialIdExchange Λ C) ≫
        (φ'.pullbackExchange Λ).app (L((π)^*⟦Λ⟧).obj C) := by
  have hp : p ≫ 𝟙 Z₀ = p := Category.comp_id _
  have key := φ'.pullbackExchange_comp_app_of_eq Λ ψ φ hc hp htot hgen C
  have hK := leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId Λ hp
    ((M₁.nearbyCycles Λ).obj C)
  exact rebase_exchange_aux _ _ _ _ _ _ C _ rfl _ hK key

end Ambient

section BoundedConstructible

variable {ℓ : ℕ} [Fact ℓ.Prime] {k₁ kη k₀ k₂ K₀ : Type u} [Field k₁] [Field kη] [Field k₀]
  [Field k₂] [Field K₀]
  {Z₁ : Over (Spec (.of k₁))} {Zη : Over (Spec (.of kη))} {Z₀ : Over (Spec (.of k₀))}
  {Z₂ : Over (Spec (.of k₂))} {W₀ : Over (Spec (.of K₀))}
  {M₁ : NearbyCyclesModel Z₁.left Z₀.left} {Mη : NearbyCyclesModel Zη.left Z₀.left}
  {N₂ : NearbyCyclesModel Z₂.left W₀.left} {c : Z₂.left ⟶ Z₁.left} {c' : Z₂.left ⟶ Zη.left}
  {π : Zη.left ⟶ Z₁.left} {p : W₀.left ⟶ Z₀.left}

private lemma boundedConstructibleNearbyCycles_map_hom' {X X' : Scheme.{u}}
    {N : NearbyCyclesModel X X'}
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {A B : Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    ((boundedConstructibleNearbyCycles hN).map f).hom =
      (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map f.hom :=
  rfl

private lemma boundedConstructibleUpperStarOfMapCompIso_hom_hom (hc : c' ≫ π = c)
    (A : Dᵇc(Z₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMapCompIso ℓ hc A).hom.hom =
      (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hc).hom.app A.obj :=
  rfl

/-- **The exchange factorization of a composite** on bounded constructible complexes: for
morphisms of models `φ = φ' ≫ ψ` as in
`NearbyCyclesModel.pullbackExchange_app_comp_map_compOfEq_of_rebase`, and exchanges `α`, `α'`,
`ρ` equal to the restrictions of the pullback exchanges of `φ`, `φ'` and of `ψ` (through
`L𝟙^* ≅ 𝟭`), `α ≫ Ψ_N(E) = p^*(ρ) ≫ α'` for the composition isomorphism
`E : c^* ≅ c'^* π^*`. -/
lemma liftExchange_comp_map_compIso_of_rebase (φ : N₂.Hom M₁ c p) (φ' : N₂.Hom Mη c' p)
    (ψ : Mη.Hom M₁ π (𝟙 Z₀.left)) (hc : c' ≫ π = c) (htot : φ'.total ≫ ψ.total = φ.total)
    (hgen : φ'.generic ≫ ψ.generic = φ.generic)
    (hM₁ : M₁.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hMη : Mη.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hN₂ : N₂.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : boundedConstructibleNearbyCycles hM₁ ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Z₀) (Y := W₀) p ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := Z₁) (Y := Z₂) c ⋙
        boundedConstructibleNearbyCycles hN₂)
    (hα : α = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hM₁ K.obj K.property) (fun K ↦ hN₂ K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ p K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ c K.obj K.property))
    (α' : boundedConstructibleNearbyCycles hMη ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := Z₀) (Y := W₀) p ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := Zη) (Y := Z₂) c' ⋙
        boundedConstructibleNearbyCycles hN₂)
    (hα' : α' = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ'.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hMη K.obj K.property) (fun K ↦ hN₂ K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ p K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ c' K.obj K.property))
    (ρ : boundedConstructibleNearbyCycles hM₁ ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := Z₁) (Y := Zη) π ⋙
        boundedConstructibleNearbyCycles hMη)
    (hρ : ∀ A, (ρ.app A).hom = ψ.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
    (A : Dᵇc(Z₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    α.app A ≫ (boundedConstructibleNearbyCycles hN₂).map
        (boundedConstructibleUpperStarOfMapCompIso ℓ hc A).hom =
      (boundedConstructibleUpperStarOfMap ℓ (X := Z₀) (Y := W₀) p).map (ρ.app A) ≫
        α'.app ((boundedConstructibleUpperStarOfMap ℓ (X := Z₁) (Y := Zη) π).obj A) := by
  subst hα hα'
  -- Compute the components separately, so no rewrite motive contains the whole square.
  have hE := (boundedConstructibleNearbyCycles_map_hom' hN₂
      (boundedConstructibleUpperStarOfMapCompIso ℓ (X := Z₁) (Y := Z₂) (Z := Zη) hc A).hom).trans
      (congrArg (N₂.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        (boundedConstructibleUpperStarOfMapCompIso_hom_hom (Zη := Zη) (Z₂ := Z₂) hc A))
  have hP := (congrArg (·.hom)
      (boundedConstructibleUpperStarOfMap_map ℓ (X := Z₀) (Y := W₀) p (ρ.app A))).trans
      (congrArg L((p)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map (hρ A))
  refine comp_eq_of_component_hom_eq (liftExchange_app_hom _ _ _ _ _ _) hE hP
    (liftExchange_app_hom _ _ _ _ _ _) ?_
  transport_exact pullbackExchange_app_comp_map_compOfEq_of_rebase _ φ φ' ψ hc htot hgen A.obj

end BoundedConstructible

section GenericSlice

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfGenericBase

section Instances

variable {K : Type u} [Field K] [Algebra k' K] (x : K) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-! The generic slice of the re-based model is that of the model. -/

instance [LocallyOfFiniteType (genericSliceBase x hb).hom] :
    LocallyOfFiniteType (genericSliceBase (M := h.rebase) x hb).hom :=
  ‹LocallyOfFiniteType (genericSliceBase x hb).hom›

instance [QuasiCompact (genericSliceBase x hb).hom] :
    QuasiCompact (genericSliceBase (M := h.rebase) x hb).hom :=
  ‹QuasiCompact (genericSliceBase x hb).hom›

instance [IsSeparated (genericSliceBase x hb).hom] :
    IsSeparated (genericSliceBase (M := h.rebase) x hb).hom :=
  ‹IsSeparated (genericSliceBase x hb).hom›

instance [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom] :
    LocallyOfFiniteType (baseChangeSpecial (M := h.rebase) b (traitSlice x)).hom :=
  ‹LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom›

instance [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom] :
    QuasiCompact (baseChangeSpecial (M := h.rebase) b (traitSlice x)).hom :=
  ‹QuasiCompact (baseChangeSpecial b (traitSlice x)).hom›

instance [IsSeparated (baseChangeSpecial b (traitSlice x)).hom] :
    IsSeparated (baseChangeSpecial (M := h.rebase) b (traitSlice x)).hom :=
  ‹IsSeparated (baseChangeSpecial b (traitSlice x)).hom›

end Instances

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom] in
/-- **The slice exchange and re-basing** on bounded constructible complexes: the slice exchange
`α` of `M`, followed by `Ψ_{M''}` of `E : c^* ≅ c'^* π^*`, is `p^*` of the re-basing exchange
followed by the slice exchange `α'` of the re-based model. -/
lemma genericSliceExchange_app_comp_map_rebase
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A ≫
      (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map
        (boundedConstructibleUpperStarOfMapCompIso ℓ (X := X₁) (Z := genericBaseChange X₁ ι)
          (Y := genericSliceBase (M := M) (traitSliceCoord k') hb)
          (h.genericSliceBaseMap_eq_rebase (traitSliceCoord k') hb).symm A).hom =
    (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map ((h.rebaseExchange ℓ).app A) ≫
      (rebaseGenericSliceExchange ℓ h hb).app
        ((genericBaseChangeUpperStar ℓ (X₁ := X₁) (ι := ι)).obj A) := by
  have key := liftExchange_comp_map_compIso_of_rebase (h.genericSliceHom (traitSliceCoord k') hb)
    (h.rebaseGenericSliceHom (traitSliceCoord k') hb) h.rebaseHom
    (h.genericSliceBaseMap_eq_rebase (traitSliceCoord k') hb).symm (Category.comp_id _)
    (Category.comp_id _) (h.preservesBoundedConstructible (ℓ := ℓ))
    (h.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ))
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) rfl
    (rebaseGenericSliceExchange ℓ h hb) rfl (h.rebaseExchange ℓ)
    (fun _ ↦ by unfold rebaseExchange; exact ObjectProperty.homMk_hom _) A
  transport_exact key

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries k'))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ)] [LocallyOfFiniteType X₁.hom]
  [QuasiCompact X₁.hom] [IsSeparated X₁.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom] in
/-- The re-based slice exchange is the slice exchange of the re-based model. -/
lemma rebaseGenericSliceExchange_eq :
    rebaseGenericSliceExchange ℓ h hb =
      genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase hb :=
  rfl

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-- **The twist equation of the generic slice and re-basing**: for a proper trait model `M` over
the generic base `(F, X₁, ι)` with proper `X₁` and full generic fibre, the twist equation of
`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` for `M` follows from the
same equation for the re-based model over `(η, X₁,η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isTraitModelOfGenericBase_rebase`), with
`u = E ≪≫ c'^*(φ) ≪≫ u'` (`NearbyCyclesModel.exists_twist_of_rebase`). -/
theorem exists_iso_map_θ_eq_twist_of_rebase (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (H : ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase
          hb).obj (dualizingComplex ℓ (genericBaseChange X₁ ι)) ≅
        dualizingComplex ℓ (genericSliceBase (M := h.rebase) (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ
            (genericSliceBase (M := h.rebase) (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase
          hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial (M := h.rebase) b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial (M := h.rebase) b (traitSlice (traitSliceCoord k'))) 0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase hb).map
          (D.θ h.isTraitModelOfGenericBase_rebase) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase hb).app
            (dualizingComplex ℓ (genericBaseChange X₁ ι)) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase
            hb).map u.hom ≫
          (genericSliceTwistIso ℓ h.isTraitModelOfGenericBase_rebase hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (M := h.rebase) (traitSliceCoord k')
            hb h.isTraitModelOfGenericBase_rebase.isTraitModelOver) ▷ _) :
    ∃ (u : (genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) ≫ v.hom =
        (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
          (genericSliceTwistIso ℓ h hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            h.isTraitModelOver) ▷ _ := by
  have := isProper_toPoint_genericBaseChange (X₁ := X₁) (ι := ι)
  have := isIso_dualizingComplexBaseChange_genericBaseChange X₁ ι ℓ
  exact exists_twist_of_rebase_of_eq (D.θ h) (D.θ h.isTraitModelOfGenericBase_rebase)
    (h.rebaseExchange ℓ) _ (D.θ_eq_rebase_of_isProper h hgen)
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) (rebaseGenericSliceExchange ℓ h hb)
    (genericSliceExchange (traitSliceCoord k') ℓ h.isTraitModelOfGenericBase_rebase hb)
    (rebaseGenericSliceExchange_eq ℓ h hb)
    (boundedConstructibleUpperStarOfMapCompIso ℓ (X := X₁) (Z := genericBaseChange X₁ ι)
      (Y := genericSliceBase (M := M) (traitSliceCoord k') hb)
      (h.genericSliceBaseMap_eq_rebase (traitSliceCoord k') hb).symm _)
    (by transport_exact genericSliceExchange_app_comp_map_rebase ℓ h hb (dualizingComplex ℓ X₁))
    _ _ H

end IsTraitModelOfGenericBase

end GenericSlice

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
