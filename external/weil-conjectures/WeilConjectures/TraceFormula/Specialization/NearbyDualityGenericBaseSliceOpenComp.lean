/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceOpen
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
import WeilConjectures.Tactic.TransportExact

/-!

# The twist equation of the generic slice from an ambient model without coordinate

Let `M` be an open sub-model of a trait model `M_c` over the generic base, through
`φ : M ⟶ M_c` over open immersions `j : X₁ ⟶ X_c`, `j' : X' ⟶ X'_c`, and let `b` be a coordinate
of `M` only (`M_c` need not have one). The generic slice `M''` of `M` along `b` maps to `M_c` by
the composite `s = s_M ≫ φ` of the slice projection and `φ`, over `c ≫ j` and `p ≫ j'`; write
`α_c : (p ≫ j')^* Ψ_{M_c} ⟶ Ψ_{M''} (c ≫ j)^*` for its pullback exchange
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchangeComp`).

The twist equation of the generic slice of `M`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`) follows from the
*twist equation of `M_c` along `s`*:
`(p ≫ j')^* θ_{M_c} ≫ v = α_c ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel_comp`).

This is the shape needed for the open sub-models `V` of a proper model `M_c` with a coordinate
`b : V ⟶ 𝔸¹_S`: extending `b` to a proper `b̄ : V_c ⟶ ℙ¹_S` on the closure of its graph, the
generic slice of `W = b̄⁻¹(𝔸¹_S)` is `V_c ×_{ℙ¹_S} Spec K⟦t⟧`, proper over the slice trait, and
the twist equation of `V_c` along `W'' ⟶ W ⟶ V_c` is produced from the composition law of
`θ` along `b̄` and the twist equation for `ℙ¹_S` along `Spec K⟦t⟧ ⟶ ℙ¹_S`
(`NearbyCyclesModel.exists_twist_of_slice_of_composition_law`). The present file passes from
`V_c` to `W`; `W ⊇ V` is then
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`.

The pullback exchange of a morphism of models over morphisms of schemes over possibly different
fields, on bounded constructible complexes, is
`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchangeOfMap`.

## Proof

`NearbyCyclesModel.exists_twist_of_openSubmodel` for the open sub-model `φ` and, on the slices,
the identity morphism of `M''` (an open immersion): the dualizing map of `M` is the restriction of
that of `M_c` (open restriction), that of `M''` is its own restriction along the identity, the
slice exchanges are compatible by the square law of the pullback exchanges
(`NearbyCyclesModel.boundedConstructiblePullbackExchange_square`, for the square
`s_M ≫ φ = 𝟙 ≫ s`), and so are the twist isomorphisms
(`NearbyCyclesModel.Hom.liftExchange_zeroTwistIso` for the identity).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

section OfMap

variable (ℓ : ℕ) [Fact ℓ.Prime] {kX kX' kY kY' : Type u} [Field kX] [Field kX'] [Field kY]
  [Field kY'] [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kX').Prime]
  [Fact (ringChar kX' ≠ ℓ)] [Fact (ringChar kY).Prime] [Fact (ringChar kY ≠ ℓ)]
  [Fact (ringChar kY').Prime] [Fact (ringChar kY' ≠ ℓ)]
  {X : Over (Spec (.of kX))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of kX'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {Y : Over (Spec (.of kY))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of kY'))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : Y.left ⟶ X.left} {f' : Y'.left ⟶ X'.left}

/-- The pullback exchange `Lf'^* Ψ_M ⟶ Ψ_N Lf^*` of a morphism of models `φ : N ⟶ M` over
arbitrary morphisms of schemes `f`, `f'` (not necessarily over a common base field), on bounded
constructible complexes. -/
noncomputable def Hom.boundedConstructiblePullbackExchangeOfMap (φ : N.Hom M f f')
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f' ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f ⋙
        boundedConstructibleNearbyCycles hN :=
  liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
    (PY' := boundedConstructible _) (PX' := boundedConstructible _)
    (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
    (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f K.obj K.property)

omit [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kX').Prime]
  [Fact (ringChar kX' ≠ ℓ)] [Fact (ringChar kY).Prime] [Fact (ringChar kY ≠ ℓ)]
  [Fact (ringChar kY').Prime] [Fact (ringChar kY' ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
lemma Hom.boundedConstructiblePullbackExchangeOfMap_eq_liftExchange (φ : N.Hom M f f')
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    φ.boundedConstructiblePullbackExchangeOfMap ℓ hN hM =
      liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _)
        (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f K.obj K.property) :=
  rfl

omit [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kX').Prime]
  [Fact (ringChar kX' ≠ ℓ)] [Fact (ringChar kY).Prime] [Fact (ringChar kY ≠ ℓ)]
  [Fact (ringChar kY').Prime] [Fact (ringChar kY' ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The components of `NearbyCyclesModel.liftExchange` of any transformation
`α : Ψ_M ⋙ Lf'^* ⟶ Lf^* ⋙ Ψ_N`, with `α` abstract so that its definition is never unfolded. -/
private lemma liftExchangeOfMap_app_hom_aux
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        L((f')^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f K.obj K.property) :
      boundedConstructibleNearbyCycles hM ⋙
          boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') f' ⟶
        boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) f ⋙
          boundedConstructibleNearbyCycles hN).app A).hom = α.app A.obj :=
  liftExchange_app_hom _ _ _ _ _ A

omit [Fact (ringChar kX).Prime] [Fact (ringChar kX ≠ ℓ)] [Fact (ringChar kX').Prime]
  [Fact (ringChar kX' ≠ ℓ)] [Fact (ringChar kY).Prime] [Fact (ringChar kY ≠ ℓ)]
  [Fact (ringChar kY').Prime] [Fact (ringChar kY' ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
lemma Hom.boundedConstructiblePullbackExchangeOfMap_app_hom (φ : N.Hom M f f')
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructiblePullbackExchangeOfMap ℓ hN hM).app A).hom =
      (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A.obj := by
  rw [Hom.boundedConstructiblePullbackExchangeOfMap_eq_liftExchange]
  exact liftExchangeOfMap_app_hom_aux ℓ hN hM _ A

end OfMap

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
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
  {Xc : Over (Spec (.of F))} [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom]
  [IsSeparated Xc.hom] {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom]
  [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom] {Mc : NearbyCyclesModel Xc.left Xc'.left}
  {qc : Mc.total ⟶ trait k'} {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}
  (hc : Mc.IsTraitModelOfGenericBase Xc ι qc gc)
  (j : X₁ ⟶ Xc) (j' : X' ⟶ Xc') (φ : M.Hom Mc j.left j'.left)

namespace IsTraitModelOfGenericBase

/-- The pullback `(p ≫ j')^* : Dᵇc(X'_c) ⥤ Dᵇc(𝒳''_s)` along the map of special fibres of the
generic slice of `M`, composed with `j' : X' ⟶ X'_c`. -/
noncomputable abbrev sliceSpecialUpperStarComp :
    Dᵇc(Xc'.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := Xc')
    (Y := baseChangeSpecial b (traitSlice (traitSliceCoord k')))
    (sliceSpecialMap (traitSliceCoord k') h.isTraitModelOver hb ≫ j'.left)

/-- The pullback `(c ≫ j)^* : Dᵇc(X_c) ⥤ Dᵇc(X₂)` along the map of bases of the generic slice of
`M`, composed with `j : X₁ ⟶ X_c`. -/
noncomputable abbrev genericSliceUpperStarComp :
    Dᵇc(Xc.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((genericSliceBase (traitSliceCoord k') hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := Xc) (Y := genericSliceBase (traitSliceCoord k') hb)
    (h.genericSliceBaseMap (traitSliceCoord k') hb ≫ j.left)

/-- The **slice exchange along `M'' ⟶ M ⟶ M_c`**: the pullback exchange
`α_c : (p ≫ j')^* Ψ_{M_c} ⟶ Ψ_{M''} (c ≫ j)^*` of the composite of the slice projection
`M'' ⟶ M` with `φ : M ⟶ M_c`, on bounded constructible complexes. -/
noncomputable abbrev genericSliceExchangeComp :
    boundedConstructibleNearbyCycles (hc.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        sliceSpecialUpperStarComp ℓ h hb j' ⟶
      genericSliceUpperStarComp ℓ h hb j ⋙
        genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb :=
  ((h.genericSliceHom (traitSliceCoord k') hb).comp φ).boundedConstructiblePullbackExchangeOfMap ℓ
    ((isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))
    (hc.preservesBoundedConstructible (ℓ := ℓ))

-- the instantiation of the abstract lemma elaborates large goals
/-- **The twist equation of the generic slice from an ambient model without coordinate**: let
`M` be an open sub-model of a trait model `M_c` over the generic base, through open immersions
`j : X₁ ⟶ X_c`, `j' : X' ⟶ X'_c` and `φ : M ⟶ M_c`, and let `b` be a coordinate of `M`. If the
twist equation holds for `θ_{M_c}` along the composite `M'' ⟶ M ⟶ M_c` of the slice projection
and `φ`, that is
`(p ≫ j')^* θ_{M_c} ≫ v = α_c ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T`
for the exchange `α_c` of that composite
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchangeComp`), then the twist
equation of `NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` holds for
`M`. Unlike `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`,
`M_c` needs no coordinate. -/
theorem exists_iso_map_θ_eq_twist_of_openSubmodel_comp (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ) [IsOpenImmersion j.left]
    [IsOpenImmersion j'.left] [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic M.j Mc.j φ.total) (hq : q = φ.total ≫ qc)
    (hg : g = φ.generic ≫ gc)
    (H : ∃ (u : (genericSliceUpperStarComp ℓ h hb j).obj (dualizingComplex ℓ Xc) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (sliceSpecialUpperStarComp ℓ h hb j').obj (dualizingComplex ℓ Xc') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (sliceSpecialUpperStarComp ℓ h hb j').map (D.θ hc) ≫ v.hom =
        (genericSliceExchangeComp ℓ h hb hc j j' φ).app (dualizingComplex ℓ Xc) ≫
          (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map u.hom ≫
          (genericSliceTwistIso ℓ h hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            h.isTraitModelOver) ▷ _) :
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
  have hM := h.isTraitModelOver
  have hM'' := isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb hM
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  have hres := D.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  -- the identity of the slice model, an open sub-model of itself
  have : IsOpenImmersion (Over.Hom.left (𝟙 (genericSliceBase (traitSliceCoord k') hb))) :=
    inferInstanceAs (IsOpenImmersion (𝟙 _))
  have : IsOpenImmersion
      (Over.Hom.left (𝟙 (baseChangeSpecial b (traitSlice (traitSliceCoord k'))))) :=
    inferInstanceAs (IsOpenImmersion (𝟙 _))
  let ψ' : (genericSliceModel (traitSliceCoord k') hb).Hom
      (genericSliceModel (traitSliceCoord k') hb)
      (Over.Hom.left (𝟙 (genericSliceBase (traitSliceCoord k') hb)))
      (Over.Hom.left (𝟙 (baseChangeSpecial b (traitSlice (traitSliceCoord k'))))) :=
    Hom.id _
  have : IsOpenImmersion ψ'.total := inferInstanceAs (IsOpenImmersion (𝟙 _))
  have : IsIso ψ'.total := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso ψ'.generic := inferInstanceAs (IsIso (𝟙 _))
  have hψ' : IsPullback ψ'.generic (genericSliceModel (traitSliceCoord k') hb).j
      (genericSliceModel (traitSliceCoord k') hb).j ψ'.total :=
    IsPullback.of_horiz_isIso ⟨by
      change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]⟩
  have htot' : (h.genericSliceHom (traitSliceCoord k') hb).total ≫ φ.total =
      ψ'.total ≫ ((h.genericSliceHom (traitSliceCoord k') hb).comp φ).total :=
    (Category.id_comp _).symm
  have hgen' : (h.genericSliceHom (traitSliceCoord k') hb).generic ≫ φ.generic =
      ψ'.generic ≫ ((h.genericSliceHom (traitSliceCoord k') hb).comp φ).generic :=
    (Category.id_comp _).symm
  have hqψ : pullback.snd b (traitSlice (traitSliceCoord k')) =
      ψ'.total ≫ pullback.snd b (traitSlice (traitSliceCoord k')) :=
    (Category.id_comp _).symm
  have hgψ : pullback.snd (pullback.snd b (traitSlice (traitSliceCoord k')))
        (traitGenericPoint (traitSliceField k')) =
      ψ'.generic ≫ pullback.snd (pullback.snd b (traitSlice (traitSliceCoord k')))
        (traitGenericPoint (traitSliceField k')) :=
    (Category.id_comp _).symm
  -- forget the definition of `ψ'`, so that `transport_exact` sees no `let` variable
  clear_value ψ'
  have hres₂ := DK.map_θ_comp_dualizingComplexUpperStarIso hM'' hM'' (𝟙 _) (𝟙 _) ψ' hψ'
    hqψ hgψ
  have hs : sliceSpecialMap (traitSliceCoord k') hM hb ≫ j'.left =
      (Over.Hom.left (𝟙 (baseChangeSpecial b (traitSlice (traitSliceCoord k'))))) ≫
        (sliceSpecialMap (traitSliceCoord k') hM hb ≫ j'.left) :=
    (Category.id_comp _).symm
  have hb' : h.genericSliceBaseMap (traitSliceCoord k') hb ≫ j.left =
      (Over.Hom.left (𝟙 (genericSliceBase (traitSliceCoord k') hb))) ≫
        (h.genericSliceBaseMap (traitSliceCoord k') hb ≫ j.left) :=
    (Category.id_comp _).symm
  have hsq := boundedConstructiblePullbackExchange_square
    (h.genericSliceHom (traitSliceCoord k') hb) φ ψ'
    ((h.genericSliceHom (traitSliceCoord k') hb).comp φ)
    htot' hgen' hb' hs
    (hc.preservesBoundedConstructible (ℓ := ℓ)) (h.preservesBoundedConstructible (ℓ := ℓ))
    (hM''.preservesBoundedConstructible (ℓ := ℓ)) (hM''.preservesBoundedConstructible (ℓ := ℓ))
    (genericSliceExchange (traitSliceCoord k') ℓ h hb) rfl
    (genericSliceExchangeComp ℓ h hb hc j j' φ) rfl (dualizingComplex ℓ Xc)
  have hκc := ψ'.liftExchange_zeroTwistIso (hM''.preservesBoundedConstructible (ℓ := ℓ))
    (hM''.preservesBoundedConstructible (ℓ := ℓ))
    (pullback.snd b (traitSlice (traitSliceCoord k')))
    (pullback.snd b (traitSlice (traitSliceCoord k')))
    (ψ'.boundedConstructiblePullbackExchange ℓ (hM''.preservesBoundedConstructible (ℓ := ℓ))
      (hM''.preservesBoundedConstructible (ℓ := ℓ))) rfl 2
    (dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb))
  exact exists_twist_of_openSubmodel
    (J₂ := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (𝟙 (genericSliceBase (traitSliceCoord k') hb)))
    (J₂' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (𝟙 (baseChangeSpecial b (traitSlice (traitSliceCoord k')))))
    (D.θ hc) (D.θ h) _ _ _ _ _ hres _ _ _ hres₂ _ _
    (boundedConstructibleUpperStarSquareIso ℓ hs _) (boundedConstructibleUpperStarSquareIso ℓ hs _)
    (boundedConstructibleUpperStarSquareIso_hom_naturality ℓ hs (D.θ hc))
    (boundedConstructibleUpperStarSquareIso ℓ hb' _) (by transport_exact hsq)
    (fun Z ↦ (Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ
        (Over.Hom.left (𝟙 (baseChangeSpecial b (traitSlice (traitSliceCoord k')))))) Z _).symm ≪≫
      whiskerLeftIso _ (boundedConstructibleTateTwistZeroUpperStarIso ℓ
        (Over.Hom.left (𝟙 (baseChangeSpecial b (traitSlice (traitSliceCoord k'))))) 2))
    (fun f ↦ μIso_symm_trans_whiskerLeftIso_hom_naturality _ _ f)
    ((Functor.Monoidal.μIso (boundedConstructibleUpperStarOfMap ℓ
        (Over.Hom.left (𝟙 (genericSliceBase (traitSliceCoord k') hb)))) _ _).symm ≪≫
      whiskerLeftIso _ (boundedConstructibleTateTwistZeroUpperStarIso ℓ
        (Over.Hom.left (𝟙 (genericSliceBase (traitSliceCoord k') hb))) 2))
    (genericSliceTwistIso ℓ h hb _) (genericSliceTwistIso ℓ h hb)
    (fun f ↦ zeroTwistIso_hom_naturality _ _ 2 f) (by transport_exact hκc) H

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
