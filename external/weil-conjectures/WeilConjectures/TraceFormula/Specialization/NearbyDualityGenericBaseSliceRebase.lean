/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceTwistIso
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingRebase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Proper

/-!

# The twist equation of the generic slice and re-basing

Inputs for deducing the twist equation of the generic slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`) for a trait model `M`
over the generic base `(F, X₁, ι)` from the same equation for its re-based model `M'` over
`(η, X₁,η, 𝟙)` (`NearbyCyclesModel.IsTraitModelOfGenericBase.isTraitModelOfGenericBase_rebase`).
The generic slices of `M` and `M'` are the same model `M''` over the same base `X₂`.

* `NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap_eq_rebase`: the map of bases
  `c : X₂ ⟶ X₁` of the slice of `M` is `c' ≫ π` for the map `c'` of the slice of `M'` and the
  projection `π : X₁,η ⟶ X₁` (the identification `ε` of the slice model is an epimorphism,
  `NearbyCyclesModel.IsTraitModelOfGenericBase.epi_genericSliceModel_ε`).
* `NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom_pullbackExchange_app_rebase`: the
  slice exchange of `M`, followed by `Lc^* ≅ Lπ^* ⋙ Lc'^*`, is `p^*` of the re-basing exchange
  followed by the slice exchange of `M'` (ambient derived categories), since the projection
  `M'' ⟶ M` is the composite of `M'' ⟶ M'` and of the identity `M' ⟶ M`.
* `NearbyCyclesModel.isIso_dualizingComplexBaseChange_genericBaseChange`: for proper `X₁` the
  comparison `φ : π^* ω_{X₁} ⟶ ω_{X₁,η}` is an isomorphism.
* `NearbyCyclesModel.exists_twist_of_rebase`: the algebra of the reduction, in abstract
  categories: from `θ_M = ρ ≫ Ψ_{M'}(φ) ≫ θ_{M'}`
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_rebase_of_isProper`), the exchange
  factorization `α ≫ Ψ_{M''}(E) = p^*(ρ) ≫ α'` and the twist equation for `M'`, the twist
  equation for `M` follows with `u = E ≪≫ c'^*(φ) ≪≫ u'`.
* the bounded constructible versions of the ingredients: `π^*`, `c'^*`, the slice exchange `α'`
  of the re-based model (`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseGenericSliceExchange`)
  and `E : c^* A ≅ c'^* π^* A`
  (`ProEtale.CondensedRing.NearbyCyclesModel.boundedConstructibleUpperStarOfMapCompIso`).

The bounded constructible version of the exchange factorization and the concrete reduction
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_rebase`) are in
`TraceFormula.Specialization.NearbyDualityGenericBaseSliceRebaseTwist`: lifting the ambient
identity of this file directly compares terms that differ by instance proofs and by the two
presentations `Spec (.of (FractionRing _))` of the base of the slice, which exhausts the kernel.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section Abstract

/-- The diagram chase behind `genericSliceHom_pullbackExchange_app_rebase`, in the shape of
`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`: a composition isomorphism
`cpI : P ≅ I ⋙ P` with `cpI ≫ P(eI) = 𝟙` (for `eI : I ≅ 𝟭`) is `P(eI⁻¹)`. -/
lemma rebase_exchange_aux {DX DXη DS Ds D₂ : Type*} [Category DX] [Category DXη]
    [Category DS] [Category Ds] [Category D₂] {Ψ : DX ⥤ DS} {I : DS ⥤ DS} {P : DS ⥤ Ds}
    {Pπ : DX ⥤ DXη} {Ψ' : DXη ⥤ DS} {Cc : DX ⥤ D₂} {C' : DXη ⥤ D₂} {Ψ'' : D₂ ⥤ Ds}
    (cpI : P ≅ I ⋙ P) (cmp : Cc ≅ Pπ ⋙ C') (eI : I ≅ 𝟭 DS) (ψN : Ψ ⋙ I ⟶ Pπ ⋙ Ψ')
    (φN : Ψ' ⋙ P ⟶ C' ⋙ Ψ'') (χN : Ψ ⋙ P ⟶ Cc ⋙ Ψ'') (C : DX)
    (sx : Ψ.obj C ⟶ Ψ'.obj (Pπ.obj C)) (hsx : sx = eI.inv.app (Ψ.obj C) ≫ ψN.app C)
    (e : P.obj (Ψ.obj C) = P.obj (Ψ.obj C))
    (hK : cpI.hom.app (Ψ.obj C) ≫ P.map (eI.hom.app (Ψ.obj C)) = eqToHom e)
    (key : χN.app C ≫ Ψ''.map (cmp.hom.app C) =
      cpI.hom.app (Ψ.obj C) ≫ P.map (ψN.app C) ≫ φN.app (Pπ.obj C)) :
    χN.app C ≫ Ψ''.map (cmp.hom.app C) =
      P.map sx ≫ φN.app (Pπ.obj C) := by
  have hc : cpI.hom.app (Ψ.obj C) = P.map (eI.inv.app (Ψ.obj C)) := by
    rw [← cancel_mono (P.map (eI.hom.app (Ψ.obj C))), hK, ← P.map_comp, Iso.inv_hom_id_app]
    simp
  rw [key, hc, hsx, P.map_comp, Category.assoc]

/-- **The twist equation and re-basing**, abstractly (the algebra behind deducing
`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation` from the re-based
model): if `θ = ρ ≫ Ψ'(φ) ≫ θ'` with `φ` invertible, `α ≫ Ψ(E) = P(ρ) ≫ α'` and the twist
equation holds for `θ'` and `α'`, then it holds for `θ` and `α`, with `u = E ≪≫ C'(φ) ≪≫ u'`
and the same `v`. -/
lemma exists_twist_of_rebase {DX DXη DS Ds D₂ : Type*} [Category DX] [Category DXη]
    [Category DS] [Category Ds] [Category D₂] {ΨM : DX ⥤ DS} {ΨM' : DXη ⥤ DS}
    {Pπ : DX ⥤ DXη} {P : DS ⥤ Ds} {Ψ : D₂ ⥤ Ds} {Cc : DX ⥤ D₂} {C' : DXη ⥤ D₂} {ω : DX}
    {ωη : DXη} {ω' : DS} {W : D₂} {V Z : Ds}
    (θ : ΨM.obj ω ⟶ ω') (θ' : ΨM'.obj ωη ⟶ ω') (ρ : ΨM ⟶ Pπ ⋙ ΨM') (φ : Pπ.obj ω ⟶ ωη)
    [IsIso φ] (hθ : θ = ρ.app ω ≫ ΨM'.map φ ≫ θ') (α : ΨM ⋙ P ⟶ Cc ⋙ Ψ)
    (α' : ΨM' ⋙ P ⟶ C' ⋙ Ψ) (E : Cc.obj ω ≅ C'.obj (Pπ.obj ω))
    (hα : α.app ω ≫ Ψ.map E.hom = P.map (ρ.app ω) ≫ α'.app (Pπ.obj ω)) (κ : Ψ.obj W ≅ Z)
    (t : Z ⟶ V)
    (H : ∃ (u : C'.obj ωη ≅ W) (v : P.obj ω' ≅ V),
      P.map θ' ≫ v.hom = α'.app ωη ≫ Ψ.map u.hom ≫ κ.hom ≫ t) :
    ∃ (u : Cc.obj ω ≅ W) (v : P.obj ω' ≅ V),
      P.map θ ≫ v.hom = α.app ω ≫ Ψ.map u.hom ≫ κ.hom ≫ t := by
  obtain ⟨u, v, huv⟩ := H
  refine ⟨E ≪≫ C'.mapIso (asIso φ) ≪≫ u, v, ?_⟩
  have hnat := α'.naturality φ
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  simp only [hθ, Functor.map_comp, Category.assoc, huv, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, reassoc_of% hα, reassoc_of% hnat]

end Abstract

namespace IsTraitModelOfGenericBase

section BaseMap

variable {K : Type u} [Field K] [Algebra k' K] (x : K)

/-- **The slice base map of the re-based model**: the map `c : X₂ ⟶ X₁` of the generic slice is
the map `c' : X₂ ⟶ X₁,η` of the generic slice of the re-based model followed by the projection
`π : X₁,η ⟶ X₁`. Both satisfy the defining property of `c`, and the identification `ε` of the
slice model is an epimorphism. -/
lemma genericSliceBaseMap_eq_rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    h.genericSliceBaseMap x hb =
      h.isTraitModelOfGenericBase_rebase.genericSliceBaseMap x hb ≫ pullback.fst X₁.hom ι := by
  have := h.epi_genericSliceModel_ε x hb
  refine (cancel_epi (genericSliceModel x hb).ε).1
    ((h.genericSliceModel_ε_comp_genericSliceBaseMap x hb).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ pullback.fst X₁.hom ι)
    (h.isTraitModelOfGenericBase_rebase.genericSliceModel_ε_comp_genericSliceBaseMap x hb).symm)
  exact (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _).symm).trans (Category.assoc _ _ _).symm

/-- The projection `M'' ⟶ M'` from the generic slice model to the re-based model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom` of the re-based model), as a
morphism from the generic slice model of `M` over the map of special fibres of the generic slice
of `M` (the generic slices of `M` and of the re-based model are the same). -/
noncomputable def rebaseGenericSliceHom (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    (genericSliceModel x hb).Hom h.rebase
      (h.isTraitModelOfGenericBase_rebase.genericSliceBaseMap x hb)
      (sliceSpecialMap x h.isTraitModelOver hb) :=
  h.isTraitModelOfGenericBase_rebase.genericSliceHom x hb

/-- **The slice exchange and re-basing** (ambient): the pullback exchange `α` of the projection
`M'' ⟶ M` from the generic slice, followed by the composition isomorphism
`Lc^* ≅ Lπ^* ⋙ Lc'^*` (along `c' ≫ π = c`), is `p^*` of the re-basing exchange followed by the
pullback exchange `α'` of the projection `M'' ⟶ M'` to the re-based model: the projection to `M`
is the composite of the projection to `M'` and of
`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseHom`. -/
lemma genericSliceHom_pullbackExchange_app_rebase
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj Λ X₁.left))) :
    (Hom.pullbackExchange (X' := (baseChangeSpecial b (traitSlice x)).left) Λ
      (h.genericSliceHom x hb)).app C ≫
      ((genericSliceModel x hb).nearbyCycles Λ).map
        ((leftDerivedUpperStarCompOfEq (B₀ := (genericSliceBase x hb).left)
          (B₁ := (genericBaseChange X₁ ι).left) Λ
          (h.genericSliceBaseMap_eq_rebase x hb).symm).hom.app C) =
    L(upperStar (X := (baseChangeSpecial b (traitSlice x)).left) (Y := X'.left) Λ
        (sliceSpecialMap x h.isTraitModelOver hb)).map
      (h.rebaseHom.specialIdExchange Λ C) ≫
      ((h.rebaseGenericSliceHom x hb).pullbackExchange Λ).app
        (L(upperStar (X := (genericBaseChange X₁ ι).left) (Y := X₁.left) Λ
          (pullback.fst X₁.hom ι)).obj C) := by
  have hp : (sliceSpecialMap x h.isTraitModelOver hb :
      (baseChangeSpecial b (traitSlice x)).left ⟶ X'.left) ≫ 𝟙 X'.left =
      sliceSpecialMap x h.isTraitModelOver hb := Category.comp_id _
  have key := (h.rebaseGenericSliceHom x hb).pullbackExchange_comp_app_of_eq
    Λ h.rebaseHom (h.genericSliceHom x hb) (h.genericSliceBaseMap_eq_rebase x hb).symm
    hp (Category.comp_id _) (Category.comp_id _) C
  have hK := leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId
    (X := (baseChangeSpecial b (traitSlice x)).left) (Y := X'.left) Λ hp
    ((M.nearbyCycles Λ).obj C)
  exact rebase_exchange_aux _ _ _ _ _ _ C _ rfl _ hK key

end BaseMap

end IsTraitModelOfGenericBase

section IsIso

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]

variable (X₁ ι) in
/-- The comparison `φ : π^* ω_{X₁} ⟶ ω_{X₁,η}` of the dualizing complexes along `ι` is an
isomorphism for proper `X₁`
(`ProEtale.CondensedRing.isIso_dualizingComplexBaseChange_of_fieldExtension`, `ι` being the
spectrum of a field extension). -/
lemma isIso_dualizingComplexBaseChange_genericBaseChange
    [IsProper (CondensedRing.toPoint X₁).left] :
    haveI := isProper_toPoint_genericBaseChange (X₁ := X₁) (ι := ι)
    IsIso (dualizingComplexBaseChange ℓ (X := X₁) (X' := genericBaseChange X₁ ι)
      (inv (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ
        (X := point F) (Y := point (FractionRing (PowerSeries k'))) ι)))
      (isPullback_genericBaseChange X₁ ι)) := by
  have := isProper_toPoint_genericBaseChange (X₁ := X₁) (ι := ι)
  obtain ⟨f, rfl⟩ := Spec.map_surjective ι
  let : Algebra F (FractionRing (PowerSeries k')) := f.hom.toAlgebra
  exact isIso_dualizingComplexBaseChange_of_fieldExtension ℓ _
    (isPullback_genericBaseChange X₁ (Spec.map f))

end IsIso

section CompExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ kη : Type u} [Field k₁] [Field k₂] [Field kη]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] [Fact (ringChar kη).Prime] [Fact (ringChar kη ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {Z : Over (Spec (.of kη))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The composition isomorphism `c^* A ≅ c'^* π^* A` of the pullbacks of bounded constructible
complexes along `c' ≫ π = c` (`ProEtale.CondensedRing.leftDerivedUpperStarCompOfEq`). -/
noncomputable def boundedConstructibleUpperStarOfMapCompIso {c : Y.left ⟶ X.left}
    {c' : Y.left ⟶ Z.left} {π : Z.left ⟶ X.left} (hc : c' ≫ π = c)
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) c).obj A ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Y) c').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Z) π).obj A) :=
  ObjectProperty.isoMk _
    ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ) hc).app A.obj)

end CompExchange

section SliceExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
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

namespace IsTraitModelOfGenericBase

/-- The pullback `π^* : Dᵇc(X₁) ⥤ Dᵇc(X₁,η)` along the projection `π : X₁,η ⟶ X₁`. -/
noncomputable abbrev genericBaseChangeUpperStar :
    Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((genericBaseChange X₁ ι).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
    (pullback.fst X₁.hom ι)

/-- The pullback `c'^* : Dᵇc(X₁,η) ⥤ Dᵇc(X₂)` along the map of bases of the generic slice of the
re-based model. -/
noncomputable abbrev rebaseGenericSliceUpperStar :
    Dᵇc((genericBaseChange X₁ ι).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((genericSliceBase (M := M) (traitSliceCoord k') hb).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := genericBaseChange X₁ ι)
    (Y := genericSliceBase (M := M) (traitSliceCoord k') hb)
    (h.isTraitModelOfGenericBase_rebase.genericSliceBaseMap (traitSliceCoord k') hb)

/-- The slice exchange `α' : p^* Ψ_{M'} ⟶ Ψ_{M''} c'^*` of the re-based model: the pullback
exchange of `NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseGenericSliceHom`, on bounded
constructible complexes. -/
noncomputable def rebaseGenericSliceExchange :
    boundedConstructibleNearbyCycles
        (h.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb ⟶
      rebaseGenericSliceUpperStar ℓ h hb ⋙ genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb :=
  liftExchange ((h.rebaseGenericSliceHom (traitSliceCoord k') hb).pullbackExchange
    (Profinite.padicAlgClRingObj ℓ)) _ _ _ _

end IsTraitModelOfGenericBase

end SliceExchange

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
