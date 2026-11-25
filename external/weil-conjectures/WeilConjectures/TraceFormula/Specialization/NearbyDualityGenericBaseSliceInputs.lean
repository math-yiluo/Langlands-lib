/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTensor
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBase

/-!

# Nearby duality over a generic base: the inputs of the slice step

Let `M` be a trait model of `X₁` over the generic base, `b : 𝒳 ⟶ 𝔸¹_S` a coordinate of its total
space and `M''` the generic slice model of `b` (`NearbyCyclesModel.genericSliceModel`), a trait
model over the generic base `(Frac K⟦t⟧, X₂)`, with special fibre `Y = 𝒳''_s`. This file sets up
the proof of the slice compatibility of nearby duality
(`NearbyCyclesModel.isIso_map_sliceSpecialMap_nearbyDualityMapOfGenericBase`, blueprint
`lemma-nearby-duality-slice--1` (2) with `lemma-duality-invariants-pro-p--1`):

* the pullback `Lg^*` of bounded constructible complexes along a morphism of schemes of finite
  type over possibly different fields (`boundedConstructibleUpperStarOfMap`), strong monoidal;
* the morphism of models `M'' ⟶ M` over `c : X₂ ⟶ X₁` and `p : Y ⟶ X'`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom`) and its pullback exchange
  `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange`),
  which is monoidal (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceExchange_tensor`);
* the action of the self-maps of a model over the identities on its nearby cycles
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceSelfAction`), which is monoidal
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceSelfAction_tensor`);
* the duality map of the slice for the dualizing objects `c^* ω_{X₁}` and `p^* ω_{X'}`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceDualityMap`).

The other inputs of the slice step are in separate files: the averaging splitting of `α`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`, in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceAveraging`), the
commutation of the pullbacks with internal Hom (blueprint
`lemma-restriction-geometric-generic-fibre` (2), in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceClosedHom`) and the
dualizing map of the slice
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap`, in
`WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceDualizing`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section UpperStarOfMap

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)] {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pullback `Lg^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible complexes
along a morphism of schemes `g : Y ⟶ X`, `X` and `Y` of finite type over possibly different
fields: the restriction of `L((g)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ g K.obj K.property

/-- The derived pullback along a morphism of schemes is strong monoidal on bounded constructible
complexes, with the comparison isomorphisms of `L((g)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable instance monoidal_boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g).Monoidal := by
  unfold boundedConstructibleUpperStarOfMap
  exact ObjectProperty.monoidalLift _ _

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The derived pullback along a morphism of schemes on bounded constructible complexes is that
of the ambient derived categories. -/
lemma boundedConstructibleUpperStarOfMap_map (g : Y.left ⟶ X.left)
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : A ⟶ B) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g).map f =
      ObjectProperty.homMk (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map f.hom) :=
  rfl

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₂).Prime] [IsSeparated X.hom]
  [IsSeparated Y.hom] in
/-- The tensor comparison of the derived pullback along a morphism of schemes on bounded
constructible complexes is that of the ambient derived pullback. -/
lemma μ_boundedConstructibleUpperStarOfMap (g : Y.left ⟶ X.left)
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g) A B =
      ObjectProperty.homMk
        (Functor.LaxMonoidal.μ L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A.obj B.obj) :=
  rfl

end UpperStarOfMap

namespace NearbyCyclesModel

section LiftExchange

variable {ℓ : ℕ} [Fact ℓ.Prime] {k₁ k₁' k₂ k₂' : Type u} [Field k₁] [Field k₁'] [Field k₂]
  [Field k₂'] [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₁').Prime]
  [Fact (ringChar k₁' ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  [Fact (ringChar k₂').Prime] [Fact (ringChar k₂' ≠ ℓ)]
  {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k₁'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {Y' : Over (Spec (.of k₂'))}
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y.left ⟶ X.left} {j' : Y'.left ⟶ X'.left}

omit [Fact (ringChar k₁).Prime] [Fact (ringChar k₁').Prime] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂').Prime] [IsSeparated X.hom] [IsSeparated X'.hom] [IsSeparated Y.hom]
  [IsSeparated Y'.hom] in
/-- The monoidality of the restriction `NearbyCyclesModel.liftExchange` to bounded constructible
complexes of a transformation `α : Ψ_M ⋙ Lj'^* ⟶ Lj^* ⋙ Ψ_N`, along morphisms of schemes over
possibly different fields, deduced from that of `α` (in the oplax form of
`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`). -/
lemma liftExchange_upperStarOfMap_tensor
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        L((j')^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (hα : ∀ A B, L((j')^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (M.tensorMap (Profinite.padicAlgClRingObj ℓ) A B) ≫ α.app (A ⊗ B) ≫
          (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
            (Functor.OplaxMonoidal.δ L((j)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A B) =
      Functor.OplaxMonoidal.δ L((j')^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ _ ≫
        (α.app A ⊗ₘ α.app B) ≫ N.tensorMap (Profinite.padicAlgClRingObj ℓ) _ _)
    (β : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j' ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) j ⋙
        boundedConstructibleNearbyCycles hN)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ j' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ j K.obj K.property))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (β.app A ⊗ₘ β.app B) ≫ boundedConstructibleTensorMap hN _ _ ≫
        (boundedConstructibleNearbyCycles hN).map (Functor.LaxMonoidal.μ
          (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) j) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j') _ _ ≫
        (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := Y') j').map
          (boundedConstructibleTensorMap hM A B) ≫ β.app (A ⊗ B) := by
  subst hβ
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.tensorHom_hom',
    liftExchange_app_hom, boundedConstructibleUpperStarOfMap_map,
    μ_boundedConstructibleUpperStarOfMap, ObjectProperty.homMk_hom]
  exact Verdier.lax_of_oplax_aux (M.tensorMap _) (N.tensorMap _) (fun A ↦ α.app A) A.obj B.obj
    (hα A.obj B.obj)

end LiftExchange

/-! ### The generic slice -/

section GenericSlice

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {K : Type u} [Field K] [Algebra k' K] (x : K)

section Hom

/-- The morphism `c : X₂ ⟶ X₁` from the base of the generic slice to the base of a trait model
over the generic base (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceBase_comp`).
-/
noncomputable def IsTraitModelOfGenericBase.genericSliceBaseMap
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    (genericSliceBase x hb).left ⟶ X₁.left :=
  (h.exists_genericSliceBase_comp x hb).choose

lemma IsTraitModelOfGenericBase.genericSliceModel_ε_comp_genericSliceBaseMap
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    (genericSliceModel x hb).ε ≫ h.genericSliceBaseMap x hb =
      baseChangeGenericMap h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x) ≫ M.ε :=
  (h.exists_genericSliceBase_comp x hb).choose_spec.2

/-- The projection `M'' ⟶ M` from the generic slice model, a morphism of models over
`c : X₂ ⟶ X₁` and the map of special fibres `p : 𝒳''_s ⟶ 𝒳_s`. -/
noncomputable def IsTraitModelOfGenericBase.genericSliceHom
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    (genericSliceModel x hb).Hom M (h.genericSliceBaseMap x hb)
      (sliceSpecialMap x h.isTraitModelOver hb) where
  total := pullback.fst _ _
  generic := baseChangeGenericMap h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x)
  comm_j := baseChangeGenericMap_j _ _ _ _ _
  comm_i := h.isTraitModelOver.isPullback_i.lift_fst _ _ _
  comm_ε := (h.genericSliceModel_ε_comp_genericSliceBaseMap x hb).symm

end Hom

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase x hb).hom] [QuasiCompact (genericSliceBase x hb).hom]
  [IsSeparated (genericSliceBase x hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice x)).hom]

namespace IsTraitModelOfGenericBase

/-- The pullback `p^* : Dᵇc(𝒳_s) ⥤ Dᵇc(𝒳''_s)` along the map of special fibres of the generic
slice. -/
noncomputable abbrev sliceSpecialUpperStar :
    Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((baseChangeSpecial b (traitSlice x)).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := baseChangeSpecial b (traitSlice x))
    (sliceSpecialMap x h.isTraitModelOver hb)

/-- The pullback `c^* : Dᵇc(X₁) ⥤ Dᵇc(X₂)` along the map of bases of the generic slice. -/
noncomputable abbrev genericSliceUpperStar :
    Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((genericSliceBase x hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericSliceBase x hb)
    (h.genericSliceBaseMap x hb)

/-- The nearby cycles `Ψ_{M''}` of the generic slice model on bounded constructible complexes. -/
noncomputable abbrev genericSliceNearbyCycles :
    Dᵇc((genericSliceBase x hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((baseChangeSpecial b (traitSlice x)).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleNearbyCycles
    ((isTraitModelOfGenericBase_genericSliceModel x hb
      h.isTraitModelOver).preservesBoundedConstructible
      (ℓ := ℓ))

/-- The **slice exchange** `α : p^* Ψ_M ⟶ Ψ_{M''} c^*`: the pullback exchange of the projection
`M'' ⟶ M` from the generic slice model, on bounded constructible complexes. -/
noncomputable def genericSliceExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        sliceSpecialUpperStar x ℓ h hb ⟶
      genericSliceUpperStar x ℓ h hb ⋙ genericSliceNearbyCycles x ℓ h hb :=
  liftExchange ((h.genericSliceHom x hb).pullbackExchange (Profinite.padicAlgClRingObj ℓ)) _ _ _ _

/-- The action `ρ(ψ) : Ψ_{M''} ⟶ Ψ_{M''}` of a self-map `ψ` of the generic slice model over the
identities on its nearby cycles, on bounded constructible complexes: the restriction of
`NearbyCyclesModel.Hom.autAction` (the pullback exchange `L𝟙^* Ψ_{M''} ⟶ Ψ_{M''} L𝟙^*` of `ψ`,
through the identifications `L𝟙^* ≅ 𝟭`). For the Galois automorphisms of the geometric generic
point, this is the action of inertia on nearby cycles. -/
noncomputable def genericSliceSelfAction
    (ψ : (genericSliceModel x hb).Hom (genericSliceModel x hb) (𝟙 _) (𝟙 _)) :
    genericSliceNearbyCycles x ℓ h hb ⟶ genericSliceNearbyCycles x ℓ h hb where
  app A := ObjectProperty.homMk (ψ.autAction (Profinite.padicAlgClRingObj ℓ) A.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    (ψ.autAction_naturality (Profinite.padicAlgClRingObj ℓ) f.hom).symm

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]
  [LocallyOfFiniteType (genericSliceBase x hb).hom] [QuasiCompact (genericSliceBase x hb).hom]
  [IsSeparated (genericSliceBase x hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice x)).hom] in
/-- The action of a self-map of the generic slice model is `NearbyCyclesModel.Hom.autAction`. -/
lemma genericSliceSelfAction_app
    (ψ : (genericSliceModel x hb).Hom (genericSliceModel x hb) (𝟙 _) (𝟙 _))
    (A : Dᵇc((genericSliceBase x hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (genericSliceSelfAction x ℓ h hb ψ).app A =
      ObjectProperty.homMk (ψ.autAction (Profinite.padicAlgClRingObj ℓ) A.obj) :=
  rfl

/-- The duality map `Ψ_{M''} RHom(A, c^* ω_{X₁}) ⟶ RHom(Ψ_{M''} A, p^* ω_{X'})` of the generic
slice model for the dualizing objects `c^* ω_{X₁}` and `p^* ω_{X'}` and a dualizing map `θ`. -/
noncomputable def genericSliceDualityMap
    (θ : (genericSliceNearbyCycles x ℓ h hb).obj
        ((genericSliceUpperStar x ℓ h hb).obj (dualizingComplex ℓ X₁)) ⟶
      (sliceSpecialUpperStar x ℓ h hb).obj (dualizingComplex ℓ X'))
    (A : Dᵇc((genericSliceBase x hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (genericSliceNearbyCycles x ℓ h hb).obj
        ((ihom A).obj ((genericSliceUpperStar x ℓ h hb).obj (dualizingComplex ℓ X₁))) ⟶
      (ihom ((genericSliceNearbyCycles x ℓ h hb).obj A)).obj
        ((sliceSpecialUpperStar x ℓ h hb).obj (dualizingComplex ℓ X')) :=
  Verdier.nearbyDualityMap (boundedConstructibleTensorMap
    ((isTraitModelOfGenericBase_genericSliceModel x hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))) θ A

omit [IsSepClosed k'] in
/-- The uncurried duality map of the slice is the pairing `θ ∘ Ψ_{M''}(ev) ∘ μ_{M''}`. -/
lemma uncurry_genericSliceDualityMap
    (θ : (genericSliceNearbyCycles x ℓ h hb).obj
        ((genericSliceUpperStar x ℓ h hb).obj (dualizingComplex ℓ X₁)) ⟶
      (sliceSpecialUpperStar x ℓ h hb).obj (dualizingComplex ℓ X'))
    (A : Dᵇc((genericSliceBase x hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    uncurry (genericSliceDualityMap x ℓ h hb θ A) =
      boundedConstructibleTensorMap
          ((isTraitModelOfGenericBase_genericSliceModel x hb
            h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ)) _ _ ≫
        (genericSliceNearbyCycles x ℓ h hb).map
          ((ihom.ev A).app ((genericSliceUpperStar x ℓ h hb).obj (dualizingComplex ℓ X₁))) ≫ θ :=
  Verdier.uncurry_nearbyDualityMap _ _ _

omit [Fact (ringChar F).Prime] [IsSeparated X₁.hom] [IsSeparated X'.hom]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime] [IsSeparated (genericSliceBase x hb).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice x)).hom] in
/-- **The slice exchange is monoidal** (blueprint `lemma-nearby-duality-slice--1`, "the pairing"):
`Ψ_{M''}(μ_{c^*}) ∘ μ_{M''} ∘ (α ⊗ α) = α ∘ p^*(μ_M) ∘ μ_{p^*}`. This is the restriction to
bounded constructible complexes of `NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`
(with `μ = δ⁻¹` for the strong monoidal pullbacks). -/
lemma genericSliceExchange_tensor (A B : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((genericSliceExchange x ℓ h hb).app A ⊗ₘ (genericSliceExchange x ℓ h hb).app B) ≫
        boundedConstructibleTensorMap
          ((isTraitModelOfGenericBase_genericSliceModel x hb
            h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ)) _ _ ≫
        (genericSliceNearbyCycles x ℓ h hb).map
          (Functor.LaxMonoidal.μ (genericSliceUpperStar x ℓ h hb) A B) =
      Functor.LaxMonoidal.μ (sliceSpecialUpperStar x ℓ h hb) _ _ ≫
        (sliceSpecialUpperStar x ℓ h hb).map
          (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ)) A B) ≫
        (genericSliceExchange x ℓ h hb).app (A ⊗ B) :=
  liftExchange_upperStarOfMap_tensor (X := X₁) (X' := X') (Y := genericSliceBase x hb)
    (Y' := baseChangeSpecial b (traitSlice x)) (j := h.genericSliceBaseMap x hb)
    (j' := sliceSpecialMap x h.isTraitModelOver hb)
    ((isTraitModelOfGenericBase_genericSliceModel x hb
      h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ))
    (h.preservesBoundedConstructible (ℓ := ℓ))
    ((h.genericSliceHom x hb).pullbackExchange (Profinite.padicAlgClRingObj ℓ))
    ((h.genericSliceHom x hb).map_tensorMap_comp_pullbackExchange_app _)
    (genericSliceExchange x ℓ h hb) rfl A B

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
  [IsSeparated (genericSliceBase x hb).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice x)).hom] in
/-- **The action of a self-map of the generic slice model on nearby cycles is monoidal**:
`μ_{M''} ∘ (ρ(ψ) ⊗ ρ(ψ)) = ρ(ψ) ∘ μ_{M''}`. It follows from
`NearbyCyclesModel.Hom.autAction_tensor`. -/
lemma genericSliceSelfAction_tensor
    (ψ : (genericSliceModel x hb).Hom (genericSliceModel x hb) (𝟙 _) (𝟙 _))
    (A B : Dᵇc((genericSliceBase x hb).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((genericSliceSelfAction x ℓ h hb ψ).app A ⊗ₘ (genericSliceSelfAction x ℓ h hb ψ).app B) ≫
        boundedConstructibleTensorMap
          ((isTraitModelOfGenericBase_genericSliceModel x hb
            h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ)) A B =
      boundedConstructibleTensorMap
          ((isTraitModelOfGenericBase_genericSliceModel x hb
            h.isTraitModelOver).preservesBoundedConstructible (ℓ := ℓ)) A B ≫
        (genericSliceSelfAction x ℓ h hb ψ).app (A ⊗ B) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.tensorHom_hom',
    genericSliceSelfAction_app, boundedConstructibleTensorMap, ObjectProperty.homMk_hom]
  exact ψ.autAction_tensor _ A.obj B.obj

end IsTraitModelOfGenericBase


end GenericSlice

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
