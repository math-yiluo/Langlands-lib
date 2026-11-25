/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseUnique
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSlice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingRebaseAux
import WeilConjectures.Tactic.ExactModProofs

/-!

# Re-basing a trait model over a generic base to the generic point of the trait

Let `M` be a trait model of `X₁` over the generic base `(F, X₁, ι : η ⟶ Spec F)`, `η` the generic
point of the strictly henselian trait `S = Spec k'⟦t⟧`. Its geometric generic fibre maps to the base
change `X₁,η = X₁ ×_F η` (`NearbyCyclesModel.genericBaseChange`), and `M` with this new
identification `ε'` is a trait model of `X₁,η` over the generic base `(η, X₁,η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.rebase`,
`NearbyCyclesModel.IsTraitModelOfGenericBase.isTraitModelOfGenericBase_rebase`). The identity of
`M` is a morphism of models `M' ⟶ M` over the projection `π : X₁,η ⟶ X₁`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseHom`), whose pullback exchange
`Ψ_M ⟶ Ψ_{M'} π^*` (`NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseExchange`) is invertible.

**The dualizing maps and re-basing**
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_rebase_of_isProper`): for a proper model
with full generic fibre and proper `X₁`, the dualizing map of `M` over `F` is that of `M'` over
`η` composed with the comparison `φ : π^* ω_{X₁} ⟶ ω_{X₁,η}` of the dualizing complexes
(`ProEtale.CondensedRing.dualizingComplexBaseChange`, the mate of proper base change):
`θ_M = α ≫ Ψ_{M'}(φ) ≫ θ_{M'}`. Both sides have the trace property of `M` over `F`: the identity of
the trait is a morphism of models `τ : S_η ⟶ S_F` over `ι`
(`NearbyCyclesModel.traitModelOfPointMap`) with `rebaseHom ≫ a = a' ≫ τ`, so the proper exchange
`χ_F` followed by the re-basing exchange is the exchange `β` of `τ`
(`NearbyCyclesModel.traitPointSpecializationExchange`), followed by the base change morphism of
`X₁,η ⟶ X₁` and the proper exchange `χ_η` of `M'`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.pushforwardExchange_app_comp_map_rebaseExchange_app`),
and `φ` is compatible with the traces.

## Implementation notes

The ambient identities are instances of the abstract lemmas of
`TraceFormula.Specialization.NearbyDualizingRebaseAux`. Lifting them to bounded constructible
complexes, the object `Lπ^* A` of the ambient statement and `(π^* A).obj` are only
definitionally equal (the instance proofs inside differ), and the kernel unfolds the derived
categories when comparing them under projections; the ambient statement is therefore phrased with
an arbitrary object `P` equal to `Lπ^* A` (`eqToHom`), instantiated at `(π^* A).obj`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section SpecialId

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {T₁ T₂ T₀ : Scheme.{u}} {M₀ : NearbyCyclesModel T₁ T₀} {N₀ : NearbyCyclesModel T₂ T₀}
  {f₀ : T₁ ⟶ T₂}

/-- The pullback exchange `Ψ_N A ⟶ Ψ_M (Lf^* A)` of a morphism of models `φ : M ⟶ N` over `f` and
the identity of the special fibre, through `L(𝟙)^* ≅ 𝟭`. -/
noncomputable def Hom.specialIdExchange (φ : M₀.Hom N₀ f₀ (𝟙 T₀))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T₂) Ab.{u + 1})
      (condensedRingObj Λ T₂))) :
    (N₀.nearbyCycles Λ).obj A ⟶ (M₀.nearbyCycles Λ).obj ((L((f₀)^*⟦Λ⟧)).obj A) :=
  (leftDerivedUpperStarId Λ T₀).inv.app _ ≫ (φ.pullbackExchange Λ).app A

/-- The exchange `NearbyCyclesModel.Hom.specialIdExchange` is natural. -/
@[reassoc]
lemma Hom.specialIdExchange_naturality (φ : M₀.Hom N₀ f₀ (𝟙 T₀))
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T₂) Ab.{u + 1})
      (condensedRingObj Λ T₂))} (a : A ⟶ A') :
    φ.specialIdExchange Λ A ≫ (M₀.nearbyCycles Λ).map ((L((f₀)^*⟦Λ⟧)).map a) =
      (N₀.nearbyCycles Λ).map a ≫ φ.specialIdExchange Λ A' := by
  have h₁ := (leftDerivedUpperStarId Λ T₀).inv.naturality ((N₀.nearbyCycles Λ).map a)
  have h₂ := (φ.pullbackExchange Λ).naturality a
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂
  simp only [Hom.specialIdExchange, Category.assoc]
  rw [← h₂]
  exact ((reassoc_of% h₁) _).symm

end SpecialId

variable (X₁ ι) in
/-- The base change `X₁,η = X₁ ×_F η` of the base of a generic base, as a scheme over the generic
point `η` of the trait. -/
noncomputable def genericBaseChange :
    Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)) :=
  Over.mk (pullback.snd X₁.hom ι)

instance [LocallyOfFiniteType X₁.hom] : LocallyOfFiniteType (genericBaseChange X₁ ι).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X₁.hom ι))

instance [QuasiCompact X₁.hom] : QuasiCompact (genericBaseChange X₁ ι).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X₁.hom ι))

instance [IsSeparated X₁.hom] : IsSeparated (genericBaseChange X₁ ι).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X₁.hom ι))

/-- The base change `X₁,η` of a proper base is proper. -/
lemma isProper_toPoint_genericBaseChange [IsProper (toPoint X₁).left] :
    IsProper (toPoint (genericBaseChange X₁ ι)).left := by
  rw [toPoint_left]
  have : IsProper X₁.hom := by rw [← toPoint_left]; infer_instance
  exact inferInstanceAs (IsProper (pullback.snd X₁.hom ι))

variable (X₁ ι) in
/-- The base change square `X₁,η ⟶ X₁` over `ι : η ⟶ Spec F`. -/
lemma isPullback_genericBaseChange :
    IsPullback (pullback.fst X₁.hom ι) (toPoint (genericBaseChange X₁ ι)).left
      (toPoint X₁).left ι := by
  rw [toPoint_left, toPoint_left]
  exact IsPullback.of_hasPullback _ _

namespace IsTraitModelOfGenericBase

/-- The geometric generic fibre of a trait model over the generic base lies over `ι`. -/
lemma ε_comp_hom (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    M.ε ≫ X₁.hom = (g ≫ traitGenericPointToSpec k') ≫ ι := by
  obtain ⟨u, -, hu₁, hu₂⟩ := h.exists_openImmersion
  rw [← hu₁, Category.assoc, pullback.condition, ← Category.assoc, hu₂, Category.assoc]

/-- The **re-based model**: the model `M` with the identification `ε' : 𝒳_Ω ⟶ X₁ ×_F η` of its
geometric generic fibre, a model of the base change `X₁,η` of the base. -/
noncomputable def rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    NearbyCyclesModel (genericBaseChange X₁ ι).left X'.left where
  total := M.total
  generic := M.generic
  j := M.j
  i := M.i
  ε := pullback.lift M.ε (g ≫ traitGenericPointToSpec k') h.ε_comp_hom

/-- **The re-based model is a trait model over the generic base `(η, X₁,η, 𝟙)`.** -/
theorem isTraitModelOfGenericBase_rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    h.rebase.IsTraitModelOfGenericBase (genericBaseChange X₁ ι) (𝟙 _) q g := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := h.exists_openImmersion_genericFibre
  let w' : pullback q (traitGenericSpec k') ⟶
      pullback (genericBaseChange X₁ ι).hom (𝟙 (Spec (.of (FractionRing (PowerSeries k'))))) :=
    w ≫ inv (pullback.fst (genericBaseChange X₁ ι).hom (𝟙 _))
  have hw'₁ : w' ≫ pullback.fst _ _ = w := by simp [w']
  have hw'₂ : w' ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [← Category.comp_id (pullback.snd (genericBaseChange X₁ ι).hom _), ← pullback.condition,
      reassoc_of% hw'₁]
    exact hw₁
  have hM := h.isTraitModelOver
  refine ⟨⟨hM.1, hM.2, hM.3, hM.4, hM.5⟩, w', inferInstanceAs (IsOpenImmersion (w ≫ _)), hw'₂, ?_⟩
  rw [hw'₁]
  apply pullback.hom_ext
  · exact hw₂.trans (pullback.lift_fst _ _ _).symm
  · exact (Category.assoc _ _ _).trans
      ((congrArg (genericFibreInclusion M q g hM.isPullback_j.w ≫ ·) hw₁).trans
        ((genericFibreInclusion_snd _ _ _ _).trans (pullback.lift_snd _ _ _).symm))

/-- The identity of `M` as a morphism of models `M' ⟶ M` from the re-based model, over the
projection `π : X₁,η ⟶ X₁` and the identity of the special fibre. -/
noncomputable def rebaseHom (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    h.rebase.Hom M (pullback.fst X₁.hom ι) (𝟙 X'.left) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [rebase]
  comm_i := by simp [rebase]
  comm_ε := by simp [rebase]

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The **re-basing exchange** `Ψ_M ⟶ Ψ_{M'} π^*` on bounded constructible complexes: the pullback
exchange of `NearbyCyclesModel.IsTraitModelOfGenericBase.rebaseHom`, through `L𝟙^* ≅ 𝟭` on the
special fibre. -/
noncomputable def rebaseExchange (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι) ⋙
        boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ)) where
  app A := ObjectProperty.homMk
    (h.rebaseHom.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    (h.rebaseHom.specialIdExchange_naturality (Profinite.padicAlgClRingObj ℓ) f.hom).symm

end IsTraitModelOfGenericBase

section RebaseExchange

/-- The identity of the trait as a morphism of models of points
`traitModelOfPoint ε₀ ⟶ traitModelOfPoint (ε₀ ≫ ι₀)` over `ι₀ : η ⟶ Spec F` and the identity of
the special point, for the geometric generic point `ε₀ : Spec Ω ⟶ η` of the trait. -/
@[simps]
noncomputable def traitModelOfPointMap
    (ι₀ : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)) :
    (traitModelOfPoint (traitGenericPointToSpec k')).Hom
      (traitModelOfPoint (traitGenericPointToSpec k' ≫ ι₀)) ι₀ (𝟙 _) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [traitModelOfPoint]
  comm_i := by simp [traitModelOfPoint]
  comm_ε := by simp [traitModelOfPoint]

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- The pullback exchange `Ψ_{S,F} ⟶ Ψ_{S,K} ι₀^*` of the nearby cycles of the trait as a model of
points along `ε₀ ≫ ι₀` and `ε₀` (`NearbyCyclesModel.traitModelOfPointMap`), on bounded
constructible complexes, through `L𝟙^* ≅ 𝟭` on the special point. -/
noncomputable def traitPointSpecializationExchange
    (ι₀ : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)) :
    traitPointSpecialization (traitGenericPointToSpec k' ≫ ι₀) ℓ ⟶
      boundedConstructibleUpperStarOfMap ℓ (X := point F)
          (Y := point (FractionRing (PowerSeries k'))) ι₀ ⋙
        traitPointSpecialization (traitGenericPointToSpec k') ℓ where
  app A := ObjectProperty.homMk
    ((traitModelOfPointMap ι₀).specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((traitModelOfPointMap ι₀).specialIdExchange_naturality
      (Profinite.padicAlgClRingObj ℓ) f.hom).symm

/-- The unit comparison of the derived pullback on bounded constructible complexes is that of the
ambient derived categories. -/
lemma boundedConstructibleUpperStarOfMap_ε_hom {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
    [Fact (ringChar k₂ ≠ ℓ)]
    {X : Over (Spec (.of k₁))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {Y : Over (Spec (.of k₂))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Y.left ⟶ X.left) :
    (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) g)).hom =
      Functor.LaxMonoidal.ε L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  ObjectProperty.monoidalLift_ε_hom _ _

/-- The unit comparison of the derived pullback is the inverse of
`ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStar_ε {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.LaxMonoidal.ε L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧) =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f).inv :=
  rfl

/-- The unit law of the exchange `NearbyCyclesModel.traitPointSpecializationExchange`, in an
abstract category. -/
private lemma unit_comp_specialIdExchange_aux {C : Type*} [Category C] {u₀ u₁ v₀ w₀ w₁ : C}
    (σ : u₀ ⟶ v₀) (i₀ : u₀ ⟶ u₁) (i₁ : v₀ ⟶ w₀) (Lσ : u₁ ⟶ w₀) (α : w₀ ⟶ w₁)
    (j : u₁ ⟶ u₀) (σ' : u₀ ⟶ w₁) (hnat : σ ≫ i₁ = i₀ ≫ Lσ) (hj : i₀ ≫ j = 𝟙 _)
    (hα : Lσ ≫ α = j ≫ σ') : σ ≫ i₁ ≫ α = σ' := by
  rw [reassoc_of% hnat, hα, reassoc_of% hj]

/-- The unit law of the exchange `NearbyCyclesModel.traitPointSpecializationExchange`:
`σ_F ≫ β(ℚ̄_ℓ) = σ_K ≫ Ψ_{S,K}(ε_{ι₀})`, for the specialization units `σ` and the unit comparison
`ε_{ι₀} : ℚ̄_ℓ ⟶ ι₀^* ℚ̄_ℓ`. -/
lemma traitPointSpecializationUnit_comp_exchange
    (ι₀ : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)) :
    traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι₀) ℓ ≫
        (traitPointSpecializationExchange ℓ ι₀).app (𝟙_ _) =
      traitPointSpecializationUnit (traitGenericPointToSpec k') ℓ ≫
        (traitPointSpecialization (traitGenericPointToSpec k') ℓ).map
          (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ (X := point F)
            (Y := point (FractionRing (PowerSeries k'))) ι₀)) := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  change (traitModelOfPoint _).unit (Profinite.padicAlgClRingObj ℓ) ≫
      (traitModelOfPointMap ι₀).specialIdExchange (Profinite.padicAlgClRingObj ℓ) (𝟙_ _) =
    (traitModelOfPoint _).unit (Profinite.padicAlgClRingObj ℓ) ≫
      ((traitModelOfPoint (traitGenericPointToSpec k')).nearbyCycles
        (Profinite.padicAlgClRingObj ℓ)).map
        (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ (X := point F)
          (Y := point (FractionRing (PowerSeries k'))) ι₀)).hom
  rw [boundedConstructibleUpperStarOfMap_ε_hom, leftDerivedUpperStar_ε]
  have hnat :=
    (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) (point k').left).inv.naturality
      ((traitModelOfPoint (traitGenericPointToSpec k' ≫ ι₀)).unit (Profinite.padicAlgClRingObj ℓ))
  have hj : (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) (point k').left).inv.app
      (𝟙_ _) ≫ (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) (𝟙 _)).hom = 𝟙 _ := by
    rw [← leftDerivedUpperStarId_hom_app_unit, Iso.inv_hom_id_app]
  exact unit_comp_specialIdExchange_aux _ _ _ _ _ _ _ hnat hj
    ((traitModelOfPointMap ι₀).map_unit_comp_pullbackExchange_app
      (Profinite.padicAlgClRingObj ℓ))

end RebaseExchange

section CompOfEq

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X₀ Y₀ : Scheme.{u}}

/-- `ProEtale.CondensedRing.leftDerivedUpperStarCompOfEq` is the composition isomorphism up to
`eqToHom`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app_eq {p : X₀ ⟶ X} {r : X ⟶ Y} {pr : X₀ ⟶ Y}
    (h : p ≫ r = pr)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompOfEq Λ h).hom.app K =
      eqToHom (by rw [h]) ≫ (leftDerivedUpperStarComp Λ p r).hom.app K := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- The diagram chase behind `pullbackSquareComparison_hom_app_eq_compOfEq`. -/
private lemma eqToHom_comp_hom_inv_aux {C : Type*} [Category C] {a b c d : C} (x : a ⟶ b)
    (y : b ⟶ a) (hxy : x ≫ y = 𝟙 _) (e₁ : d = a) (e₂ : a = d) (z : d ⟶ c) :
    (eqToHom e₁ ≫ x) ≫ y ≫ eqToHom e₂ ≫ z = z := by
  subst e₁
  simp [reassoc_of% hxy]

/-- The pullback comparison of a commutative square `g' ≫ p = p' ≫ g` through the composition
isomorphisms `L(g' ≫ p)^* ≅ Lg^* ⋙ Lp'^*` (along `p' ≫ g = g' ≫ p`) and
`L(g' ≫ p)^* ≅ Lp^* ⋙ Lg'^*`. -/
lemma pullbackSquareComparison_hom_app_eq_compOfEq {p : X ⟶ Y} {g : Y₀ ⟶ Y} {p' : X₀ ⟶ Y₀}
    {g' : X₀ ⟶ X} (sq : CommSq g' p' p g) (h : p' ≫ g = g' ≫ p)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ sq).hom.app K =
      (leftDerivedUpperStarCompOfEq Λ h).inv.app K ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app K := by
  rw [← cancel_epi ((leftDerivedUpperStarCompOfEq Λ h).hom.app K), Iso.hom_inv_id_app_assoc,
    pullbackSquareComparison_hom_app, leftDerivedUpperStarCompOfEq_hom_app_eq]
  exact eqToHom_comp_hom_inv_aux _ _ (Iso.hom_inv_id_app _ _) _ _ _

/-- The two unit laws of the composition isomorphisms of `𝟙 X ≫ s` and `s ≫ 𝟙 Y`, combined. -/
lemma leftDerivedUpperStarComp_id_hom_app_comp_eq {s : X ⟶ Y} (h : s ≫ 𝟙 Y = 𝟙 X ≫ s)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarComp Λ (𝟙 X) s).hom.app K ≫
        (leftDerivedUpperStarId Λ X).hom.app (L((s)^*⟦Λ⟧).obj K) =
      (leftDerivedUpperStarCompOfEq Λ h).hom.app K ≫
        L((s)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) :=
  (leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId Λ rfl K).trans
    (leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId Λ h K).symm

end CompOfEq

namespace IsTraitModelOfGenericBase

/-- The geometric generic point lies over `ι` compatibly with the identifications `ε`: the
compatibility for the morphism `NearbyCyclesModel.IsTraitModelOfGenericBase.toPoint`. -/
lemma comp_traitGenericPointToSpec_comp (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    g ≫ traitGenericPointToSpec k' ≫ ι = M.ε ≫ X₁.hom :=
  (h.ε_comp_hom.trans (Category.assoc _ _ _)).symm

/-- The geometric generic point of the re-based model lies over the generic point. -/
lemma comp_traitGenericPointToSpec_rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    g ≫ traitGenericPointToSpec k' = h.rebase.ε ≫ (genericBaseChange X₁ ι).hom :=
  (pullback.lift_snd _ _ _).symm

/-- The re-based model has full generic fibre if `M` has. -/
lemma isPullback_rebase (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    IsPullback h.rebase.ε g (genericBaseChange X₁ ι).hom (traitGenericPointToSpec k' ≫ 𝟙 _) := by
  rw [Category.comp_id]
  refine IsPullback.of_right (h₁₂ := pullback.fst X₁.hom ι) (h₂₂ := ι) ?_
    (h.comp_traitGenericPointToSpec_rebase).symm (IsPullback.of_hasPullback X₁.hom ι)
  exact (pullback.lift_fst _ _ _ : h.rebase.ε ≫ pullback.fst X₁.hom ι = M.ε).symm ▸ hgen

variable (X₁ ι) in
/-- The base change square `X₁,η ⟶ X₁` over `ι : η ⟶ Spec F`, as a commutative square of the
underlying schemes `X₁,η.left`, `(point η).left` and `(point F).left`. -/
lemma commSq_genericBaseChange :
    @CommSq Scheme _ (genericBaseChange X₁ ι).left X₁.left
      (point (FractionRing (PowerSeries k'))).left (point F).left (pullback.fst X₁.hom ι)
      (CondensedRing.toPoint (genericBaseChange X₁ ι)).left (CondensedRing.toPoint X₁).left ι :=
  (isPullback_genericBaseChange X₁ ι).toCommSq

/-- **Re-basing and the pullback exchanges** (ambient): the pullback exchange of
`a : M ⟶ S_F` followed by the re-basing exchange is the pullback exchange
`β : Ψ_{S,F} ⟶ Ψ_{S,η} ι^*` of the trait, followed by the pullback exchange of
`a' : M' ⟶ S_η` and the pullback comparison of the base change square of `X₁,η ⟶ X₁`. Both are
factorizations of the pullback exchange of `rebaseHom ≫ a = a' ≫ τ`. -/
lemma pullbackExchange_app_comp_specialIdExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology (point F).left) Ab.{u + 1})
      (condensedRingObj Λ (point F).left))) :
    ((h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).pullbackExchange Λ).app C ≫
      h.rebaseHom.specialIdExchange Λ _ =
    L(((CondensedRing.toPoint X').left)^*⟦Λ⟧).map
        ((traitModelOfPointMap ι).specialIdExchange Λ C) ≫
      ((h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
          h.comp_traitGenericPointToSpec_rebase).pullbackExchange Λ).app _ ≫
      (h.rebase.nearbyCycles Λ).map ((pullbackSquareComparison Λ
        (commSq_genericBaseChange X₁ ι)).hom.app C) := by
  have h₂ : (CondensedRing.toPoint (genericBaseChange X₁ ι)).left ≫ ι =
      pullback.fst X₁.hom ι ≫ (CondensedRing.toPoint X₁).left :=
    (isPullback_genericBaseChange X₁ ι).w.symm
  have h₂' : (CondensedRing.toPoint X').left ≫ 𝟙 _ = 𝟙 _ ≫ (CondensedRing.toPoint X').left := by
    rw [Category.comp_id, Category.id_comp]
  have htot : (h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
        h.comp_traitGenericPointToSpec_rebase).total ≫
      (traitModelOfPointMap ι).total =
      (h.rebaseHom.comp (h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp)).total :=
    (Category.comp_id q).trans (Category.id_comp q).symm
  have hgen : (h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
        h.comp_traitGenericPointToSpec_rebase).generic ≫
      (traitModelOfPointMap ι).generic =
      (h.rebaseHom.comp (h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp)).generic :=
    (Category.comp_id g).trans (Category.id_comp g).symm
  have L₁ := h.rebaseHom.pullbackExchange_comp_app Λ
    (h.toPoint (traitGenericPointToSpec k' ≫ ι) h.comp_traitGenericPointToSpec_comp)
  have L₂ := (h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
    h.comp_traitGenericPointToSpec_rebase).pullbackExchange_comp_app_of_eq Λ
      (traitModelOfPointMap ι)
      (h.rebaseHom.comp (h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp)) h₂ h₂' htot hgen
  exact rebase_pullbackExchange_aux _ _ _ _ (leftDerivedUpperStarId Λ X'.left)
    (leftDerivedUpperStarId Λ (point k').left)
    (leftDerivedUpperStarComp_id_hom_app_comp_eq Λ h₂') _ _ _ _ _ L₁ L₂ C _
    (pullbackSquareComparison_hom_app_eq_compOfEq Λ (commSq_genericBaseChange X₁ ι) h₂ C).symm

/-- **Re-basing and the proper exchanges** (ambient): the proper exchange `χ_F` of `a : M ⟶ S_F`
followed by the re-basing exchange is `β(Ra_*)`, followed by the nearby cycles of the base change
morphism `ι^* Ra_* ⟶ Ra_{η*} π^*` and the proper exchange `χ_η` of `a' : M' ⟶ S_η`. The object
`Lπ^* E` is replaced by an equal object `P` through `eqToHom`, so that the statement can be
instantiated at the objects of bounded constructible complexes. -/
lemma pushforwardExchange_app_comp_map_specialIdExchange_of_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (E : DerivedCategory (Mod (Sheaf (ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj Λ X₁.left)))
    (P : DerivedCategory (Mod (Sheaf (ProEt.topology (genericBaseChange X₁ ι).left) Ab.{u + 1})
      (condensedRingObj Λ (genericBaseChange X₁ ι).left)))
    (hP : L(upperStar (X := (genericBaseChange X₁ ι).left) (Y := X₁.left) Λ
      (pullback.fst X₁.hom ι)).obj E = P) :
    ((h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).pushforwardExchange Λ).app E ≫
      R(((CondensedRing.toPoint X').left)_*⟦Λ⟧).map (h.rebaseHom.specialIdExchange Λ E ≫
        (h.rebase.nearbyCycles Λ).map (eqToHom hP)) =
    (traitModelOfPointMap ι).specialIdExchange Λ _ ≫
      ((traitModelOfPoint (traitGenericPointToSpec k')).nearbyCycles Λ).map
        ((baseChangeMap Λ (commSq_genericBaseChange X₁ ι)).app E ≫
          R(((CondensedRing.toPoint (genericBaseChange X₁ ι)).left)_*⟦Λ⟧).map (eqToHom hP)) ≫
      ((h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
          h.comp_traitGenericPointToSpec_rebase).pushforwardExchange Λ).app P :=
  rebase_pushforwardExchange_aux_of_eq
    (derivedUpperStarLowerStarAdjunction Λ (CondensedRing.toPoint X₁).left)
    (derivedUpperStarLowerStarAdjunction Λ
      (CondensedRing.toPoint (genericBaseChange X₁ ι)).left)
    (derivedUpperStarLowerStarAdjunction Λ (CondensedRing.toPoint X').left)
    ((h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).pullbackExchange Λ)
    ((h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
          h.comp_traitGenericPointToSpec_rebase).pullbackExchange Λ)
    (pullbackSquareComparison Λ (commSq_genericBaseChange X₁ ι)).hom
    (h.rebaseHom.specialIdExchange Λ)
    (fun f ↦ (h.rebaseHom.specialIdExchange_naturality Λ f).symm)
    ((traitModelOfPointMap ι).specialIdExchange Λ)
    (pullbackExchange_app_comp_specialIdExchange Λ h)
    ((h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).pushforwardExchange Λ) rfl
    ((h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
          h.comp_traitGenericPointToSpec_rebase).pushforwardExchange Λ) rfl
    (baseChangeMap Λ (commSq_genericBaseChange X₁ ι))
    (Adjunction.exchangeRight_eq_mateEquiv _ _ _) E P hP

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The nearby cycles of the trait as a model of a point, on morphisms of bounded constructible
complexes, are the ambient nearby cycles. -/
lemma traitPointSpecialization_map_hom [IsSepClosed k']
    (ε : Spec (.of (traitGenericField k')) ⟶ Spec (.of F))
    {K L : Dᵇc((point F).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K ⟶ L) :
    ((traitPointSpecialization ε ℓ).map f).hom =
      ((traitModelOfPoint ε).nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map f.hom :=
  rfl

/-- The lift of `pushforwardExchange_app_comp_map_specialIdExchange_of_eq` to bounded
constructible complexes, for an arbitrary ambient base change morphism `bc` whose restriction is
written as `NearbyCyclesModel.liftExchange`: kept abstract in `bc`, so that elaboration and the
kernel never unfold the base change morphism. -/
private lemma pushforwardExchange_app_comp_map_rebaseExchange_app_aux
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (bc : R(((CondensedRing.toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L(upperStar (X := (point (FractionRing (PowerSeries k'))).left) (Y := (point F).left)
          (Profinite.padicAlgClRingObj ℓ) ι) ⟶
      L(upperStar (X := (genericBaseChange X₁ ι).left) (Y := X₁.left)
          (Profinite.padicAlgClRingObj ℓ) (pullback.fst X₁.hom ι)) ⋙
        R(((CondensedRing.toPoint (genericBaseChange X₁ ι)).left)_*⟦Profinite.padicAlgClRingObj
          ℓ⟧))
    (hP : L(upperStar (X := (genericBaseChange X₁ ι).left) (Y := X₁.left)
      (Profinite.padicAlgClRingObj ℓ) (pullback.fst X₁.hom ι)).obj A.obj =
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A).obj)
    (hbc : ((h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).pushforwardExchange
          (Profinite.padicAlgClRingObj ℓ)).app A.obj ≫
      R(((CondensedRing.toPoint X').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (h.rebaseHom.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj ≫
          (h.rebase.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map (eqToHom hP)) =
      (traitModelOfPointMap ι).specialIdExchange (Profinite.padicAlgClRingObj ℓ)
        (R(((CondensedRing.toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj) ≫
      ((traitModelOfPoint (traitGenericPointToSpec k')).nearbyCycles
        (Profinite.padicAlgClRingObj ℓ)).map (bc.app A.obj ≫
          R(((CondensedRing.toPoint (genericBaseChange X₁ ι)).left)_*⟦Profinite.padicAlgClRingObj
            ℓ⟧).map (eqToHom hP)) ≫
      ((h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
          h.comp_traitGenericPointToSpec_rebase).pushforwardExchange
            (Profinite.padicAlgClRingObj ℓ)).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A).obj) :
    (h.pushforwardExchange ℓ (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).app A ≫
      (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
        ((h.rebaseExchange ℓ).app A) =
    (traitPointSpecializationExchange ℓ ι).app
        ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁)).obj A) ≫
      (traitPointSpecialization (traitGenericPointToSpec k') ℓ).map
        ((NearbyCyclesModel.liftExchange bc
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ (CondensedRing.toPoint X₁) K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ
            (CondensedRing.toPoint (genericBaseChange X₁ ι)) K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ ι K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
            (pullback.fst X₁.hom ι) K.obj K.property) :
            boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁) ⋙
              boundedConstructibleUpperStarOfMap ℓ (X := point F)
                (Y := point (FractionRing (PowerSeries k'))) ι ⟶
            boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
                (pullback.fst X₁.hom ι) ⋙
              boundedConstructibleLowerStar ℓ (CondensedRing.toPoint (genericBaseChange X₁ ι))).app
          A) ≫
      (h.isTraitModelOfGenericBase_rebase.pushforwardExchange ℓ (traitGenericPointToSpec k')
        h.comp_traitGenericPointToSpec_rebase).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A) := by
  have eρ : ((h.rebaseExchange ℓ).app A).hom =
      h.rebaseHom.specialIdExchange (Profinite.padicAlgClRingObj ℓ) A.obj ≫
          (h.rebase.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map (eqToHom hP) := by
    rw [eqToHom_map]
    unfold IsTraitModelOfGenericBase.rebaseExchange
    exact (ObjectProperty.homMk_hom _).trans (Category.comp_id _).symm
  have hu : ((traitPointSpecializationExchange ℓ ι).app
      ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁)).obj A)).hom =
      (traitModelOfPointMap ι).specialIdExchange (Profinite.padicAlgClRingObj ℓ)
        (R(((CondensedRing.toPoint X₁).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A.obj) := by
    unfold traitPointSpecializationExchange
    exact ObjectProperty.homMk_hom _
  have hx : ((h.pushforwardExchange ℓ (traitGenericPointToSpec k' ≫ ι)
      h.comp_traitGenericPointToSpec_comp).app A).hom =
      ((h.toPoint (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).pushforwardExchange
          (Profinite.padicAlgClRingObj ℓ)).app A.obj :=
    Hom.boundedConstructiblePushforwardExchange_app_hom ℓ _ _ _ A
  have hw : ((h.isTraitModelOfGenericBase_rebase.pushforwardExchange ℓ
      (traitGenericPointToSpec k') h.comp_traitGenericPointToSpec_rebase).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A)).hom =
      ((h.isTraitModelOfGenericBase_rebase.toPoint (traitGenericPointToSpec k')
          h.comp_traitGenericPointToSpec_rebase).pushforwardExchange
            (Profinite.padicAlgClRingObj ℓ)).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A).obj :=
    Hom.boundedConstructiblePushforwardExchange_app_hom ℓ _ _ _ _
  have ebc : ((NearbyCyclesModel.liftExchange bc
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ (CondensedRing.toPoint X₁) K)
          (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ
            (CondensedRing.toPoint (genericBaseChange X₁ ι)) K)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ ι K.obj K.property)
          (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
            (pullback.fst X₁.hom ι) K.obj K.property) :
            boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁) ⋙
              boundedConstructibleUpperStarOfMap ℓ (X := point F)
                (Y := point (FractionRing (PowerSeries k'))) ι ⟶
            boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
                (pullback.fst X₁.hom ι) ⋙
              boundedConstructibleLowerStar ℓ (CondensedRing.toPoint (genericBaseChange X₁ ι))).app
          A).hom = bc.app A.obj ≫
          R(((CondensedRing.toPoint (genericBaseChange X₁ ι)).left)_*⟦Profinite.padicAlgClRingObj
            ℓ⟧).map (eqToHom hP) :=
    (NearbyCyclesModel.liftExchange_app_hom bc _ _ _ _ A).trans
      ((Category.comp_id _).symm.trans ((congrArg (bc.app A.obj ≫ ·) (eqToHom_refl _ _).symm).trans
        (congrArg (bc.app A.obj ≫ ·) (eqToHom_map _ hP).symm)))
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, traitPointSpecialization_map_hom,
    ebc, boundedConstructibleLowerStar_map_hom, hx, hw, eρ, hu]
  exact hbc

/-- **Re-basing and the proper exchanges** on bounded constructible complexes: the proper exchange
`χ_F` of `M` over `F` followed by the re-basing exchange is the exchange `β` of the trait,
followed by the nearby cycles of the base change morphism `ι^* Ra_* ⟶ Ra_{η*} π^*` and the
proper exchange `χ_η` of the re-based model over `η`. -/
lemma pushforwardExchange_app_comp_map_rebaseExchange_app
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (h.pushforwardExchange ℓ (traitGenericPointToSpec k' ≫ ι)
        h.comp_traitGenericPointToSpec_comp).app A ≫
      (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
        ((h.rebaseExchange ℓ).app A) =
    (traitPointSpecializationExchange ℓ ι).app
        ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁)).obj A) ≫
      (traitPointSpecialization (traitGenericPointToSpec k') ℓ).map
        ((boundedConstructibleBaseChangeOfMap ℓ
          (isPullback_genericBaseChange X₁ ι).toCommSq).app A) ≫
      (h.isTraitModelOfGenericBase_rebase.pushforwardExchange ℓ (traitGenericPointToSpec k')
        h.comp_traitGenericPointToSpec_rebase).app
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A) := by
  have key := pushforwardExchange_app_comp_map_rebaseExchange_app_aux ℓ h A
    (baseChangeMap (Profinite.padicAlgClRingObj ℓ) (commSq_genericBaseChange X₁ ι)) rfl
    (by
      cast_proofs pushforwardExchange_app_comp_map_specialIdExchange_of_eq
        (Profinite.padicAlgClRingObj ℓ) h A.obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := genericBaseChange X₁ ι)
          (pullback.fst X₁.hom ι)).obj A).obj rfl)
  unfold boundedConstructibleBaseChangeOfMap
  cast_proofs key

end IsTraitModelOfGenericBase

namespace NearbyDualizingDataOfGenericBase

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **The dualizing maps and re-basing to the generic point of the trait**: for a proper trait model
`M` over the generic base `(F, X₁, ι)` with `X₁` proper and full generic fibre, the dualizing map
`θ_M` is the composite of the re-basing exchange `Ψ_M ω_{X₁} ⟶ Ψ_{M'} π^* ω_{X₁}`, of `Ψ_{M'}` of
the comparison `φ : π^* ω_{X₁} ⟶ ω_{X₁,η}` of the dualizing complexes along `ι` (for the inverse
of the unit isomorphism of the monoidal functor `ι^*`), and of the dualizing map `θ_{M'}` of the
re-based model over `η`. -/
theorem θ_eq_rebase_of_isProper (D : NearbyDualizingDataOfGenericBase k' ℓ)
    [IsProper (toPoint X₁).left] [IsProper (toPoint X').left]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    haveI := isProper_toPoint_genericBaseChange (X₁ := X₁) (ι := ι)
    D.θ h = (h.rebaseExchange ℓ).app (dualizingComplex ℓ X₁) ≫
      (boundedConstructibleNearbyCycles
          (h.isTraitModelOfGenericBase_rebase.preservesBoundedConstructible (ℓ := ℓ))).map
        (dualizingComplexBaseChange ℓ
          (inv (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ
            (X := point F) (Y := point (FractionRing (PowerSeries k'))) ι)))
          (isPullback_genericBaseChange X₁ ι)) ≫
      D.θ h.isTraitModelOfGenericBase_rebase := by
  have := isProper_toPoint_genericBaseChange (X₁ := X₁) (ι := ι)
  have hgen' := h.isPullback_rebase hgen
  have htr := D.pushforwardExchange_comp_map_θ_comp_trace h hgen _
    h.comp_traitGenericPointToSpec_comp
  have htr' := D.pushforwardExchange_comp_map_θ_comp_trace h.isTraitModelOfGenericBase_rebase
    hgen' (traitGenericPointToSpec k') h.comp_traitGenericPointToSpec_rebase
  have : IsIso ((h.pushforwardExchange ℓ _ h.comp_traitGenericPointToSpec_comp).app
      (dualizingComplex ℓ X₁)) :=
    h.isIso_pushforwardExchange_app ℓ _ h.comp_traitGenericPointToSpec_comp hgen _
  have hstar := IsTraitModelOfGenericBase.pushforwardExchange_app_comp_map_rebaseExchange_app ℓ h
    (dualizingComplex ℓ X₁)
  have hφ := baseChange_comp_map_dualizingComplexBaseChange_comp_trace ℓ (X := X₁)
    (X' := genericBaseChange X₁ ι)
    (inv (Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ
      (X := point F) (Y := point (FractionRing (PowerSeries k'))) ι)))
    (isPullback_genericBaseChange X₁ ι)
  have hunit := traitPointSpecializationUnit_comp_exchange ℓ ι
  refine eq_of_map_comp_trace_eq ℓ X' ?_
  rw [← cancel_epi ((h.pushforwardExchange ℓ _ h.comp_traitGenericPointToSpec_comp).app
    (dualizingComplex ℓ X₁)), htr]
  refine (rebase_trace_aux (trη := trace ℓ (genericBaseChange X₁ ι))
    (ση := traitPointSpecializationUnit (traitGenericPointToSpec k') ℓ)
    (ε := Functor.LaxMonoidal.ε (boundedConstructibleUpperStarOfMap ℓ
      (X := point F) (Y := point (FractionRing (PowerSeries k'))) ι))
    _ _ _ _ _ _ _ _ _ _ hstar ?_ ?_ ?_).symm
  · cast_proofs htr'
  · cast_proofs hφ
  · cast_proofs hunit

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
