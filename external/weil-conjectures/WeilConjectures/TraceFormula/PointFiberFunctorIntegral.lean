/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.Preadditive.NatTransIsIso
public import WeilConjectures.NumberTheory.Padics.IntegersToAlgCl
public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-!
# The integral point fibre functor

Let `k` be a separably closed field, `s = Spec k`, and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`
with ring of integers `𝒪_E`. As for `ℚ̄_ℓ` (`WeilConjectures.TraceFormula.PointFiberFunctor`),
the unit `𝒪̲_E,s` of the abelian category `Mod_{𝒪̲_E,s}` of `𝒪̲_E`-modules on `s_proét` is
projective, and its endomorphisms are the constants `𝒪_E = C(*, 𝒪_E)`
(`ProEtale.CondensedRing.surjective_pointIntegersUnitEndRingHom`). Its global sections
`Γ = Hom(𝒪̲_E,s, -) : Mod_{𝒪̲_E,s} ⥤ Mod_{𝒪_E}` (`ProEtale.CondensedRing.pointSectionsIntegral`)
are exact and induce the *integral point fibre functor*
`Fib_s : Dᵇc(s)⟦𝒪̲_E⟧ ⥤ D(𝒪_E)` (`ProEtale.CondensedRing.pointFiberFunctorIntegral`).

**Point sections commute with extension of scalars**
(`ProEtale.CondensedRing.pointFiberFunctorIntegralExtendScalarsIso`): for `K` in `Dᵇc(s)⟦𝒪̲_E⟧`,
```
Fib_s(ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K) ≅ ℚ̄_ℓ ⊗ᴸ_{𝒪_E} Fib_s(K),
```
the extension of scalars on the left being `boundedConstructibleExtendScalars` along
`𝒪_{E,s} ⟶ E_s` followed by `constructibleToPadicAlgCl` along `E_s ⟶ ℚ̄_ℓ,s`, and on the right
`ModuleCat.derivedExtendScalars` along the flat `𝒪_E ⟶ ℚ̄_ℓ`. All the functors involved being
exact, this is induced by the comparison
`ℚ̄_ℓ ⊗_{𝒪_E} Γ(s, M) ⟶ Γ(s, ℚ̄_ℓ ⊗_{𝒪_E} M)` of abelian categories
(`ProEtale.CondensedRing.pointSectionsExtendScalarsComparison`), which is an isomorphism at the
unit, hence (both sides being right exact) at every finitely presented module. The cohomology
sheaves of a bounded constructible complex over the separably closed point are finitely
presented, so the induced comparison of derived categories is an isomorphism on them.

This file adds no `sorry`. It inherits those of its inputs, notably the exactness of the
extension of scalars along `E_s ⟶ ℚ̄_ℓ,s`
(`ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`),
the equivalence between `Mod_{𝒪̲_E,s}` and condensed `𝒪̲_E`-modules
(`ProEtale.CondensedRing.isEquivalence_upperStarFromPointMod`), and the preservation of bounded
constructibility used to define the extensions of scalars on `Dᵇc`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] (E : FiniteIntermediateField ℓ)

/-- The abelian category of `𝒪̲_E`-module objects on the pro-étale site of the point
`s = Spec k`, the ambient category of `Dᵇc(s)⟦𝒪̲_E⟧`. -/
abbrev PointModIntegral : Type _ :=
  Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left)

/-- The constant global sections `𝒪_E →+* Γ 𝒪̲_E` of the condensed ring `𝒪̲_E = C(-, 𝒪_E)`. -/
noncomputable def padicIntegersConstRingHom :
    integers ℓ E.1 →+* Γ (Profinite.padicIntegersRingObj.{u} ℓ E.1) :=
  letI := normedFieldOfAlgebra ℓ E.1
  Profinite.continuousMapConstRingHom (integers ℓ E.1)

/-- The scalars `𝒪_E` acting on the unit of `Mod_{𝒪̲_E,s}`: a scalar `a` acts by the
multiplication by the constant global section `a`. -/
noncomputable def pointIntegersUnitEndRingHom :
    integers ℓ E.1 →+* End (𝟙_ (PointModIntegral ℓ k E)) :=
  (Mod.regularEndRingHom.comp (Γ.mapFunctor (upperStarFromPoint (point k).left))).comp
    (padicIntegersConstRingHom ℓ E)

/-- The scalars `𝒪_E` acting on the unit of `Mod_{𝒪̲_E,s}`, as a ring homomorphism to the
opposite of its endomorphism ring, from the universe `u + 1` copy of `𝒪_E`. -/
noncomputable def pointIntegersScalarsOp :
    Shrink.{u + 1} (integers ℓ E.1) →+* (End (𝟙_ (PointModIntegral ℓ k E)))ᵐᵒᵖ :=
  ((pointIntegersUnitEndRingHom ℓ k E).toOpposite fun x y ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]).comp
      (shrinkRingEquiv ℓ E.1).symm.toRingHom

/-- The global sections `Γ = Hom(𝒪̲_E,s, -) : Mod_{𝒪̲_E,s} ⥤ Mod_{𝒪_E}` over the point. -/
noncomputable def pointSectionsIntegral :
    PointModIntegral ℓ k E ⥤ ModuleCat.{u + 1} (Shrink.{u + 1} (integers ℓ E.1)) :=
  coyonedaSections (pointIntegersScalarsOp ℓ k E)

instance : (pointSectionsIntegral ℓ k E).Additive := by
  unfold pointSectionsIntegral
  infer_instance

variable [IsSepClosed k]

/-- For `k` separably closed, the unit of `Mod_{𝒪̲_E,s}` is projective. -/
instance projective_tensorUnit_pointModIntegral : Projective (𝟙_ (PointModIntegral ℓ k E)) :=
  projective_regular_of_isSepClosed (k := k) _

instance : PreservesFiniteLimits (pointSectionsIntegral ℓ k E) := by
  unfold pointSectionsIntegral
  infer_instance

instance : PreservesFiniteColimits (pointSectionsIntegral ℓ k E) := by
  unfold pointSectionsIntegral
  infer_instance

/-- For `k` separably closed, every endomorphism of the unit of `Mod_{𝒪̲_E,s}` is a scalar of
`𝒪_E`. -/
theorem surjective_pointIntegersUnitEndRingHom :
    Function.Surjective (pointIntegersUnitEndRingHom ℓ k E) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.1
  have := isEquivalence_upperStarFromPointMod (Ω := k) Λ
  have hE := (upperStarFromPoint (Spec (.of k))).bijective_regularEndRingHom_comp_mapFunctor Λ
    (Functor.FullyFaithful.ofFullyFaithful (upperStarFromPointMod Λ (Spec (.of k))))
  let := normedFieldOfAlgebra ℓ E.1
  exact hE.2.comp (Profinite.continuousMapConstRingHom_surjective (integers ℓ E.1))

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.MonObj

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] {R S : C} [MonObj R] [MonObj S] (g : R ⟶ S) [IsMonHom g]
  [IsMonHom (F.map g)] [Preadditive C] [MonoidalPreadditive C] [Preadditive D]
  [MonoidalPreadditive D] [F.Additive]

/-- The global sections induced by a lax monoidal functor are natural in the algebra object. -/
lemma Γ.map_map_mapFunctor (s : Γ R) :
    Γ.map (F.map g) (Γ.mapFunctor F s) = Γ.mapFunctor F (Γ.map g s) := by
  ext1
  rw [Γ.map_hom, Γ.mapFunctor_hom, Γ.mapFunctor_hom, Γ.map_hom, Category.assoc, F.map_comp]

end CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] (E : FiniteIntermediateField ℓ)

/-- The constant global sections of `𝒪̲_E` are sent to the constant global sections of `ℚ̲̄_ℓ`
by the inclusions `𝒪̲_E ⟶ E̲ ⟶ ℚ̲̄_ℓ`. -/
lemma Γ_map_padicIntegersConstRingHom (r : integers ℓ E.1) :
    Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        (Γ.map (padicIntegersRingObjToContinuousMapRingObj ℓ E) (padicIntegersConstRingHom ℓ E r)) =
      Profinite.PadicAlgCl.constRingHom ℓ (algebraMap E.1 (PadicAlgCl ℓ) r) := by
  have h : Γ.map (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      (padicIntegersConstRingHom ℓ E r) = Profinite.continuousMapConstRingHom E.1 (r : E.1) :=
    Sheaf.Γ_map_ringHomΓSheafCompose _
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E.1) _ (fun _ _ ↦ rfl) _
      (fun _ _ ↦ rfl) fun _ ↦ rfl
  rw [h]
  exact Sheaf.Γ_map_ringHomΓSheafCompose _
    (Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E) _ (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl)
    fun _ ↦ rfl

/-- The extension of scalars `ℚ̄_ℓ ⊗_{𝒪_E} - : Mod_{𝒪̲_E,s} ⥤ Mod_{ℚ̲̄_ℓ,s}` on module objects over
the point, along the inclusions `𝒪_{E,s} ⟶ E_s ⟶ ℚ̄_ℓ,s`. -/
noncomputable abbrev pointModExtendScalars : PointModIntegral ℓ k E ⥤ PointMod ℓ k :=
  Mod.extendScalars (padicIntegersToPadicSubfield (point k).left ℓ E) ⋙
    Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl (point k).left ℓ E)

/-- The extension of scalars of the unit `𝒪̲_E,s` is the unit `ℚ̲̄_ℓ,s`. -/
noncomputable def pointModExtendScalarsUnitIso :
    (pointModExtendScalars ℓ k E).obj (𝟙_ (PointModIntegral ℓ k E)) ≅ 𝟙_ (PointMod ℓ k) :=
  Mod.extendScalarsCompObjRegularIso (padicIntegersToPadicSubfield (point k).left ℓ E)
    (padicSubfieldRingObjToPadicAlgCl (point k).left ℓ E)

/-- The extension of scalars `ℚ̄_ℓ ⊗_{𝒪_E} -` sends the multiplication by a scalar `a ∈ 𝒪_E` on
the unit to the multiplication by its image in `ℚ̄_ℓ`. -/
lemma pointModExtendScalarsUnitIso_inv_comp_map (a : Shrink.{u + 1} (integers ℓ E.1)) :
    (pointModExtendScalarsUnitIso ℓ k E).inv ≫
        (pointModExtendScalars ℓ k E).map (pointIntegersScalarsOp ℓ k E a).unop.asHom =
      (pointScalarsOp ℓ k (integersToULift ℓ E.1 a)).unop.asHom ≫
        (pointModExtendScalarsUnitIso ℓ k E).inv := by
  let r := (shrinkRingEquiv ℓ E.1).symm a
  have h₁ : (pointIntegersScalarsOp ℓ k E a).unop = Mod.regularEndRingHom
      (Γ.mapFunctor (upperStarFromPoint (point k).left) (padicIntegersConstRingHom ℓ E r)) :=
    rfl
  have h₂ : (pointScalarsOp ℓ k (integersToULift ℓ E.1 a)).unop = Mod.regularEndRingHom
      (Γ.mapFunctor (upperStarFromPoint (point k).left)
        (Profinite.PadicAlgCl.constRingHom ℓ (algebraMap E.1 (PadicAlgCl ℓ) r))) :=
    rfl
  have h : Γ.map (padicSubfieldRingObjToPadicAlgCl (point k).left ℓ E)
      (Γ.map (padicIntegersToPadicSubfield (point k).left ℓ E)
        (Γ.mapFunctor (upperStarFromPoint (point k).left) (padicIntegersConstRingHom ℓ E r))) =
      Γ.mapFunctor (upperStarFromPoint (point k).left)
        (Profinite.PadicAlgCl.constRingHom ℓ (algebraMap E.1 (PadicAlgCl ℓ) r)) := by
    rw [Γ.map_map_mapFunctor, Γ.map_map_mapFunctor, Γ_map_padicIntegersConstRingHom]
  rw [h₁, h₂, ← h]
  exact Mod.extendScalarsCompObjRegularIso_inv_comp_map _ _ _

/-- The comparison `ℚ̄_ℓ ⊗_{𝒪_E} Γ(s, M) ⟶ Γ(s, ℚ̄_ℓ ⊗_{𝒪_E} M)` between the extension of scalars
of the sections over the point and the sections of the extension of scalars, adjoint to
`m ↦ ℚ̄_ℓ ⊗ m`. -/
noncomputable def pointSectionsExtendScalarsComparison :
    pointSectionsIntegral ℓ k E ⋙ ModuleCat.extendScalars (integersToULift ℓ E.1) ⟶
      pointModExtendScalars ℓ k E ⋙ pointSections ℓ k :=
  coyonedaSectionsExtendScalarsComparison (integersToULift ℓ E.1) (pointIntegersScalarsOp ℓ k E)
    (pointScalarsOp ℓ k) (pointModExtendScalars ℓ k E) (pointModExtendScalarsUnitIso ℓ k E)
    (pointModExtendScalarsUnitIso_inv_comp_map ℓ k E)

variable [IsSepClosed k]

/-- For `k` separably closed, the comparison is an isomorphism at the unit: both sides are
`ℚ̄_ℓ`. -/
instance isIso_pointSectionsExtendScalarsComparison_app_unit :
    IsIso ((pointSectionsExtendScalarsComparison ℓ k E).app (𝟙_ (PointModIntegral ℓ k E))) := by
  refine isIso_coyonedaSectionsExtendScalarsComparison_app_self _ _ _ _ _ _ (fun t ↦ ?_)
    ((bijective_pointUnitEndRingHom ℓ k).comp Equiv.ulift.bijective)
  obtain ⟨r, hr⟩ := surjective_pointIntegersUnitEndRingHom ℓ k E (End.of t)
  exact ⟨shrinkRingEquiv ℓ E.1 r, (congrArg (pointIntegersUnitEndRingHom ℓ k E)
    ((shrinkRingEquiv ℓ E.1).symm_apply_apply r)).trans hr⟩

/-- For `k` separably closed, the comparison is an isomorphism at every finitely presented
`𝒪̲_E,s`-module. -/
lemma isIso_pointSectionsExtendScalarsComparison_app {M : PointModIntegral ℓ k E}
    (hM : Mod.IsFinitelyPresented _ M) :
    IsIso ((pointSectionsExtendScalarsComparison ℓ k E).app M) := by
  obtain ⟨n, m, g, ⟨e⟩⟩ := hM
  have : IsIso ((pointSectionsExtendScalarsComparison ℓ k E).app
      (Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left))) :=
    isIso_pointSectionsExtendScalarsComparison_app_unit ℓ k E
  have := NatTrans.isIso_app_cokernel_biproduct_fin (pointSectionsExtendScalarsComparison ℓ k E)
    _ g
  exact NatTrans.isIso_app_of_iso _ e

/-- **The integral point fibre functor** `Fib_s : Dᵇc(s)⟦𝒪̲_E⟧ ⥤ D(𝒪_E)`, induced by the exact
global sections functor over the point. -/
noncomputable def pointFiberFunctorIntegral :
    Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      DerivedCategory (ModuleCat.{u + 1} (Shrink.{u + 1} (integers ℓ E.1))) :=
  (boundedConstructible _).ι ⋙ (pointSectionsIntegral ℓ k E).mapDerivedCategory

noncomputable instance : (pointFiberFunctorIntegral ℓ k E).CommShift ℤ := by
  unfold pointFiberFunctorIntegral
  infer_instance

instance : (pointFiberFunctorIntegral ℓ k E).Additive := by
  unfold pointFiberFunctorIntegral
  infer_instance

/-- The comparison `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} RΓ(s, K) ⟶ RΓ(s, ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K)` on derived categories,
induced by `pointSectionsExtendScalarsComparison`. -/
noncomputable def pointSectionsDerivedExtendScalarsComparison :
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_integersToULift.{u} ℓ E.1)
    (pointSectionsIntegral ℓ k E ⋙
        ModuleCat.extendScalars (integersToULift ℓ E.1)).mapDerivedCategory ⟶
      (pointModExtendScalars ℓ k E ⋙ pointSections ℓ k).mapDerivedCategory :=
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_integersToULift.{u} ℓ E.1)
  Functor.mapDerivedCategoryNatTrans (pointSectionsExtendScalarsComparison ℓ k E)

/-- The derived comparison is an isomorphism on bounded constructible complexes: their
cohomology sheaves are finitely presented over the separably closed point. -/
instance isIso_pointSectionsDerivedExtendScalarsComparison_app
    (K : Dᵇc((point k).left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso ((pointSectionsDerivedExtendScalarsComparison ℓ k E).app K.obj) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_integersToULift.{u} ℓ E.1)
  refine Functor.isIso_mapDerivedCategoryNatTrans_app (pointSectionsExtendScalarsComparison ℓ k E)
    K.obj fun n ↦ ?_
  obtain ⟨p, q, g, ⟨e⟩⟩ := isFinitelyPresented_upperStar_of_isConstructibleModuleObject
    (Profinite.padicIntegersRingObj ℓ E.1) (Field.toIsField k) IsField.isSepClosed_toField
    (((mem_boundedConstructible_iff _ _).1 K.property).2 n) (𝟙 _)
  exact isIso_pointSectionsExtendScalarsComparison_app ℓ k E
    ⟨p, q, g, ⟨((upperStarId _ _).app _).symm ≪≫ e⟩⟩

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- **Point sections commute with extension of scalars**: on bounded constructible complexes
over the separably closed point, `Fib_s(ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K) ≅ ℚ̄_ℓ ⊗ᴸ_{𝒪_E} Fib_s(K)`, where the
extension of scalars on the left is along `𝒪_{E,s} ⟶ E_s ⟶ ℚ̄_ℓ,s`. -/
noncomputable def pointFiberFunctorIntegralExtendScalarsIso :
    boundedConstructibleExtendScalars (point k).left ℓ E ⋙
        constructibleToPadicAlgCl (point k).left ℓ E ⋙ pointFiberFunctor ℓ k ≅
      pointFiberFunctorIntegral ℓ k E ⋙
        ModuleCat.derivedExtendScalars (integersToULift.{u} ℓ E.1)
          (flat_integersToULift.{u} ℓ E.1) :=
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_integersToULift.{u} ℓ E.1)
  let Fφ := Mod.extendScalars (padicIntegersToPadicSubfield (point k).left ℓ E)
  let Fψ := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl (point k).left ℓ E)
  let incl := (boundedConstructible
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (point k).left)).ι
  have : IsIso (Functor.whiskerLeft incl (pointSectionsDerivedExtendScalarsComparison ℓ k E)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      fun K ↦ isIso_pointSectionsDerivedExtendScalarsComparison_app ℓ k E K
  Functor.isoWhiskerLeft incl
      (Functor.isoWhiskerRight Fφ.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
        Functor.isoWhiskerLeft Fφ.mapDerivedCategory
          (Functor.isoWhiskerRight Fψ.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
            Functor.mapDerivedCategoryCompIso Fψ (pointSections ℓ k)) ≪≫
        Functor.mapDerivedCategoryCompIso Fφ (Fψ ⋙ pointSections ℓ k)) ≪≫
    (asIso (Functor.whiskerLeft incl (pointSectionsDerivedExtendScalarsComparison ℓ k E))).symm ≪≫
    Functor.isoWhiskerLeft incl (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
