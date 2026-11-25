/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.TraceFormula.Specialization.TraitDirectImageUnit
public import WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Deligne's finiteness theorem for the nearby cycles of the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait, with
geometric generic point `j : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`. The geometric
nearby cycles `Li^* Rj_* Lj^*` of `S` carry bounded constructible complexes of `ℚ̄_ℓ`-sheaves
on `S` to bounded constructible complexes on `Spec k'`
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj`). This is the case
`𝔸⁰_S = S` of Deligne's finiteness theorem for nearby cycles (SGA 4½, [Th. finitude], Thm. 3.2),
and the base case of its proof by induction on the dimension.

The proof is a direct computation on the pro-étale site:
* `Lj^*` preserves bounded constructible complexes, and by dévissage along the truncation
  triangles (`ProEtale.boundedConstructible_obj_of_forall_singleFunctor`) it suffices to treat a
  constructible sheaf `M` on `Spec Ω` placed in degree `0`;
* such an `M` is finitely presented (`Spec Ω` is a separably closed point,
  `ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject`);
* `i^*` kills the higher direct images `Rⁿ j_* N`, `n > 0`, of every sheaf `N` on `Spec Ω`
  (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_rightDerived_of_pos`), so
  `Li^* Rj_* (M[0]) = (i^* j_* M)[0]`, and the long exact sequence of `Rj_*` shows that
  `i^* j_*` is exact (`ProEtale.CondensedRing.preservesFiniteColimits_traitNearbyFunctor`);
* `i^* j_*` sends `ℚ̄_ℓ` to `ℚ̄_ℓ` (`ProEtale.isIso_upperStar_traitClosedPoint_map_unit_app`),
  hence finitely presented modules to finitely presented modules, which are constructible.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A finitely presented module object is pro-étale locally finitely presented, for the
identity cover. -/
lemma isLocallyFinitelyPresented_of_isFinitelyPresented {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  let α := condensedPullbackHom Λ (𝟙 X)
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((𝟙 X)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M)
  exact ((IsFinitelyPresented.upperStar Λ (𝟙 X) hM).of_iso e).of_comap (inv α)

/-- A finitely presented module object is constructible, for the trivial stratification. -/
lemma isConstructibleModuleObject_of_isFinitelyPresented {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M :=
  ⟨Scheme.Stratification.trivial X, fun _ ↦ (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2
    (isLocallyFinitelyPresented_of_isFinitelyPresented Λ (IsFinitelyPresented.upperStar Λ _ hM))⟩

variable (k' : Type u) [Field k'] [IsSepClosed k']

/-- After restriction to the closed point of the trait, the higher direct images `Rⁿ j_* N`,
`n > 0`, of any sheaf `N` on the geometric generic point `j : Spec Ω ⟶ S` vanish: the sections
of `i^*` are computed on the henselian lifts `W` of the w-contractible ind-étale `k'`-algebras,
which are weakly contractible, as are their geometric generic fibres. -/
theorem isZero_upperStar_traitClosedPoint_obj_rightDerived_of_pos (n : ℕ) (hn : 0 < n)
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of (traitGenericField k'))))) :
    IsZero ((traitClosedPoint k')^*⟦Λ⟧.obj
      (((traitGenericPoint k')_*⟦Λ⟧.rightDerived n).obj N)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine isZero_upperStar_traitClosedPoint_obj_of_forall Λ _ fun C _ _ _ _ _ hC ↦ ?_
  have hW : (ProEt.topology (trait k')).IsWeaklyContractible.{u + 1} (traitClosedLift C) :=
    Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction
      (R := CommRingCat.of (Algebra.ClosedLift (PowerSeries k') C))
      (Algebra.ClosedLift.exists_retraction (A := PowerSeries k') (C := C)
        (Ideal.span {(PowerSeries.X : PowerSeries k')})
        (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction C T)) (Iso.refl _)
  have := preservesHomology_sectionsFunctor Λ hW
  have := preservesHomology_sectionsFunctor Λ
    (isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec (k' := k') C hC)
  let I := injectiveResolution N
  let K := ((traitGenericPoint k')_*⟦Λ⟧.mapHomologicalComplex _).obj I.cocomplex
  have hK : ((K.sc' m (m + 1) (m + 2)).map (sectionsFunctor Λ (traitClosedLift C))).Exact :=
    (I.exact_succ m).map (sectionsFunctor Λ _)
  refine AddCommGrpCat.subsingleton_of_isZero
    (((ShortComplex.exact_iff_isZero_homology _).1 hK).of_iso ?_)
  exact (sectionsFunctor Λ (traitClosedLift C)).mapIso (I.isoRightDerivedObj _ (m + 1) ≪≫
      K.homologyIsoSc' m (m + 1) (m + 2) (by simp) (by simp)) ≪≫
    ((K.sc' m (m + 1) (m + 2)).mapHomologyIso _).symm

/-- The functor `i^* j_*` from sheaves on the geometric generic point `Spec Ω` of the trait to
sheaves on its closed point `Spec k'`. -/
noncomputable abbrev traitNearbyFunctor :
    Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k')))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of (traitGenericField k')))) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k'))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k'))) :=
  (traitGenericPoint k')_*⟦Λ⟧ ⋙ (traitClosedPoint k')^*⟦Λ⟧

/-- The functor `i^* j_*` preserves epimorphisms: for an epimorphism `p : A ⟶ B` with kernel
`K`, the long exact sequence of `Rj_*` gives an exact sequence `j_* A ⟶ j_* B ⟶ R¹ j_* K`, and
`i^* R¹ j_* K = 0`. -/
lemma epi_traitNearbyFunctor_map {X Y : Mod (Sheaf (Scheme.ProEt.topology
      (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of (traitGenericField k'))))}
    (p : X ⟶ Y) [Epi p] : Epi ((traitNearbyFunctor Λ k').map p) := by
  let F₀ := (traitGenericPoint k')_*⟦Λ⟧
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
  have hE := (F₀.rightDerivedHomologySequence_exact₃ hS 0 1 rfl).map (traitClosedPoint k')^*⟦Λ⟧
  have hZ : IsZero ((traitClosedPoint k')^*⟦Λ⟧.obj ((DerivedCategory.homologyFunctor _ 1).obj
      (F₀.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj S.X₁)))) :=
    (isZero_upperStar_traitClosedPoint_obj_rightDerived_of_pos Λ k' 1 one_pos S.X₁).of_iso
      ((traitClosedPoint k')^*⟦Λ⟧.mapIso (F₀.homologyRightDerivedFunctorObjSingleFunctorIso _ 1))
  have h₁ := hE.epi_f (hZ.eq_of_tgt _ _)
  let e := F₀.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
  have hp : F₀.map p = e.inv.app X ≫ (DerivedCategory.homologyFunctor _ 0).map
      (F₀.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map p)) ≫ e.hom.app Y := by
    have h := e.hom.naturality p
    simp only [Functor.comp_map] at h
    rw [h, Iso.inv_hom_id_app_assoc]
  change Epi ((traitClosedPoint k')^*⟦Λ⟧.map (F₀.map p))
  rw [hp, Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h₁ _ inferInstance)

/-- The functor `i^* j_*` is exact; in particular it preserves finite colimits. -/
instance preservesFiniteColimits_traitNearbyFunctor :
    PreservesFiniteColimits (traitNearbyFunctor Λ k') := by
  refine (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun S hS ↦ ?_
  have := hS.mono_f
  have := hS.epi_g
  refine ⟨?_, epi_traitNearbyFunctor_map Λ k' S.g⟩
  exact hS.exact.map_of_mono_of_preservesKernel _ ‹_› inferInstance

/-- The functor `i^* j_*` sends the free module `Λ_{Spec Ω}` to the free module `Λ_{Spec k'}`:
`Λ_{Spec Ω} = j^* Λ_S`, and `i^*` inverts the unit `Λ_S ⟶ j_* j^* Λ_S`. -/
noncomputable def traitNearbyFunctorRegularIso :
    (traitNearbyFunctor Λ k').obj
        (Mod.regular (condensedRingObj Λ (Spec (.of (traitGenericField k'))))) ≅
      Mod.regular (condensedRingObj Λ (Spec (.of k'))) :=
  (traitClosedPoint k')^*⟦Λ⟧.mapIso ((traitGenericPoint k')_*⟦Λ⟧.mapIso
      (upperStarObjRegularIso Λ (traitGenericPoint k')).symm) ≪≫
    (@asIso _ _ _ _ _ (isIso_upperStar_traitClosedPoint_map_unit_app Λ k')).symm ≪≫
    upperStarObjRegularIso Λ (traitClosedPoint k')

/-- The functor `i^* j_*` preserves finitely presented modules. -/
lemma isFinitelyPresented_traitNearbyFunctor_obj
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of (traitGenericField k'))))}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of (traitGenericField k')))) M) :
    Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of k')))
      ((traitNearbyFunctor Λ k').obj M) :=
  hM.map _ (traitNearbyFunctorRegularIso Λ k')

/-- The cohomology sheaves of `Li^* Rj_* (N[0])`: in degree `n ≥ 0`, they are
`i^* Rⁿ j_* N`. -/
noncomputable def homologyTraitNearbyObjSingleIso (n : ℕ)
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of (traitGenericField k'))))) :
    (DerivedCategory.homologyFunctor _ n).obj ((L((traitClosedPoint k')^*⟦Λ⟧)).obj
        ((R((traitGenericPoint k')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj N))) ≅
      (traitClosedPoint k')^*⟦Λ⟧.obj (((traitGenericPoint k')_*⟦Λ⟧.rightDerived n).obj N) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ (traitClosedPoint k')).app _) ≪≫
    ((traitClosedPoint k')^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm.app _ ≪≫
    (traitClosedPoint k')^*⟦Λ⟧.mapIso
      ((traitGenericPoint k')_*⟦Λ⟧.homologyRightDerivedFunctorObjSingleFunctorIso N n)

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- For a constructible sheaf `M` on the geometric generic point `Spec Ω` of the trait,
`Li^* Rj_* (M[0]) = (i^* j_* M)[0]` is bounded constructible on the closed point: `M` is finitely
presented, `i^*` kills `Rⁿ j_* M` for `n > 0`, and `i^* j_*` preserves finitely presented
modules. -/
theorem boundedConstructible_traitNearby_singleFunctor_obj
    {M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k')))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of (traitGenericField k'))))}
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of (traitGenericField k')))) M) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k')))
      ((L((traitClosedPoint k')^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((R((traitGenericPoint k')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  set Λ := Profinite.padicAlgClRingObj ℓ
  have hfp : Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of (traitGenericField k')))) M :=
    (isFinitelyPresented_upperStar_of_isConstructibleModuleObject Λ (Field.toIsField _)
      IsField.isSepClosed_toField hM
      (𝟙 _)).of_iso ((upperStarId Λ _).app M)
  have hGE : ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsGE 0 :=
    (traitGenericPoint k')_*⟦Λ⟧.isGE_rightDerivedFunctor_obj_singleFunctor M
  have hpos : ∀ n : ℤ, 0 < n → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((L((traitClosedPoint k')^*⟦Λ⟧)).obj ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    exact (isZero_upperStar_traitClosedPoint_obj_rightDerived_of_pos Λ k' m (by omega) M).of_iso
      (homologyTraitNearbyObjSingleIso Λ k' m M)
  have hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((L((traitClosedPoint k')^*⟦Λ⟧)).obj ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
    intro n hn
    refine ((traitClosedPoint k')^*⟦Λ⟧.map_isZero
      (DerivedCategory.isZero_of_isGE ((R((traitGenericPoint k')_*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) 0 n hn)).of_iso ?_
    exact (DerivedCategory.homologyFunctor _ n).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ (traitClosedPoint k')).app _) ≪≫
      ((traitClosedPoint k')^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm.app _
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨0, 0, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · rcases hi with hi | hi
    · exact hneg i hi
    · exact hpos i hi
  · rcases lt_trichotomy n 0 with hn | rfl | hn
    · exact isConstructibleModuleObject_of_isZero _ (hneg n hn)
    · refine IsConstructibleModuleObject.of_iso ?_
        (isConstructibleModuleObject_of_isFinitelyPresented Λ
          (isFinitelyPresented_traitNearbyFunctor_obj Λ k' hfp))
      exact ((traitClosedPoint k')^*⟦Λ⟧.mapIso
          ((traitGenericPoint k')_*⟦Λ⟧.rightDerivedZeroIsoSelf.app M).symm) ≪≫
        (homologyTraitNearbyObjSingleIso Λ k' 0 M).symm
    · exact isConstructibleModuleObject_of_isZero _ (hpos n hn)

/-- **Deligne's finiteness theorem for the nearby cycles of the trait** (the case `𝔸⁰_S = S` of
SGA 4½, [Th. finitude], Thm. 3.2): the geometric nearby cycles `Li^* Rj_* Lj^*` of the strictly
henselian trait `S = Spec k'⟦t⟧` carry bounded constructible complexes of `ℚ̄_ℓ`-sheaves on `S`
to bounded constructible complexes on its closed point. `Lj^* B` is bounded constructible on
`Spec Ω`, and by dévissage it suffices to treat a constructible sheaf on `Spec Ω` placed in
degree `0` (`ProEtale.CondensedRing.boundedConstructible_traitNearby_singleFunctor_obj`). -/
theorem boundedConstructible_traitNearbyCycles_obj
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (trait k')) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (trait k')))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k')))
      ((L((traitClosedPoint k')^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((R((traitGenericPoint k')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((L((traitGenericPoint k')^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))) :=
  boundedConstructible_obj_of_forall_singleFunctor
    (Φ := R((traitGenericPoint k')_*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
      L((traitClosedPoint k')^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (fun _ hF ↦ boundedConstructible_traitNearby_singleFunctor_obj k' hF)
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (traitGenericPoint k') B hB)

namespace NearbyCyclesModel

/-- The trait `S = Spec k'⟦t⟧` as a model of itself: total space `S`, geometric generic fibre
`Spec Ω`, special fibre `Spec k'`, and identification `ε = j`. Its nearby cycles are the geometric
nearby cycles `Li^* Rj_* Lj^*` of the trait. -/
@[simps]
noncomputable def traitSelfModel : NearbyCyclesModel (trait k') (Spec (.of k')) where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := traitClosedPoint k'
  ε := traitGenericPoint k'

omit [IsSepClosed k'] in
/-- The trait is a model of finite type over itself. -/
lemma isTraitModel_traitSelfModel :
    (traitSelfModel k').IsTraitModel (X' := Over.mk (𝟙 (Spec (.of k')))) := by
  have : IsIso (Over.mk (𝟙 (Spec (.of k')))).hom := inferInstanceAs (IsIso (𝟙 _))
  exact ⟨⟨𝟙 _, 𝟙 _, inferInstance, inferInstance, inferInstance,
    IsPullback.of_vert_isIso ⟨by simp⟩, IsPullback.of_vert_isIso ⟨by simp⟩⟩⟩

/-- **Deligne's finiteness theorem for the trait itself**: the nearby cycles of the trait, as a
model of itself, preserve bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructible_traitNearbyCycles_obj`). -/
theorem preservesBoundedConstructible_traitSelfModel :
    (traitSelfModel k').PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) :=
  fun _ hB ↦ boundedConstructible_traitNearbyCycles_obj k' hB

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
