/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Composition, cancellation and target locality of the base change property

For a coefficient ring `Λ` which is torsion as an additive group, the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` of proper morphisms

- is stable under composition (`AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`);
- cancels along proper surjections: if `f` is proper and surjective and `f` and `f ≫ h` have the
  property, then so does `h` (`AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp`).

Composition is the vertical pasting law of the derived base change map. Cancellation is proved
on the side of injective acyclicity: an injective sheaf `I` on `Y` is a direct summand of
`f_* J` for an injective `J` on `X` (`AlgebraicGeometry.Etale.mono_homEquiv_of_surjective`), and
the higher direct images of the base change of `f_* J` along `h` vanish because
`R(h'f')_* = Rh'_* ∘ Rf'_*` and both `Rf'_*` and `R(h'f')_*` kill the higher cohomology of the
base change of `J`.

Finally, for an arbitrary coefficient ring the base change property is local on the target
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_affineOpens`).

## References

- Stacks Project, Lemma 59.91.7, <https://stacks.math.columbia.edu/tag/0A4C>
- Stacks Project, Lemma 59.91.8, <https://stacks.math.columbia.edu/tag/0A4D>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The right derived functor of a left exact functor `F` sends an `F`-acyclic object `M`
placed in degree `0` to `F.obj M` placed in degree `0`: the single complex `M[0]` is a bounded
below complex of `F`-acyclic objects, on which the unit of the right derived functor is an
isomorphism (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`). -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIsoOfRightAcyclic (M : C)
    (hM : F.rightAcyclic M) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (F.obj M) :=
  let K : CochainComplex.Plus C := ⟨(CochainComplex.singleFunctor C 0).obj M, ⟨0, inferInstance⟩⟩
  have : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K)) :=
    F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic K fun n ↦ by
      by_cases hn : n = 0
      · subst hn
        exact F.rightAcyclic.prop_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hM
      · exact F.rightAcyclic.prop_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)
  F.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.quotientCompQhIso C).app K).symm ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K))).symm ≪≫
    mapHomotopyCategoryPlusSingleFunctorQhObjIso F 0 M

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory D] {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- A natural transformation `τ : F ⟶ G` of additive functors is an isomorphism at `J` as soon
as the induced morphism of bounded below derived categories is an isomorphism at the single
complex `J[0]`: taking homology in degree `0` recovers `τ.app J`. -/
theorem isIso_app_of_isIso_Qh_map_mapHomotopyCategoryPlus_app (τ : F ⟶ G) (J : C)
    (h : IsIso (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app
      ((HomotopyCategory.Plus.quotient C).obj
        ⟨(CochainComplex.singleFunctor C 0).obj J, ⟨0, inferInstance⟩⟩)))) :
    IsIso (τ.app J) := by
  have h₁ := (DerivedCategory.Plus.homologyFunctor D 0).map_isIso
    (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app
      ((HomotopyCategory.Plus.quotient C).obj
        ⟨(CochainComplex.singleFunctor C 0).obj J, ⟨0, inferInstance⟩⟩)))
  dsimp [DerivedCategory.Plus.homologyFunctor] at h₁
  let K : CochainComplex C ℤ := (CochainComplex.singleFunctor C 0).obj J
  let φ := (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K
  have e : (DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app
      ((HomotopyCategory.Plus.quotient C).obj ⟨K, ⟨0, inferInstance⟩⟩))).hom =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D _).map φ) := by
    have e₀ : ∀ {X Y : HomotopyCategory.Plus D} (x : X ⟶ Y), (DerivedCategory.Plus.Qh.map x).hom =
        DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map x) := fun _ ↦ rfl
    rw [e₀, NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    rfl
  rw [e] at h₁
  have h₂ : IsIso ((DerivedCategory.homologyFunctor D 0).map (DerivedCategory.Q.map φ)) := h₁
  have h₃ : IsIso (HomologicalComplex.homologyMap φ 0) := by
    have := (DerivedCategory.homologyFunctorFactors D 0).hom.naturality φ
    have h₄ : IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor D 0).map φ ≫
      (DerivedCategory.homologyFunctorFactors D 0).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
      dsimp only [Functor.comp_map]
      infer_instance
    rw [this] at h₄
    exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctorFactors D 0).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((HomologicalComplex.homologyFunctor D _ 0).map φ)
  let α := HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0
  let β := HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0
  have hsq : φ ≫ β.hom.app J =
      α.hom.app J ≫ (HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (τ.app J) := by
    apply HomologicalComplex.to_single_hom_ext
    simp [φ, α, β, K, HomologicalComplex.single_map_f_self]
  have h₅ : IsIso (HomologicalComplex.homologyMap
      ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (τ.app J)) 0) := by
    have h₆ : IsIso (HomologicalComplex.homologyMap (φ ≫ β.hom.app J) 0) := by
      rw [HomologicalComplex.homologyMap_comp]
      infer_instance
    rw [hsq, HomologicalComplex.homologyMap_comp] at h₆
    exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (α.hom.app J) 0) _
  have := (HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).hom.naturality
    (τ.app J)
  simp only [Functor.comp_map, Functor.id_map, HomologicalComplex.homologyFunctor_map] at this
  have h₇ : IsIso ((HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).hom.app
      (F.obj J) ≫ τ.app J) := by
    rw [← this]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).hom.app _) _


omit [HasDerivedCategory D] in
/-- A natural transformation `τ : S ⟶ T` between left exact functors of abelian categories is an
isomorphism at the kernel `E.X₁` of a morphism `E.g : E.X₂ ⟶ E.X₃` as soon as it is one at
`E.X₂` and at `E.X₃`: both `S` and `T` preserve the kernel. In the diagram
```
0 ⟶ S E.X₁ ⟶ S E.X₂ ⟶ S E.X₃
      |         |         |
      τ         τ         τ
      v         v         v
0 ⟶ T E.X₁ ⟶ T E.X₂ ⟶ T E.X₃
```
both rows are exact and the two right vertical maps are isomorphisms. -/
theorem isIso_app_of_exact_of_mono {S T : C ⥤ D} [PreservesFiniteLimits S]
    [PreservesFiniteLimits T] (τ : S ⟶ T) {E : ShortComplex C} (hE : E.Exact) [Mono E.f]
    [IsIso (τ.app E.X₂)] [IsIso (τ.app E.X₃)] : IsIso (τ.app E.X₁) := by
  have kS := KernelFork.mapIsLimit _ hE.fIsKernel S
  have hw : (T.map E.f ≫ inv (τ.app E.X₂)) ≫ S.map E.g = 0 := by
    rw [← cancel_mono (τ.app E.X₃), Category.assoc, Category.assoc, τ.naturality,
      IsIso.inv_hom_id_assoc, ← T.map_comp, E.zero, T.map_zero, zero_comp]
  obtain ⟨σ, hσ⟩ := KernelFork.IsLimit.lift' kS _ hw
  simp only [KernelFork.map_ι, KernelFork.ι_ofι] at hσ
  refine ⟨σ, ?_, ?_⟩
  · rw [← cancel_mono (S.map E.f), Category.assoc, hσ, Category.id_comp,
      ← τ.naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [← cancel_mono (T.map E.f), Category.assoc, ← τ.naturality, reassoc_of% hσ,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
end CategoryTheory.NatTrans

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Composition stability of the base change property.** For a torsion coefficient ring `Λ`,
if `f : X ⟶ Y` and `h : Y ⟶ Z` satisfy the base change property, so does `f ≫ h`. For a
torsion ring the property is `AlgebraicGeometry.Etale.IsBaseChangeIso`, which is stable under
composition by the vertical pasting law of the derived base change map.
(blueprint: `lemma-composition-cancellation--1`) -/
@[stacks 0A4D]
theorem Etale.HasTorsionBaseChange.comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} (hf : Etale.HasTorsionBaseChange Λ f)
    (hh : Etale.HasTorsionBaseChange Λ h) : Etale.HasTorsionBaseChange Λ (f ≫ h) :=
  have := Etale.isBaseChangeIso_of_hasTorsionBaseChange Λ hΛ hf
  have := Etale.isBaseChangeIso_of_hasTorsionBaseChange Λ hΛ hh
  have := Etale.IsBaseChangeIso.comp (ModuleCat.{u + 1} Λ) f h
  Etale.hasTorsionBaseChange_of_isBaseChangeIso Λ (f ≫ h)

/-- **Composition stability of injective acyclicity.** For a torsion coefficient ring `Λ` and
proper morphisms `f : X ⟶ Y`, `h : Y ⟶ Z` with injective acyclicity, `f ≫ h` has injective
acyclicity. (blueprint: `lemma-composition-cancellation--1`) -/
theorem Etale.HasInjectiveAcyclicity.comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [IsProper h] (hf : Etale.HasInjectiveAcyclicity Λ f)
    (hh : Etale.HasInjectiveAcyclicity Λ h) : Etale.HasInjectiveAcyclicity Λ (f ≫ h) :=
  (Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ (f ≫ h)).1
    (Etale.HasTorsionBaseChange.comp Λ hΛ
      ((Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ f).2 hf)
      ((Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ h).2 hh))

/-- **The underived exchange at an injective sheaf, from the base change property.** For a
torsion coefficient ring `Λ`, if `f` satisfies the base change property, then for every
cartesian square and every injective sheaf `J` on `X` the underived base change map
`g^* f_* J ⟶ f'_* g'^* J` is an isomorphism. Indeed the derived base change map at `J[0]` is
computed by the underived one followed by the unit `f'_* g'^* J ⟶ Rf'_*(g'^* J)`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`), which is an isomorphism since
`g'^* J` is `f'_*`-acyclic by injective acyclicity; taking homology in degree `0` gives the
claim. -/
theorem Etale.isIso_baseChangeMap_app_of_hasTorsionBaseChange (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Etale.HasTorsionBaseChange Λ f)
    {Y' X' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective J] :
    IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app J) := by
  let K : CochainComplex.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨(CochainComplex.singleFunctor _ 0).obj J, ⟨0, inferInstance⟩⟩
  let P := (HomotopyCategory.Plus.quotient _).obj K
  have : IsTorsionModuleSheaf J := .of_isTorsion hΛ J
  have hJ := (hf.hasInjectiveAcyclicity Λ f).rightAcyclic Λ sq J
  have h₁ : IsIso ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) :=
    (f)_*[ModuleCat.{u + 1} Λ].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic K
      fun n ↦ by
        by_cases hn : n = 0
        · subst hn
          exact (f)_*[ModuleCat.{u + 1} Λ].rightAcyclic.prop_of_iso
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 J).symm
            ((f)_*[ModuleCat.{u + 1} Λ].rightAcyclic_of_injective J)
        · exact (f)_*[ModuleCat.{u + 1} Λ].rightAcyclic.prop_of_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 J n hn)
  have h₂ : IsIso ((f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
      (((g')^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj P)) :=
    (f')_*[ModuleCat.{u + 1} Λ].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
      (((g')^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj K) fun n ↦ by
        by_cases hn : n = 0
        · subst hn
          exact (f')_*[ModuleCat.{u + 1} Λ].rightAcyclic.prop_of_iso
            ((g')^*[ModuleCat.{u + 1} Λ].mapIso
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 J).symm) hJ
        · exact (f')_*[ModuleCat.{u + 1} Λ].rightAcyclic.prop_of_isZero
            (Functor.map_isZero ((g')^*[ModuleCat.{u + 1} Λ])
              (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 J n hn))
  have h₃ : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (DerivedCategory.Plus.Qh.obj P)) :=
    hf sq _ (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X hΛ _)
  have hfac := Etale.derivedBaseChangeMapPlus_fac_app (ModuleCat.{u + 1} Λ) sq.toCommSq P
  have h₄ : IsIso (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) ≫
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (DerivedCategory.Plus.Qh.obj P)) := inferInstance
  rw [hfac] at h₄
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at h₄
  exact NatTrans.isIso_app_of_isIso_Qh_map_mapHomotopyCategoryPlus_app _ J h₄

/-- **The retract supplied by a surjection.** Let `f : X ⟶ Y` be surjective, let `I` be a sheaf
on `Y` and `ι : f^* I ⟶ J` a monomorphism. Then the adjoint map `I ⟶ f_* J` is a monomorphism:
at a geometric point `ȳ` of `Y`, choose a geometric point `x̄` of `X` above it; the stalk map
`I_ȳ ⟶ (f_* J)_ȳ` followed by the restriction to `J_x̄` is the injection
`I_ȳ = (f^* I)_x̄ ⟶ J_x̄`. Geometric stalks are conservative. If `I` is injective, the
monomorphism splits, so `I` is a direct summand of `f_* J`.
(blueprint: `lemma-composition-cancellation--2`) -/
theorem Etale.mono_homEquiv_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    {I : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : (f)^*[ModuleCat.{u + 1} Λ].obj I ⟶ J) [Mono ι] :
    Mono ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ ι) := by
  have := Etale.mono_unit_app_of_surjective Λ f f.surjective I
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- **The underived exchange cancels along a surjection.** For a torsion coefficient ring `Λ`,
let `f : X ⟶ Y` be surjective and `h : Y ⟶ Z` such that `f` and `f ≫ h` satisfy the base change
property. Then for every cartesian square over `h` the underived base change map
`c^* h_* ⟶ h'_* b^*` is an isomorphism. At `f_* J` with `J` injective this follows from the
vertical pasting law and `AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_hasTorsionBaseChange`
for `f` and `f ≫ h`; a general sheaf `G` is the kernel of a map `f_* J₁ ⟶ f_* J₂` between such
sheaves (the unit `G ⟶ f_* f^* G` is a monomorphism since `f` is surjective), and both sides of
the base change map are left exact. -/
theorem Etale.isIso_baseChangeMap_of_hasTorsionBaseChange_comp (hΛ : IsAddTorsion Λ)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z} [Surjective f]
    (hf : Etale.HasTorsionBaseChange Λ f) (hfh : Etale.HasTorsionBaseChange Λ (f ≫ h))
    {Z' Y' : Scheme.{u}} {c : Z' ⟶ Z} {h' : Y' ⟶ Z'} {b : Y' ⟶ Y}
    (sq : IsPullback b h' h c) :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have hJ (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
      IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((f)_*[ModuleCat.{u + 1} Λ].obj J)) := by
    have sq₁ : IsPullback (pullback.fst f b) (pullback.snd f b) f b :=
      IsPullback.of_hasPullback f b
    have := Etale.isIso_baseChangeMap_app_of_hasTorsionBaseChange Λ hΛ hf sq₁ J
    have h₂ := Etale.isIso_baseChangeMap_app_of_hasTorsionBaseChange Λ hΛ hfh
      (sq₁.paste_vert sq) J
    rw [Etale.baseChangeMap_paste_vert_app _ sq₁.toCommSq sq.toCommSq] at h₂
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h₂
  have (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app G) := by
    let A := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
    let ι₁ : G ⟶ (f)_*[ModuleCat.{u + 1} Λ].obj
        (Injective.under ((f)^*[ModuleCat.{u + 1} Λ].obj G)) :=
      A.homEquiv _ _ (Injective.ι _)
    have : Mono ι₁ := Etale.mono_homEquiv_of_surjective Λ f (Injective.ι _)
    let ι₂ : cokernel ι₁ ⟶ (f)_*[ModuleCat.{u + 1} Λ].obj
        (Injective.under ((f)^*[ModuleCat.{u + 1} Λ].obj (cokernel ι₁))) :=
      A.homEquiv _ _ (Injective.ι _)
    have : Mono ι₂ := Etale.mono_homEquiv_of_surjective Λ f (Injective.ι _)
    let E : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      ShortComplex.mk ι₁ (cokernel.π ι₁ ≫ ι₂) (by simp)
    let E₀ : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      ShortComplex.mk ι₁ (cokernel.π ι₁) (by simp)
    let φ : E₀ ⟶ E := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := ι₂ }
    have hE : E.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (ShortComplex.exact_cokernel ι₁)
    have : Mono E.f := inferInstanceAs (Mono ι₁)
    have : IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app E.X₂) := hJ _
    have : IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app E.X₃) := hJ _
    exact NatTrans.isIso_app_of_exact_of_mono _ hE
  exact NatIso.isIso_of_isIso_app _

/-- **Vanishing descends to a retract.** If `I` is a retract of `M` and the higher direct images
of `M` along `h` vanish in degree `q`, then so do those of `I`: the higher direct image functors
are additive, so `Rᵠh_* I` is a retract of `Rᵠh_* M = 0`.
(blueprint: `lemma-composition-cancellation--2`) -/
theorem Etale.isZero_homology_rightDerivedFunctorPlus_of_retract {X Y : Scheme.{u}}
    (h : X ⟶ Y) {I M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (s : I ⟶ M)
    (r : M ⟶ I) (hsr : s ≫ r = 𝟙 I) (q : ℤ)
    (hM : IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj M)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj I))) := by
  let G := DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0 ⋙ R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙
    DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  have : IsSplitMono (G.map s) := .mk' ⟨G.map r, by rw [← G.map_comp, hsr, G.map_id]⟩
  exact IsZero.of_mono (G.map s) hM

/-- **Cancellation of injective acyclicity along a surjection.** For a torsion coefficient ring
`Λ`, let `f : X ⟶ Y` be surjective with the base change property and let `h : Y ⟶ Z` be such
that `f ≫ h` has injective acyclicity. Then `h` has injective acyclicity.

Let `I` be an injective sheaf on `Y`; embed `f^* I` into an injective `J` on `X`. By
`AlgebraicGeometry.Etale.mono_homEquiv_of_surjective` the sheaf `I` is a direct summand of
`f_* J`. After a base change `Z' ⟶ Z`, the underived exchange of `f` at `J`
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_hasTorsionBaseChange`) identifies the base
change of `f_* J` with `f'_*` of the base change of `J`, whose higher direct images along `h'`
vanish since `Rh'_* ∘ Rf'_* = R(h'f')_*`, the base change of `J` is `f'_*`-acyclic and
`IA(f ≫ h)` holds. The vanishing descends to the direct summand.
(blueprint: `lemma-composition-cancellation--2`) -/
@[stacks 0A4C]
theorem Etale.HasInjectiveAcyclicity.of_comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [Surjective f]
    (hf : Etale.HasTorsionBaseChange Λ f) (hfh : Etale.HasInjectiveAcyclicity Λ (f ≫ h)) :
    Etale.HasInjectiveAcyclicity Λ h := by
  intro Z' Y' c h' b sq I _ _ q hq
  let ι := Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I)
  let J := Injective.under ((f)^*[ModuleCat.{u + 1} Λ].obj I)
  let s := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ ι
  have := Etale.mono_homEquiv_of_surjective Λ f ι
  have hsr : s ≫ Injective.factorThru (𝟙 I) s = 𝟙 I := Injective.comp_factorThru _ _
  have sq₁ : IsPullback (pullback.fst f b) (pullback.snd f b) f b := IsPullback.of_hasPullback f b
  have : IsTorsionModuleSheaf J := .of_isTorsion hΛ J
  have hJ := (hf.hasInjectiveAcyclicity Λ f).rightAcyclic Λ sq₁ J
  refine Etale.isZero_homology_rightDerivedFunctorPlus_of_retract Λ h'
    ((b)^*[ModuleCat.{u + 1} Λ].map s)
    ((b)^*[ModuleCat.{u + 1} Λ].map (Injective.factorThru (𝟙 I) s))
    (by rw [← Functor.map_comp, hsr, CategoryTheory.Functor.map_id]) q ?_
  have := Etale.isIso_baseChangeMap_app_of_hasTorsionBaseChange Λ hΛ hf sq₁ J
  refine IsZero.of_iso (hfh (sq₁.paste_vert sq) J inferInstance inferInstance q hq) ?_
  exact (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((R+((h')_*[ModuleCat.{u + 1} Λ])).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app J))) ≪≫
      (R+((h')_*[ModuleCat.{u + 1} Λ])).mapIso
        (Functor.rightDerivedFunctorPlusObjSingleFunctorIsoOfRightAcyclic _ _ hJ).symm ≪≫
      (Functor.rightDerivedFunctorPlusCompIso' _ _
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (pullback.snd f b) h')).app _)

/-- **Cancellation of the base change property along a surjection.** For a torsion coefficient
ring `Λ`, let `f : X ⟶ Y` be surjective and `h : Y ⟶ Z`. If `f` and `f ≫ h` satisfy the base
change property, so does `h`: by `AlgebraicGeometry.Etale.HasInjectiveAcyclicity.of_comp` the
morphism `h` has injective acyclicity, its underived exchange is an isomorphism by
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_hasTorsionBaseChange_comp`, and the two together
give the base change property
(`AlgebraicGeometry.Etale.HasInjectiveAcyclicity.hasTorsionBaseChange_of_isIso_baseChangeMap`).
(blueprint: `lemma-composition-cancellation--2`) -/
@[stacks 0A4C]
theorem Etale.HasTorsionBaseChange.of_comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [Surjective f]
    (hf : Etale.HasTorsionBaseChange Λ f) (hfh : Etale.HasTorsionBaseChange Λ (f ≫ h)) :
    Etale.HasTorsionBaseChange Λ h :=
  (Etale.HasInjectiveAcyclicity.of_comp Λ hΛ hf (hfh.hasInjectiveAcyclicity Λ _)
    ).hasTorsionBaseChange_of_isIso_baseChangeMap Λ hΛ h fun _ _ _ _ _ sq ↦
      Etale.isIso_baseChangeMap_of_hasTorsionBaseChange_comp Λ hΛ hf hfh sq

/-- **Target locality of the base change property.** A morphism `f : X ⟶ Y` satisfies the base
change property as soon as its restrictions `f ∣_ U : f ⁻¹ᵁ U ⟶ U` over all affine opens `U`
of `Y` do: the derived base change map of a cartesian square over `Y` is an isomorphism as soon
as its pullbacks over the members of the open cover of the base change by the preimages of
the `U` are (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_etale_cover`).
(blueprint: `proposition-proper-base-change-etale-site--1`) -/
theorem Etale.hasTorsionBaseChange_of_affineOpens {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ U : Y.affineOpens, Etale.HasTorsionBaseChange Λ (f ∣_ (U : Y.Opens))) :
    Etale.HasTorsionBaseChange Λ f := by
  intro Y' X' g f' g' sq K hK
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
  refine Etale.isIso_baseChange_app_of_etale_cover Λ (ι := Y.affineOpens)
    (fun U ↦ (g ⁻¹ᵁ (U : Y.Opens)).ι) (fun x ↦ ?_) (fun U ↦ g ∣_ (U : Y.Opens))
    (fun U ↦ (U : Y.Opens).ι) (fun U ↦ morphismRestrict_ι g U)
    (fun U ↦ (f ⁻¹ᵁ (U : Y.Opens)).ι) (fun U ↦ f ∣_ (U : Y.Opens))
    (fun U ↦ (isPullback_morphismRestrict f U).flip)
    (fun U ↦ pullback.fst (f ∣_ (U : Y.Opens)) (g ∣_ (U : Y.Opens)))
    (fun U ↦ pullback.snd (f ∣_ (U : Y.Opens)) (g ∣_ (U : Y.Opens)))
    (fun U ↦ IsPullback.of_hasPullback _ _) sq K fun U ↦ ?_
  · obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g.base x)) isOpen_univ
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩
  · rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    refine h U (IsPullback.of_hasPullback _ _) _ fun n ↦ ?_
    exact @Scheme.IsTorsionModuleSheaf.of_epi _ _ _ _ _
      ((((f ⁻¹ᵁ (U : Y.Opens)).ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso
        n).hom.app K) inferInstance (@isTorsionModuleSheaf_upperStar _ _ _ _ _ _ (hK n))

end AlgebraicGeometry
