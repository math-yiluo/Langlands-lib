/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionMono
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimensionDefs
import Mathlib.Condensed.Discrete.Characterization

/-!
# Cohomological dimension of étale sheaves of `Λ`-modules

The (torsion étale) cohomological dimension of a scheme and of a morphism, for sheaves of
`Λ`-modules (blueprint `definition-cohomological-dimension`), and its finiteness for schemes and
morphisms of finite type over a field (blueprint `theorem-results-from-etale-theory--6`, Stacks
0F10).

## Main definitions and statements

- `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`,
  `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimensionMorphism`
  (`definition-cohomological-dimension`).
- `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism` and
  `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimension_of_isSepClosed`
  (`theorem-results-from-etale-theory--6`).
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le`: the
  vanishing of `R^q f_*` above twice the dimension of the base changes of the source to the
  field extensions, over an arbitrary field, deduced from the separably closed case by a limit
  argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A quasi-compact scheme locally of finite type over a field has finite dimension. -/
lemma exists_topologicalKrullDim_le_of_locallyOfFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_isPullback aX
  exact ⟨d, hd K (𝟙 _) (𝟙 X) aX (IsPullback.id_horiz aX)⟩

/-- The `q`-th homology of `Rf_*` of a sheaf placed in degree `0` is the higher direct image
`R^q f_*`, computed on the bounded below derived category. -/
noncomputable def homologyRightDerivedLowerStarSingleIsoHigherDirectImage {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      Etale.higherDirectImage Λ f q F :=
  ((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F q ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm

/-- Blueprint `theorem-results-from-etale-theory--6`, part (1), over a separably closed field: a
morphism between `K`-schemes of finite type has finite cohomological dimension, with bound
`2 dim X`. This is `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`. -/
theorem hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType
    (hΛ : IsAddTorsion Λ) {K : Type u} [Field K] [IsSepClosed K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) :
    HasFiniteCohomologicalDimensionMorphism Λ f := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_locallyOfFiniteType aX
  have : LocallyOfFiniteType f := by
    subst hf
    exact locallyOfFiniteType_of_comp f aY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiCompact f := inferInstance
  refine ⟨2 * d, fun F q hq ↦ ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  exact (Etale.isZero_higherDirectImage_of_two_mul_lt hΛ f aX aY hf d hd F n hq).of_iso
    (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F n)

/-- The key step of blueprint `theorem-results-from-etale-theory--6`, part (1), over an arbitrary
field `K`. Let `f : X ⟶ Y` be a morphism between `K`-schemes of finite type such that
`dim (X ×_K L) ≤ n` for every field extension `L` of `K`. Then `R^q f_* F = 0` for every `q > 2n`.

Write `K^sep` for a separable closure of `K` and `X_L = X ×_K L`. By the limit theorem for higher
direct images (`AlgebraicGeometry.Etale.higherDirectImage_limit`), the stalks of the
`R^q (X_L → Y)_* F` over the finite subextensions `L` of `K^sep/K` have colimit the stalk of
`R^q (X_{K^sep} → Y)_* F`, which vanishes by the separably closed case
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_quasiCompact_of_two_mul_lt`). So every
element of a stalk of `R^q f_* F` dies in some `R^q (X_L → Y)_* F`. But the transition map
`R^q f_* F ⟶ R^q (X_L → Y)_* F` is a monomorphism
(`AlgebraicGeometry.Etale.mono_higherDirectImageOverMap`): after the étale surjective base change
`Y_L ⟶ Y`, the projection `X ×_Y Y_L ⟶ X` factors through `X_L`. -/
theorem isZero_higherDirectImage_of_forall_topologicalKrullDim_le (hΛ : IsAddTorsion Λ)
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (n : ℕ)
    (hn : ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of K)) {P : Scheme.{u}}
      (p₁ : P ⟶ X) (p₂ : P ⟶ Spec (.of L)), IsPullback p₁ p₂ aX s →
        topologicalKrullDim P ≤ (n : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * n : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q F) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  -- the cofiltered system of the `X_L`, for the finite subextensions `L` of `K^sep / K`
  let Ks := SeparableClosure K
  let I := IntermediateField.FiniteSubext K Ks
  let D : Iᵒᵖ ⥤ Scheme.{u} := (IntermediateField.subextDiagram K Ks).op ⋙ Scheme.Spec
  let c : Cone D := subextSpecCone K Ks
  have hc : IsLimit c := isLimitSubextSpecCone K Ks
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : Iᵒᵖ := Opposite.op ⟨⊥, inferInstance⟩
  let ρ : CommRingCat.of (⊥ : IntermediateField K Ks) ≅ CommRingCat.of K :=
    (IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso
  let p : X ⟶ D.obj i₀ := aX ≫ Spec.map ρ.hom
  let pY : Y ⟶ D.obj i₀ := aY ≫ Spec.map ρ.hom
  let D' := baseChangeDiagram D p
  let c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  let D'' : Over i₀ ⥤ Over X :=
    { obj j := Over.mk (pullback.fst p (D.map j.hom))
      map g := Over.homMk (D'.map g) (baseChangeDiagram_map_fst D p g)
      map_id j := by ext1; exact D'.map_id j
      map_comp g h := by ext1; exact D'.map_comp g h }
  let c'' : Cone D'' :=
    { pt := Over.mk (pullback.fst p (c.π.app i₀))
      π := { app j := Over.homMk (c'.π.app j) (baseChangeCone_π_app_fst D c p j)
             naturality j j' g := by ext1; exact c'.π.naturality g } }
  have hc'' : IsLimit ((Over.forget X).mapCone c'') := hc'
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := hD
  have (j j' : Over i₀) (g : j ⟶ j') : IsAffineHom (D''.map g).left :=
    inferInstanceAs (IsAffineHom (D'.map g))
  have (j : Over i₀) : QuasiCompact ((D''.obj j).hom ≫ f) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (D.map j.hom) ≫ f))
  have (j : Over i₀) : QuasiSeparated ((D''.obj j).hom ≫ f) := by
    have : IsAffine (D.obj j.left) := inferInstanceAs (IsAffine (Spec _))
    have : QuasiSeparatedSpace (D''.obj j).left :=
      (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (D.map j.hom))).mp inferInstance
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (D.map j.hom) ≫ f))
  have : IsAffine c.pt := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (c.π.app i₀) := inferInstanceAs (IsAffineHom (Spec.map _))
  have : QuasiCompact (c''.pt.hom ≫ f) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (c.π.app i₀) ≫ f))
  have : QuasiSeparated (c''.pt.hom ≫ f) := by
    have : QuasiSeparatedSpace c''.pt.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (c.π.app i₀))
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (c.π.app i₀) ≫ f))
  -- the higher direct image vanishes over the limit `X_{K^sep}`
  have hT : IsZero (Etale.higherDirectImage Λ (c''.pt.hom ≫ f) q
      ((c''.pt.hom)^*[ModuleCat.{u + 1} Λ].obj F)) := by
    let aT : pullback p (c.π.app i₀) ⟶ Spec (.of Ks) := pullback.snd p (c.π.app i₀)
    have hρ : (Scheme.Spec.mapIso ρ.symm.op).hom = Spec.map ρ.inv := rfl
    have hρρ : Spec.map ρ.hom ≫ Spec.map ρ.inv = 𝟙 _ := by
      rw [← Spec.map_comp, ρ.inv_hom_id, Spec.map_id]
    have hpb : IsPullback (pullback.fst p (c.π.app i₀)) aT aX
        (c.π.app i₀ ≫ Spec.map ρ.inv) :=
      (IsPullback.of_hasPullback p (c.π.app i₀)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (Scheme.Spec.mapIso ρ.symm.op) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by
          erw [hρ]
          exact (Category.assoc _ _ _).trans ((congrArg (aX ≫ ·) hρρ).trans
            (Category.comp_id _)))
        (by
          erw [hρ]
          exact (Category.id_comp _).symm)
    have : LocallyOfFiniteType aT :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    exact Etale.isZero_higherDirectImage_of_quasiCompact_of_two_mul_lt hΛ (k := Ks)
      (c''.pt.hom ≫ f) aT n (hn Ks _ _ _ hpb) _ q hq
  -- the transition maps from `X` to the stages `X_L` are monomorphisms
  let X₀ : Over X := Over.mk (𝟙 X)
  have hmono (j : Over i₀) (ψ : D''.obj j ⟶ X₀) :
      Mono (Etale.higherDirectImageOverMap Λ f F q ψ) := by
    let L : IntermediateField K Ks := j.left.unop.1
    have : FiniteDimensional K L := j.left.unop.2
    have hr : (IntermediateField.subextDiagram K Ks).map j.hom.unop =
        ρ.hom ≫ CommRingCat.ofHom (algebraMap K L) := by
      ext x
      exact IntermediateField.inclusion_bot_apply _ _ x
    have hDj : D.map j.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom := by
      rw [← Spec.map_comp, ← hr]
      rfl
    have : IsIso (Spec.map ρ.hom) := inferInstanceAs (IsIso (Scheme.Spec.mapIso ρ.op).hom)
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
      have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
      have : Algebra.FinitePresentation K L :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      exact HasRingHomProperty.Spec_iff.mpr
        (RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩)
    have hE : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom) :=
      inferInstance
    have hS : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom) :=
      inferInstance
    have : Etale (D.map j.hom) := by
      rw [hDj]
      exact hE
    have : Surjective (D.map j.hom) := by
      rw [hDj]
      exact hS
    have hψ : ψ.left = pullback.fst p (D.map j.hom) := by simpa [X₀, D''] using Over.w ψ
    have h₂ := pullback.condition (f := pY) (g := D.map j.hom)
    refine Etale.mono_higherDirectImageOverMap Λ f F q ψ (pullback.fst pY (D.map j.hom))
      (Surjective.surj (f := pullback.fst pY (D.map j.hom)))
      (IsPullback.of_hasPullback (X₀.hom ≫ f) (pullback.fst pY (D.map j.hom)))
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd pY (D.map j.hom)) ?_) ?_
    · have h₃ : (X₀.hom ≫ f) ≫ pY = p := by simp [X₀, p, pY, ← hf]
      rw [← h₃]
      exact (pullback.condition_assoc pY).trans ((congrArg (_ ≫ ·) h₂).trans
        (Category.assoc _ _ _).symm)
    · rw [hψ, pullback.lift_fst]
  -- hence the higher direct image vanishes, by the limit theorem
  let R₀ := Etale.higherDirectImage Λ (X₀.hom ≫ f) q ((X₀.hom)^*[ModuleCat.{u + 1} Λ].obj F)
  have hR₀ : IsZero R₀ := Etale.isZero_higherDirectImage_of_isLimit_of_mono Λ f F D'' c'' hc'' q
    (i₀ := Over.mk (𝟙 i₀)) (Over.homMk (D''.obj (Over.mk (𝟙 i₀))).hom (by simp [X₀])) hmono hT
  have e : R₀ = Etale.higherDirectImage Λ f q ((𝟙 X)^*[ModuleCat.{u + 1} Λ].obj F) := by
    simp [R₀, X₀]
  rw [e] at hR₀
  exact hR₀.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((f)_*[ModuleCat.{u + 1} Λ]).mapIso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) X).app F).symm)))

/-- Blueprint `theorem-results-from-etale-theory--6`: finite cohomological dimension of finite-type
morphisms, part (1).

Let `K` be a field and `f : X ⟶ Y` a morphism between `K`-schemes of finite type. For a torsion
coefficient ring `Λ`, the higher direct images `R^q f_*` of étale sheaves of `Λ`-modules vanish
in all large degrees `q`. -/
theorem hasFiniteCohomologicalDimensionMorphism (hΛ : IsAddTorsion Λ) {K : Type u} [Field K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX) :
    HasFiniteCohomologicalDimensionMorphism Λ f := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le_of_isPullback aX
  refine ⟨2 * n, fun F q hq ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = m := ⟨q.toNat, by omega⟩
  exact (isZero_higherDirectImage_of_forall_topologicalKrullDim_le Λ hΛ aX aY f _hf n hn F m
    hq).of_iso (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F m)

/-- Blueprint `theorem-results-from-etale-theory--6`: finite cohomological dimension of finite-type
morphisms, part (2).

Over a separably closed field `K`, a `K`-scheme `X` of finite type has finite étale
cohomological dimension: for a torsion coefficient ring `Λ`, `H^q(X, F) = 0` for every étale
sheaf `F` of `Λ`-modules and all large `q`. -/
theorem hasFiniteCohomologicalDimension_of_isSepClosed (hΛ : IsAddTorsion Λ) {K : Type u}
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] :
    HasFiniteCohomologicalDimension Λ X := by
  obtain ⟨d, hd⟩ := hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType
    Λ hΛ aX (𝟙 _) aX (Category.comp_id _)
  refine ⟨d, fun F q hq ↦ ?_⟩
  -- `H^q(X, F) = H^q(Spec K, Ra_* F) = Γ(Spec K, R^q a_* F)`, `Γ` being exact on `Spec K`
  exact ((Sheaf.Γ _ _).map_isZero (hd F q hq)).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app _).symm ≪≫
      ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).rightDerivedFunctorHomologyFunctorIso q).symm.app _)

end Etale

end AlgebraicGeometry
