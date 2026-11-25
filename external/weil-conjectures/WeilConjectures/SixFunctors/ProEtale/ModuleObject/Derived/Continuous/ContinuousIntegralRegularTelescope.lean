/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.ConstructibleSheaf.FreeLifting

/-! # The regular coefficient localization telescope -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private noncomputable abbrev coefficientPresheaf (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheaf R ⋙ forget₂ RingCat Ab

private noncomputable abbrev integralPresheafMap :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E :=
  Functor.whiskerRight
    (Profinite.continuousMapRingPresheafMap (continuousIntegers ℓ E).subtype
      continuous_subtype_val) (forget₂ RingCat Ab)

private noncomputable def localizationLegHom (n : ℕ) :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E where
  app S := AddCommGrpCat.ofHom
    { toFun x := ULift.up
        (⟨fun s ↦ (x.down s : E) / (ℓ : E) ^ n,
          (continuous_subtype_val.comp x.down.continuous).div_const _⟩ : C(S.unop, E))
      map_zero' := by apply ULift.ext; ext; simp
      map_add' x y := by
        apply ULift.ext
        ext s
        change ((x.down s : E) + (y.down s : E)) / (ℓ : E) ^ n =
          (x.down s : E) / (ℓ : E) ^ n + (y.down s : E) / (ℓ : E) ^ n
        exact add_div _ _ _ }
  naturality _ _ _ := rfl

private noncomputable def localizationLeg (n : ℕ) :
    Mod.regular (coefficientPresheaf.{u} (continuousIntegers ℓ E)) ⟶
      (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E)) :=
  Mod.homMk (localizationLegHom ℓ E n) (by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    ext x
    change ((a.down x : E) * (b.down x : E)) / (ℓ : E) ^ n =
      (a.down x : E) * ((b.down x : E) / (ℓ : E) ^ n)
    exact mul_div_assoc _ _ _)

private noncomputable abbrev localizationSequence :
    ℕ ⥤ Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
      (coefficientPresheaf (continuousIntegers ℓ E)) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
    (coefficientPresheaf (continuousIntegers ℓ E))))

private noncomputable def localizationCocone : Cocone (localizationSequence.{u} ℓ E) where
  pt := (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E))
  «ι» := NatTrans.ofSequence (localizationLeg ℓ E) (by
    intro n
    simp only [localizationSequence, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext s
    change (continuousIntegers ℓ E).subtype (ℓ • x.down s) / (ℓ : E) ^ (n + 1) =
      (x.down s : E) / (ℓ : E) ^ n
    rw [map_nsmul, nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ℓ E]
    rfl)

private noncomputable def localizationCoconeIsColimit :
    IsColimit (localizationCocone.{u} ℓ E) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape ℕ
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
        (coefficientPresheaf (continuousIntegers ℓ E))) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (coefficientPresheaf (continuousIntegers ℓ E)))
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := continuousIntegralFunctions_isLocalization ℓ E S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : continuousIntegers ℓ E)) x.down
    refine ⟨n, ULift.up a, ?_⟩
    apply ULift.ext
    ext s
    change x.down s = (a s : E) / (ℓ : E) ^ n
    have ha' := congrArg (fun f : C(S.unop, E) ↦ f s) ha
    change x.down s * (ℓ : E) ^ n = (a s : E) at ha'
    exact (eq_div_iff (pow_ne_zero n (ell_ne_zero ℓ E))).2 ha'
  · intro n x y h
    have hxy : x = y := by
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      have h' := congrArg (fun f : ULift.{u + 1} C(S.unop, E) ↦ f.down s) h
      change (x.down s : E) / (ℓ : E) ^ n = (y.down s : E) / (ℓ : E) ^ n at h'
      exact (div_left_inj' (pow_ne_zero n (ell_ne_zero ℓ E))).mp h'
    subst y
    exact ⟨n, 𝟙 n, rfl⟩

private noncomputable def mappedRegularIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] (R : C) [MonObj R] :
    (L.mapMod R).obj (Mod.regular R) ≅ Mod.regular (L.obj R) :=
  Mod.isoMk (Iso.refl _) (by simp [Mod.act])

private noncomputable def restrictedRegularIso
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B B' : C} [MonObj A] [MonObj B] [MonObj B']
    (φ : A ⟶ B) (φ' : A ⟶ B') [IsMonHom φ] [IsMonHom φ']
    (e : B ≅ B') [IsMonHom e.hom] (w : φ ≫ e.hom = φ') :
    (Mod.comap φ).obj (Mod.regular B) ≅ (Mod.comap φ').obj (Mod.regular B') :=
  Mod.isoMk e (by
    change (φ ▷ B ≫ μ[B]) ≫ e.hom = A ◁ e.hom ≫ φ' ▷ B' ≫ μ[B']
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, w, whisker_exchange_assoc])

private noncomputable def pointCoefficientIso (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] :
    (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (coefficientPresheaf R) ≅ Profinite.continuousMapRingObj R :=
  Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf R)

private noncomputable abbrev schemeCoefficientFunctor (X : Scheme.{u}) :=
  presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

private noncomputable def schemeCoefficientIso (X : Scheme.{u})
    (R : Type) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    (schemeCoefficientFunctor X).obj (coefficientPresheaf R) ≅
      condensedRingObj (Profinite.continuousMapRingObj R) X :=
  (upperStarFromPoint X).mapIso (pointCoefficientIso R)

private theorem schemeCoefficientIso_naturality (X : Scheme.{u}) :
    (schemeCoefficientFunctor X).map (integralPresheafMap ℓ E) ≫
        (schemeCoefficientIso X E).hom =
      (schemeCoefficientIso X (continuousIntegers ℓ E)).hom ≫
        coefficientMap (integralScalarMap ℓ E) X := by
  change (upperStarFromPoint X).map
      ((presheafToSheaf _ Ab).map (integralPresheafMap ℓ E)) ≫
        (upperStarFromPoint X).map (pointCoefficientIso E).hom =
    (upperStarFromPoint X).map (pointCoefficientIso (continuousIntegers ℓ E)).hom ≫
      (upperStarFromPoint X).map (integralScalarMap ℓ E)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [integralScalarMap, Sheaf.sheafCompose_map_eq]
  simp only [pointCoefficientIso, Iso.hom_inv_id_assoc]
  rfl

omit [Fact ℓ.Prime] in
/-- Transport a scalar telescope colimit and its specified zeroth leg through an
additive functor and coefficient isomorphisms.
Source: universal properties of colimits and natural isomorphisms.
(blueprint: lem-weil-pbc-integral-regular-telescope).
Proof. Reindex the mapped cocone by the natural isomorphism with constant component
`er.hom`; its inverse changes the zeroth leg by `er.inv`. The given leg equation
then cancels `er.inv` with `er.hom`. -/
theorem transportRegularTelescope
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {M : A}
    (c : Cocone (integralLocalizationSequence ℓ M))
    (hc : IsColimit (F.mapCocone c)) {N P : B}
    (er : F.obj M ≅ N) (es : F.obj c.pt ≅ P)
    (V : B ⥤ C) (φ : V.obj N ⟶ V.obj P)
    (hz : V.map (F.map (c.ι.app 0) ≫ es.hom) = V.map er.hom ≫ φ) :
    ∃ c' : Cocone (integralLocalizationSequence ℓ N),
      Nonempty (IsColimit c') ∧ ∃ e : c'.pt ≅ P,
        V.map (c'.ι.app 0 ≫ e.hom) = φ := by
  let α : integralLocalizationSequence ℓ M ⋙ F ⟶ integralLocalizationSequence ℓ N :=
    NatTrans.ofSequence (fun _ ↦ er.hom) (by
      intro n
      simp only [integralLocalizationSequence, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ]
      change F.map (ℓ • 𝟙 M) ≫ er.hom = er.hom ≫ (ℓ • 𝟙 N)
      rw [F.map_nsmul, F.map_id]
      simp)
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso er.hom
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c' := (Cocone.precompose (asIso α).inv).obj (F.mapCocone c)
  refine ⟨c', ⟨(IsColimit.precomposeHomEquiv (asIso α).symm _).symm hc⟩, es, ?_⟩
  have hi : (asIso α).inv.app 0 = er.inv := by
    apply (cancel_mono er.hom).1
    change (asIso α).inv.app 0 ≫ (asIso α).hom.app 0 = er.inv ≫ er.hom
    simp; rfl
  change V.map (((asIso α).inv.app 0 ≫ F.map (c.ι.app 0)) ≫ es.hom) = φ
  rw [hi, Category.assoc, V.map_comp, hz, ← Category.assoc,
    ← V.map_comp, er.inv_hom_id]
  change V.map (𝟙 N) ≫ φ = φ
  rw [V.map_id, Category.id_comp]

/-- The regular restricted E-module is the scalar telescope of the regular integral
module; the zeroth leg is the coefficient inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2, compact-test localization.
(blueprint: lem-weil-pbc-integral-regular-telescope).
Proof. On every compact profinite test, divide by ℓⁿ. Compactness supplies one
common denominator, and injectivity gives the colimit equivalence relation.
Monoidal sheafification and inverse image from the point preserve the resulting
module colimit. Their coefficient isomorphisms identify the zeroth leg with the
original coefficient inclusion. -/
theorem integralRegularTelescope (X : Scheme.{u}) :
    ∃ c : Cocone (integralLocalizationSequence ℓ (Mod.regular
        (condensedRingObj (integralCoeff ℓ E) X))),
      Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (integralScalarMap ℓ E) X)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)),
        (c.ι.app 0 ≫ e.hom).hom = coefficientMap (integralScalarMap ℓ E) X := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let S := coefficientPresheaf.{u} E
  let A := condensedRingObj (integralCoeff ℓ E) X
  let B := condensedRingObj (Profinite.continuousMapRingObj E) X
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  let b := schemeCoefficientIso X E
  let φ := integralPresheafMap.{u} ℓ E
  let ψ := coefficientMap (integralScalarMap ℓ E) X
  have : IsMonHom a.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj R) _ a.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso (continuousIntegers ℓ E)).hom
  have : IsMonHom a.inv := by infer_instance
  have : IsMonHom b.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj S) _ b.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso E).hom
  let F := L.mapMod R ⋙ Mod.comap a.inv
  have : L.Additive := by
    exact rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : (L.mapMod R).Additive := ⟨fun {M N f g} ↦
    Mod.hom_ext _ _ (L.map_add (f := f.hom) (g := g.hom))⟩
  have : PreservesColimitsOfShape ℕ (L.mapMod R) := by
    have : PreservesColimitsOfShape ℕ
        (L.mapMod R ⋙ Mod.forget (L.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape ℕ (Mod.forget R ⋙ L))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (L.obj R))
  let er : F.obj (Mod.regular R) ≅ Mod.regular A :=
    (Mod.comap a.inv).mapIso (mappedRegularIso L R) ≪≫
      restrictedRegularIso a.inv (𝟙 A) a (by exact a.inv_hom_id) ≪≫ (Mod.comapId A).app _
  let es : F.obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap ψ).obj (Mod.regular B) :=
    (Mod.comap a.inv).mapIso
      ((L.mapModComapIso φ).app (Mod.regular S) ≪≫
        (Mod.comap (L.map φ)).mapIso (mappedRegularIso L S)) ≪≫
      (Mod.comapComp a.inv (L.map φ)).symm.app (Mod.regular (L.obj S)) ≪≫
      restrictedRegularIso (a.inv ≫ L.map φ) ψ b (by
        rw [Category.assoc, schemeCoefficientIso_naturality, Iso.inv_hom_id_assoc])
  apply transportRegularTelescope ℓ F (localizationCocone ℓ E)
    (isColimitOfPreserves F (localizationCoconeIsColimit.{u} ℓ E))
    er es (Mod.forget A) ψ
  change L.map (localizationLegHom ℓ E 0) ≫ b.hom = a.hom ≫ ψ
  have hz : localizationLegHom ℓ E 0 = φ := by
    ext T x
    apply ULift.ext
    ext t
    simp only [localizationLegHom, pow_zero, div_one]
    rfl
  rw [hz]
  exact schemeCoefficientIso_naturality ℓ E X

end AlgebraicGeometry.ProEtale.CondensedRing
