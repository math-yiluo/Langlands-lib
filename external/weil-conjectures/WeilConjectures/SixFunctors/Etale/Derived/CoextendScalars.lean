/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Derived coextension of scalars commutes with the derived direct image

For a ring morphism `φ : Λ →+* Λ'`, coextension of scalars `M ↦ Hom_Λ(Λ', M)` sends étale sheaves
of `Λ`-modules to étale sheaves of `Λ'`-modules. It is right adjoint to the exact restriction of
scalars, so it preserves K-injective complexes, and it commutes with the direct image `g_*`
(both are computed objectwise). Hence its total right derived functor commutes with `Rg_*`:

`Rg_* ⋙ R coext ≅ R coext ⋙ Rg_*`.

For `Λ = 𝒪_E` and `Λ' = 𝒪_E/ϖ` the functor `R coext = RHom_{𝒪_E}(𝒪_E/ϖ, -)` is the reduction
modulo `ϖ` shifted by `-1`, read in `D(-, 𝒪_E/ϖ)`; this is a first step towards comparing
the integral and the finite stages of the projection formula
(`lemma-projection-formula-integral-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- Coextension of scalars along `φ : Λ →+* Λ'`, from étale sheaves of `Λ`-modules to étale
sheaves of `Λ'`-modules. -/
noncomputable abbrev coextendScalars (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ') :=
  sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)

instance (X : Scheme.{u}) : (coextendScalars φ X).Additive where
  map_add {_ _ _ _} := by
    ext : 3
    rfl

instance (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Coextension of scalars preserves K-injective complexes, being right adjoint to the exact
restriction of scalars. -/
instance (X : Scheme.{u}) : (coextendScalars φ X).PreservesKInjectiveComplexes :=
  (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).preservesKInjectiveComplexes

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Coextension of scalars commutes with the direct image, both being computed objectwise. -/
noncomputable def lowerStarCompCoextendScalarsIso :
    (g)_*[ModuleCat.{u + 1} Λ] ⋙ coextendScalars φ Y ≅
      coextendScalars φ Z ⋙ (g)_*[ModuleCat.{u + 1} Λ'] :=
  Iso.refl _

/-- **Derived coextension of scalars commutes with `Rg_*`.** -/
noncomputable def rightDerivedLowerStarCompCoextendScalarsIso :
    ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor ⋙
        (coextendScalars φ Y).rightDerivedFunctor ≅
      (coextendScalars φ Z).rightDerivedFunctor ⋙
        ((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompCoextendScalarsIso φ g) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm

section Detect

variable {X : Scheme.{u}} (ϖ : Λ)

/-- The short complex `Hom_Λ(Λ/ϖ, F) ⟶ F ⟶ F` of étale sheaves, the first map being the counit of
restriction and coextension of scalars along `Λ → Λ/ϖ` and the second multiplication by `ϖ`. -/
noncomputable def coextendQuotientSheafShortComplex
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ShortComplex.mk
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.app F)
    (ϖ • 𝟙 F) (by
      ext U : 3
      exact (ModuleCat.coextendQuotientShortComplex ϖ (F.obj.obj U)).zero)

lemma coextendQuotientSheafShortComplex_map_eval
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etaleᵒᵖ) :
    ((coextendQuotientSheafShortComplex ϖ F).map
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U)) =
      ModuleCat.coextendQuotientShortComplex ϖ (F.obj.obj U) :=
  rfl

variable {ϖ} in
/-- For an injective étale sheaf `F` and a nonzerodivisor `ϖ`, the sequence
`0 ⟶ Hom_Λ(Λ/ϖ, F) ⟶ F ⟶ F ⟶ 0` (multiplication by `ϖ`) is short exact. -/
lemma shortExact_coextendQuotientSheafShortComplex (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective F] :
    (coextendQuotientSheafShortComplex ϖ F).ShortExact := by
  let S := coextendQuotientSheafShortComplex ϖ F
  have hpre : (S.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun U ↦ ?_
    have h := ModuleCat.exact_coextendQuotientShortComplex ϖ (F.obj.obj U)
    rw [ShortComplex.exact_iff_isZero_homology] at h
    exact h.of_iso ((S.map (sheafToPresheaf _ _)).mapHomologyIso
      ((CategoryTheory.evaluation _ _).obj U)).symm
  have hmono : Mono (S.map (sheafToPresheaf _ _)).f := by
    have (U : X.Etaleᵒᵖ) : Mono ((S.map (sheafToPresheaf _ _)).f.app U) :=
      ModuleCat.mono_coextendQuotientShortComplex_f ϖ (F.obj.obj U)
    exact NatTrans.mono_of_mono_app _
  have : Mono S.f := (sheafToPresheaf _ _).mono_of_mono_map hmono
  have : Epi S.g := Sheaf.epi_smul_id_of_injective.{u + 1} F hϖ
  refine ⟨?_⟩
  have e : S.map (sheafToPresheaf _ _ ⋙ presheafToSheaf _ _) ≅ S :=
    S.mapNatIso (asIso (sheafificationAdjunction _ _).counit)
  exact (ShortComplex.exact_iff_of_iso e).1 (hpre.map (presheafToSheaf _ _))

variable {ϖ} in
/-- The short exact sequence of complexes `0 ⟶ Hom_Λ(Λ/ϖ, I) ⟶ I ⟶ I ⟶ 0` for a complex `I` of
injective étale sheaves. -/
noncomputable def coextendQuotientComplexShortComplex
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :=
  ShortComplex.mk
    (X₁ := (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {ϖ}))
      |>.mapHomologicalComplex _).obj
        (((coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X).mapHomologicalComplex _).obj I))
    { f n := (coextendQuotientSheafShortComplex ϖ (I.X n)).f
      comm' i j _ := ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.naturality (I.d i j)) }
    (ϖ • 𝟙 I) (by
      ext n : 1
      exact (coextendQuotientSheafShortComplex ϖ (I.X n)).zero)

lemma shortExact_coextendQuotientComplexShortComplex (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [∀ n, Injective (I.X n)] :
    (coextendQuotientComplexShortComplex (ϖ := ϖ) I).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    shortExact_coextendQuotientSheafShortComplex hϖ (I.X n)

/-- **The derived coextension detects invertibility of `ϖ`.** For a nonzerodivisor `ϖ` of `Λ`
and `C ∈ D(X_ét, Λ)`, if `RHom_Λ(Λ/ϖ, C) = 0` in `D(X_ét, Λ/ϖ)` then `ϖ` acts invertibly on
`C`. Computing with a K-injective resolution `I` of `C` with injective components, the short exact
sequence `0 ⟶ Hom_Λ(Λ/ϖ, I) ⟶ I ⟶ I ⟶ 0` gives a distinguished triangle whose first vertex is
the restriction of scalars of `RHom_Λ(Λ/ϖ, C)`. -/
theorem isIso_smul_id_of_isZero_rightDerivedFunctor_coextendScalars
    (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (C : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hC : IsZero ((coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X).rightDerivedFunctor.obj
      C)) :
    IsIso (ϖ • 𝟙 C) := by
  let A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let coext := coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X
  let res := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {ϖ}))
  -- a K-injective resolution with injective components
  let K := _root_.DerivedCategory.Q.objPreimage C
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} A).obj K
  have hi := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A K).2
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} A).app K) := hi
  let eC : C ≅ _root_.DerivedCategory.Q.obj I :=
    (_root_.DerivedCategory.Q.objObjPreimageIso C).symm ≪≫
      asIso (_root_.DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{u + 1} A).app K))
  -- the first vertex of the triangle vanishes
  have h₁ : IsZero (_root_.DerivedCategory.Q.obj
      (coextendQuotientComplexShortComplex (ϖ := ϖ) I).X₁) := by
    have hu : IsIso (coext.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) :=
      inferInstance
    have h₀ : IsZero (coext.rightDerivedFunctor.obj
        (_root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) :=
      hC.of_iso (coext.rightDerivedFunctor.mapIso
        ((_root_.DerivedCategory.quotientCompQhIso A).app I ≪≫ eC.symm))
    have h₂ : IsZero (_root_.DerivedCategory.Q.obj ((coext.mapHomologicalComplex _).obj I)) :=
      (h₀.of_iso (asIso (coext.rightDerivedFunctorUnit.app _))).of_iso
        ((_root_.DerivedCategory.quotientCompQhIso _).app _).symm
    exact (res.mapDerivedCategory.map_isZero h₂).of_iso
      ((res.mapDerivedCategoryFactors).app _).symm
  have hT := _root_.DerivedCategory.triangleOfSES_distinguished
    (shortExact_coextendQuotientComplexShortComplex ϖ hϖ I)
  have h₂ := (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hT).1 h₁
  have e : (_root_.DerivedCategory.triangleOfSES
      (shortExact_coextendQuotientComplexShortComplex ϖ hϖ I)).mor₂ =
      ϖ • 𝟙 (_root_.DerivedCategory.Q.obj I) := by
    change _root_.DerivedCategory.Q.map (ϖ • 𝟙 I) = _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [e] at h₂
  have : ϖ • 𝟙 C = eC.hom ≫ (ϖ • 𝟙 (_root_.DerivedCategory.Q.obj I)) ≫ eC.inv := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id]
  rw [this]
  infer_instance

end Detect

section Pullback

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The base change comparison `coext ∘ g^* ⟶ g^* ∘ coext` between coextension of scalars and
étale pullback: the mate, along `g^* ⊣ g_*`, of the identification `g_* ∘ coext = coext ∘ g_*`
(`AlgebraicGeometry.Etale.lowerStarCompCoextendScalarsIso`). -/
noncomputable def coextendScalarsUpperStarMap :
    coextendScalars φ Y ⋙ (g)^*[ModuleCat.{u + 1} Λ'] ⟶
      (g)^*[ModuleCat.{u + 1} Λ] ⋙ coextendScalars φ Z :=
  ((mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)).symm
      (TwoSquare.mk _ _ _ _ (lowerStarCompCoextendScalarsIso φ g).hom))

end Pullback

end Etale

end AlgebraicGeometry
