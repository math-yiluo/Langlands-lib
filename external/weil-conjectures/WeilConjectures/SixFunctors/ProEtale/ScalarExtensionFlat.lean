/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.Sites.FlatExtendScalars
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Descent
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Extension of scalars of pro-étale sheaves preserves flatness

For any morphism of commutative rings `R ⟶ S`, extension of scalars
`S ⊗_R - : Sh(X_proét, R) ⥤ Sh(X_proét, S)` sends flat sheaves to flat sheaves
(`AlgebraicGeometry.ProEtale.preservesFlat_sheafExtendScalars`), since with scalars restricted to
`R`, tensoring with `S ⊗_R F` is tensoring with `F` (`CategoryTheory.Sheaf.flat_extendScalars_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- An `R`-algebra `S`, as an `R`-module, is `S` with the `R`-module structure obtained by
restricting scalars along `algebraMap R S`. -/
noncomputable def _root_.ModuleCat.restrictScalarsAlgebraMapSelfLinearEquiv :
    S ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' r s := Algebra.smul_def r s
  left_inv _ := rfl
  right_inv _ := rfl

-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small pro-étale sites
-- take long to synthesize
omit [Algebra R S] in
/-- Extension of scalars along any ring morphism preserves flat pro-étale sheaves
(`CategoryTheory.Sheaf.flat_extendScalars_obj`). -/
instance preservesFlat_sheafExtendScalars (φ : R →+* S) :
    (sheafExtendScalars φ X).PreservesFlat where
  flat_obj hF := Sheaf.flat_extendScalars_obj _ φ hF

variable {X}

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- For a basis `b` of the finite free `R`-algebra `S` and a pro-étale sheaf `F` of `R`-modules,
the maps `F ⟶ res (S ⊗_R F)` given by the unit of extension of scalars followed by multiplication
by the `b i` exhibit `res (S ⊗_R F)` as a sum of copies of `F`. Indeed `S ⊗_R F` is computed
sectionwise, `S` being finite free over `R`, and on sections this is
`ModuleCat.ExtendScalars.isIso_biproductDesc_unit_comp_map_smul`. -/
theorem isIso_biproductDesc_sheafExtendScalarsAdjunction_unit [Module.Finite R S]
    [Module.Free R S] {ι : Type} [Finite ι] (b : Module.Basis ι R S)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    IsIso (biproduct.desc fun i ↦ (sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app F ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map ((b i : S) • 𝟙 _)) := by
  let φ := algebraMap R S
  let b' := b.map ModuleCat.restrictScalarsAlgebraMapSelfLinearEquiv
  have := Fintype.ofFinite ι
  -- `S ⊗_R F` is already a sheaf on sections, `S` being finite free
  have : PreservesLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) :=
    ModuleCat.preservesLimits_extendScalars_of_finite_projective φ
      (by rw [toAlgebra_algebraMap]; infer_instance)
      (by rw [toAlgebra_algebraMap]; infer_instance)
  have hs : Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (F.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) :=
    ((sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj F).property
  have : IsIso (toSheafify (Scheme.ProEt.topology X)
      (F.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)) := isIso_toSheafify _ hs
  -- the statement on sections
  have hU (U : (X.ProEt)ᵒᵖ) : IsIso (biproduct.desc fun i ↦
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app (F.obj.obj U) ≫
        (ModuleCat.restrictScalars.{u + 1} φ).map
          (ModuleCat.restrictScalarsSelfVal φ (b' i) •
            𝟙 ((ModuleCat.extendScalars φ).obj (F.obj.obj U)))) :=
    ModuleCat.ExtendScalars.isIso_biproductDesc_unit_comp_map_smul φ b' (F.obj.obj U)
  -- the statement on underlying presheaves
  let t := Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
    (F.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
      (ModuleCat.restrictScalars.{u + 1} φ)
  let ψ (i : ι) := ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).whiskerRight
      (X.ProEt)ᵒᵖ).unit.app F.obj ≫
    Functor.whiskerRight ((b i : S) • 𝟙 (F.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ))
      (ModuleCat.restrictScalars.{u + 1} φ)
  have hψ : IsIso (biproduct.desc ψ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    have : IsIso (biproduct.desc fun i ↦ ((CategoryTheory.evaluation _ _).obj U).map (ψ i)) :=
      hU U
    exact (Functor.isIso_map_biproductDesc ((CategoryTheory.evaluation _ _).obj U) ψ).2 this
  have he : (biproduct.desc fun i ↦ (sheafToPresheaf _ _).map
      ((sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app F ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map ((b i : S) • 𝟙 _))) =
      biproduct.desc ψ ≫ t := by
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, Functor.map_comp]
    change ((Sheaf.adjunction _
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).unit.app F).hom ≫
        Functor.whiskerRight ((b i : S) • 𝟙 ((sheafExtendScalars φ X).obj F)).hom
          (ModuleCat.restrictScalars.{u + 1} φ) = _
    rw [Sheaf.adjunction_unit_app_hom]
    simp only [ψ, t, Category.assoc, ← Functor.whiskerRight_comp]
    congr 2
    change toSheafify _ _ ≫ ((b i : S) • 𝟙 _) = ((b i : S) • 𝟙 _) ≫ toSheafify _ _
    rw [Linear.comp_smul, Linear.smul_comp]
    erw [Category.comp_id]
  have : IsIso (biproduct.desc fun i ↦ (sheafToPresheaf _ _).map
      ((sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app F ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map ((b i : S) • 𝟙 _))) := by
    have : IsIso (biproduct.desc ψ ≫ t) := inferInstance
    rwa [← he] at this
  have := Functor.isIso_map_biproductDesc (sheafToPresheaf _ _) (g := fun i ↦
      (sheafExtendScalarsAdjunction (algebraMap R S) X).unit.app F ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map ((b i : S) • 𝟙 _))
    |>.2 inferInstance
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

end AlgebraicGeometry.ProEtale
