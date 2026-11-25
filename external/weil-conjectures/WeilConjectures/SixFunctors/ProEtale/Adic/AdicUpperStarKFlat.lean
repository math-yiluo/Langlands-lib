/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleInternalPullbackKFlat
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
public import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Algebra.Homology.CountableTensorStructures
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import all WeilConjectures.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorRightIsoNaturality

/-!
# Pullback of `ℓ`-adic sheaves preserves ordinary K-flatness

For a morphism of schemes `f : X ⟶ Y`, the pullback `f^*ᵃ[l]` of sheaves of `ℚ̄_ℓ`-modules
sends complexes that are K-flat for the ordinary (coequalizer) relative tensor product to such
complexes (`AlgebraicGeometry.ProEtale.nativeOrdinaryKFlat_adicUpperStar`).

The proof transports the question along the monoidal equivalence between `ℓ`-adic sheaves and
module objects over a ring object in abelian pro-étale sheaves, where pullback preserves
K-flatness (`preservesKFlatComplexes_mapMod_proEtale`).
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {M : Type*} {A : Type*} [Category M] [Category A]
  [Abelian M] [Abelian A] [MonoidalCategory M] [MonoidalCategory A]
  [MonoidalPreadditive M] [MonoidalPreadditive A]
  [SymmetricCategory M] [SymmetricCategory A]
  [HasCountableCoproducts M] [HasCountableCoproducts A]
  [TensorPreservesCountableCoproducts M] [TensorPreservesCountableCoproducts A]

/-- An additive monoidal equivalence preserves and reflects K-flatness of cochain complexes. -/
theorem kFlat_mapHomologicalComplex_obj_iff (F : M ⥤ A) [F.Additive] [F.IsEquivalence]
    [F.Monoidal] (P : CochainComplex M ℤ) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat ((F.mapHomologicalComplex (.up ℤ)).obj P) ↔
      (HomologicalComplex.quasiIso M (.up ℤ)).kFlat P := by
  have : F.asEquivalence.functor.Additive := inferInstanceAs F.Additive
  have : F.asEquivalence.functor.Monoidal := inferInstanceAs F.Monoidal
  rw [← Equivalence.acyclic_tensor_iff_kFlat, ← Equivalence.acyclic_tensor_iff_kFlat]
  exact (Equivalence.acyclic_tensor_map_iff F.asEquivalence P).symm

/-- A complex `P` is K-flat iff `N ⊗ P` is acyclic for every acyclic complex `N`. -/
theorem kFlat_iff_acyclic_tensorRight (P : CochainComplex M ℤ) :
    (HomologicalComplex.quasiIso M (.up ℤ)).kFlat P ↔
      ∀ N : CochainComplex M ℤ, N.Acyclic → (N ⊗ P).Acyclic := by
  rw [← Equivalence.acyclic_tensor_iff_kFlat]
  exact Equivalence.acyclic_tensor_swap P

end CategoryTheory.Functor


namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

instance (Y : Scheme.{u}) : TensorPreservesCountableCoproducts (AdicSheaf l Y) where
  left _ _ _ := inferInstance
  right _ _ _ := inferInstance

instance (Y : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R]
    [IsCommMonObj R] :
    TensorPreservesCountableCoproducts (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) where
  left _ _ _ := inferInstance
  right _ _ _ := inferInstance

/-- The ordinary coequalizer relative tensor bifunctor is the flipped monoidal tensor. -/
noncomputable def ordinaryTensorBifunctorIso (Y : Scheme.{u}) :
    ProEtaleWeilSheaf.ordinaryTensorBifunctor l Y ≅ (curriedTensor (AdicSheaf l Y)).flip :=
  NatIso.ofComponents (fun P ↦ Mod.relativeTensorRightIso P)
    (fun g ↦ Mod.tensorLeftMap_relativeTensorRightIso_hom g)

/-- The ordinary total relative tensor complex is the monoidal tensor in the other order. -/
noncomputable def ordinaryTensorTotalIso (Y : Scheme.{u})
    (P Q : CochainComplex (AdicSheaf l Y) ℤ) :
    ProEtaleWeilSheaf.ordinaryTensorTotal l Y P Q ≅ Q ⊗ P :=
  HomologicalComplex.mapBifunctorIsoOfIso (ordinaryTensorBifunctorIso l Y) P Q (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso Q P (curriedTensor (AdicSheaf l Y)) (.up ℤ)

/-- Ordinary K-flatness of a complex of `ℓ`-adic sheaves is K-flatness for the monoidal
structure. -/
theorem nativeOrdinaryKFlat_iff_kFlat (Y : Scheme.{u}) (P : CochainComplex (AdicSheaf l Y) ℤ) :
    ProEtaleWeilSheaf.NativeOrdinaryKFlat l Y P ↔
      (HomologicalComplex.quasiIso (AdicSheaf l Y) (.up ℤ)).kFlat P := by
  rw [Functor.kFlat_iff_acyclic_tensorRight]
  refine forall₂_congr fun N _ ↦ ?_
  exact ⟨fun h n ↦ (h n).of_iso (ordinaryTensorTotalIso l Y P N),
    fun h n ↦ (h n).of_iso (ordinaryTensorTotalIso l Y P N).symm⟩


section Scalars

variable {T : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} [MonObj R]
  [IsCommMonObj R] [MonObj S] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

/-- Extension of scalars along an isomorphism of ring objects preserves and reflects
K-flatness. -/
theorem kFlat_extendScalars_iff
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) ℤ) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ↔
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K := by
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : (Mod.extendScalars φ).IsEquivalence :=
    (Mod.extendRestrictAdjunction φ).isEquivalence_left_of_isEquivalence_right
  have : (Mod.extendScalars φ).Additive :=
    (Mod.extendRestrictAdjunction φ).left_adjoint_additive
  obtain ⟨m, -⟩ := Mod.exists_extendScalarsMonoidal φ
  exact Functor.kFlat_mapHomologicalComplex_obj_iff (Mod.extendScalars φ) K

/-- Restriction of scalars along an isomorphism of ring objects preserves and reflects
K-flatness. -/
theorem kFlat_comap_iff
    (K : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) S) ℤ) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj K) ↔
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K := by
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : (Mod.extendScalars φ).Additive :=
    (Mod.extendRestrictAdjunction φ).left_adjoint_additive
  let e : ((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
      (((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj K) ≅ K :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app K ≪≫
      (NatIso.mapHomologicalComplex (asIso (Mod.extendRestrictAdjunction φ).counit)
        (.up ℤ)).app K ≪≫ (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app K
  rw [← kFlat_extendScalars_iff φ]
  exact ⟨fun h ↦ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso e h,
    fun h ↦ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso e.symm h⟩

end Scalars


/-- Pullback of `ℓ`-adic sheaves along any morphism of schemes preserves ordinary K-flatness:
if `P ⊗ N` is acyclic for every acyclic `N` on `Y`, then `f^* P ⊗ N` is acyclic for every
acyclic `N` on `X`.

Proof: forgetting ambient scalars and restricting along the coefficient realization is a
monoidal equivalence with module objects over the condensed coefficient ring, compatible with
pullback (`nativeScalarForgetting_pullbackIso`); there, pullback is `mapMod(f^*)`, which
preserves K-flat complexes (`preservesKFlatComplexes_mapMod_proEtale`), followed by extension
of scalars along an isomorphism of ring objects. -/
theorem nativeOrdinaryKFlat_adicUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (AdicSheaf l Y) ℤ)
    (hP : ProEtaleWeilSheaf.NativeOrdinaryKFlat l Y P) :
    ProEtaleWeilSheaf.NativeOrdinaryKFlat l X
      (((adicUpperStar l f).mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [nativeOrdinaryKFlat_iff_kFlat] at hP ⊢
  obtain ⟨mY⟩ := nativeScalarForgetting_monoidal l Y
  obtain ⟨mX⟩ := nativeScalarForgetting_monoidal l X
  have := nativeScalarForgetting_isEquivalence l Y
  have := nativeScalarForgetting_isEquivalence l X
  have : (AdicSheaf.forgetAb l Y).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (AdicSheaf.forgetAb l X).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨e⟩ := nativeScalarForgetting_pullbackIso l f
  rw [← Functor.kFlat_mapHomologicalComplex_obj_iff (AdicSheaf.forgetAb l X),
    ← kFlat_comap_iff (nativeModuleCoefficientIso l X).hom]
  rw [← Functor.kFlat_mapHomologicalComplex_obj_iff (AdicSheaf.forgetAb l Y),
    ← kFlat_comap_iff (nativeModuleCoefficientIso l Y).hom] at hP
  have h := (CondensedRing.preservesKFlatComplexes_mapMod_proEtale f _).kFlat_map _ hP
  rw [← kFlat_extendScalars_iff (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)] at h
  exact (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_of_iso
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P).symm h



end AlgebraicGeometry.ProEtale
