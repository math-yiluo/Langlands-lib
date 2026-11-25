/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# Forgetting the Weil structure of native total tensor complexes

The native tensor product of pro-étale Weil sheaves `B ⊗ A` has underlying sheaf the relative
tensor product `(Mod.tensorLeft B).obj A` of the underlying `ℓ`-adic sheaves, which is the monoidal
tensor product `A ⊗ B` of `ℓ`-adic sheaves (`CategoryTheory.Mod.relativeTensorRightIso`). This file
records the resulting comparison of the native total tensor complex with the tensor product of
complexes of `ℓ`-adic sheaves after forgetting the Weil structures.

## Main definitions

* `AlgebraicGeometry.ProEtaleWeilSheaf.nativeForgetTensorIso`: forgetting the Weil structure of
  the native tensor product of sheaves gives the tensor product of `ℓ`-adic sheaves.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
/-- The identification `(Mod.tensorLeft N).obj M ≅ M ⊗ N` is natural in `N`. -/
lemma tensorLeftMap_app_comp_relativeTensorRightIso_hom_app {N N' : Mod C R} (g : N ⟶ N')
    (M : Mod C R) :
    (tensorLeftMap g).app M ≫ (relativeTensorRightIso N').hom.app M =
      (relativeTensorRightIso N).hom.app M ≫ M ◁ g := by
  apply tensorLeft_hom_ext N M
  have h₁ : tensorLeftπ N M ≫ (relativeTensorRightIso N).hom.app M = relativeTensorπ M N := by
    simp [relativeTensorRightIso, tensorLeftπ, relativeTensorCofork]
  have h₂ : tensorLeftπ N' M ≫ (relativeTensorRightIso N').hom.app M = relativeTensorπ M N' := by
    simp [relativeTensorRightIso, tensorLeftπ, relativeTensorCofork]
  rw [reassoc_of% h₁, ← Category.assoc, tensorLeftπ_tensorLeftMap_app, Category.assoc, h₂]
  apply Mod.hom_ext
  exact (tensorObjπ_whiskerLeft g).symm

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The underlying map of the native tensor product with a morphism, in the fixed variable, is
the tensor product of the underlying morphism of `ℓ`-adic sheaves. -/
lemma nativeTensorMap_app_hom_f {A B : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B)
    (Q : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorMap k₀ l X f).app Q).hom.f = (Mod.tensorLeftMap f.hom.f).app Q.carrier := by
  change ((conjugateEquiv (Mod.ihomAdjunction B.carrier)
    (Mod.ihomAdjunction A.carrier)).symm (Mod.ihomMap f.hom.f)).app Q.carrier = _
  rw [Mod.ihomMap, Equiv.symm_apply_apply]

/-- Naturality of the forgetful comparison of native tensor products. -/
lemma nativeForgetTensor_naturality {P T P' T' : ProEtaleWeilSheaf k₀ l X} (f : P ⟶ P')
    (g : T ⟶ T') :
    ((tensorFunctor k₀ l X T).map f ≫ (nativeTensorMap k₀ l X g).app P').hom.f ≫
        (Mod.relativeTensorRightIso T'.carrier).hom.app P'.carrier =
      (Mod.relativeTensorRightIso T.carrier).hom.app P.carrier ≫ (f.hom.f ⊗ₘ g.hom.f) := by
  rw [Endofunctor.IsoAlgebra.comp_hom_f, nativeTensorMap_app_hom_f, Category.assoc,
    Mod.tensorLeftMap_app_comp_relativeTensorRightIso_hom_app]
  change (Mod.tensorLeft T.carrier).map f.hom.f ≫ _ ≫ _ = _
  rw [← Category.assoc, (Mod.relativeTensorRightIso T.carrier).hom.naturality f.hom.f,
    Category.assoc, MonoidalCategory.tensorHom_def]
  rfl

/-- Forgetting the Weil structure of the native tensor product `B ⊗ A`, with `A` the first
variable, gives the tensor product `A ⊗ B` of the underlying `ℓ`-adic sheaves. -/
def nativeForgetTensorIso :
    Functor.uncurry.obj (nativeTensorBifunctor k₀ l X).flip ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
        Functor.uncurry.obj (curriedTensor
          (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :=
  NatIso.ofComponents (fun PT ↦ (Mod.relativeTensorRightIso PT.2.carrier).app PT.1.carrier)
    (by
      rintro ⟨P, T⟩ ⟨P', T'⟩ ⟨f, g⟩
      exact nativeForgetTensor_naturality k₀ l X f g)

/-- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeForgetTensorIso`, as a morphism of bifunctors. -/
def nativeForgetTensorNatTrans :
    (Functor.postcompose₂.obj
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).obj
        (nativeTensorBifunctor k₀ l X).flip ⟶
      (((Functor.whiskeringLeft₂ _).obj
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).obj
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).obj
        (curriedTensor (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) where
  app P :=
    { app T := (nativeForgetTensorIso k₀ l X).hom.app (P, T)
      naturality T T' g := by
        simpa using (nativeForgetTensorIso k₀ l X).hom.naturality (Prod.mkHom (𝟙 P) g) }
  naturality P P' f := by
    refine NatTrans.ext (funext fun T ↦ ?_)
    simpa using (nativeForgetTensorIso k₀ l X).hom.naturality (Prod.mkHom f (𝟙 T))

instance (P T : ProEtaleWeilSheaf k₀ l X) :
    IsIso (((nativeForgetTensorNatTrans k₀ l X).app P).app T) :=
  inferInstanceAs (IsIso ((nativeForgetTensorIso k₀ l X).hom.app (P, T)))

/-- Forgetting the Weil structure of the native total tensor complex gives the tensor product of
the underlying complexes of `ℓ`-adic sheaves. -/
def nativeForgetTotalIso (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj (((nativeTensorTotal k₀ l X).obj P).obj T) ≅
      ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
          (.up ℤ)).obj P ⊗
        ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
          (.up ℤ)).obj T :=
  asIso (HomologicalComplex.mapBifunctorComparison (nativeForgetTensorNatTrans k₀ l X) (.up ℤ) P T)

/-- The comparison `AlgebraicGeometry.ProEtaleWeilSheaf.nativeForgetTotalIso` is natural in both
complexes. -/
lemma nativeForgetTotalIso_hom_naturality {P P' T T' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ}
    (f : P ⟶ P') (g : T ⟶ T') :
    ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).map (((nativeTensorTotal k₀ l X).map f).app T ≫
          ((nativeTensorTotal k₀ l X).obj P').map g) ≫ (nativeForgetTotalIso k₀ l X P' T').hom =
      (nativeForgetTotalIso k₀ l X P T).hom ≫
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
          ((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).map g) := by
  dsimp only [nativeTensorTotal]
  rw [NativeRestrictionDescentProof.map₂CochainComplex_map_comp_map]
  exact HomologicalComplex.mapBifunctorComparison_naturality _ _ f g

/-- A complex of pro-étale Weil sheaves whose underlying complex of `ℓ`-adic sheaves is K-flat is
K-flat for the native tensor product: forgetting the Weil structure identifies both native total
tensor products with tensor products of complexes of `ℓ`-adic sheaves, and reflects
quasi-isomorphisms. -/
theorem nativeIsKFlat_of_kFlat_forget (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj P)) :
    NativeIsKFlat k₀ l X P := by
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  have hU {A B : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (φ : A ⟶ B)
      (h : QuasiIso ((U.mapHomologicalComplex (.up ℤ)).map φ)) : QuasiIso φ :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ U).1 h
  refine ⟨fun {Q Q'} s hs ↦ hU _ ?_, fun {Q Q'} s hs ↦ hU _ ?_⟩
  · have h := hP.1 ((U.mapHomologicalComplex (.up ℤ)).map s)
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)
    have e := nativeForgetTotalIso_hom_naturality k₀ l X (𝟙 P) s
    rw [(nativeTensorTotal k₀ l X).map_id, NatTrans.id_app, Category.id_comp,
      CategoryTheory.Functor.map_id] at e
    rw [← HomologicalComplex.mem_quasiIso_iff]
    refine ((HomologicalComplex.quasiIso _ (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoMk (nativeForgetTotalIso k₀ l X P Q) (nativeForgetTotalIso k₀ l X P Q') ?_)).2 h
    simpa [MonoidalCategory.id_tensorHom] using e.symm
  · have h := hP.2 ((U.mapHomologicalComplex (.up ℤ)).map s)
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)
    have e := nativeForgetTotalIso_hom_naturality k₀ l X s (𝟙 P)
    rw [(nativeTensorTotal k₀ l X).obj Q' |>.map_id, Category.comp_id,
      CategoryTheory.Functor.map_id] at e
    rw [← HomologicalComplex.mem_quasiIso_iff]
    refine ((HomologicalComplex.quasiIso _ (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoMk (nativeForgetTotalIso k₀ l X Q P) (nativeForgetTotalIso k₀ l X Q' P) ?_)).2 h
    simpa [MonoidalCategory.tensorHom_id] using e.symm

omit [Fact (ringChar k₀ ≠ l)] in
/-- The tensor product `(Mod.tensorLeft P).obj N` of `ℓ`-adic sheaves is the monoidal tensor
product `N ⊗ P`, naturally in both variables. -/
def ordinaryTensorBifunctorFlipIso (Y : Scheme.{u}) :
    (ordinaryTensorBifunctor l Y).flip ≅ curriedTensor (ProEtale.AdicSheaf l Y) :=
  NatIso.ofComponents
    (fun N ↦ NatIso.ofComponents (fun P ↦ (Mod.relativeTensorRightIso P).app N)
      (fun {P P'} g ↦ by
        change (Mod.tensorLeftMap g).app N ≫ (Mod.relativeTensorRightIso P').hom.app N = _
        rw [Mod.tensorLeftMap_app_comp_relativeTensorRightIso_hom_app]
        rfl))
    (fun {N N'} f ↦ by
      refine NatTrans.ext (funext fun P ↦ ?_)
      exact (Mod.relativeTensorRightIso P).hom.naturality f)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The ordinary acyclic tensor test implies K-flatness for the monoidal tensor product of
complexes of `ℓ`-adic sheaves. -/
theorem kFlat_of_nativeOrdinaryKFlat (Y : Scheme.{u})
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (hP : NativeOrdinaryKFlat l Y P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr : (CochainComplex.mapBifunctor N P (curriedTensor _)).Acyclic := by
    refine (hP N hN).of_iso ?_
    exact (HomologicalComplex.mapBifunctorFlipIso P N (ordinaryTensorBifunctor l Y) (.up ℤ)).symm ≪≫
      HomologicalComplex.mapBifunctorIsoOfIso (ordinaryTensorBifunctorFlipIso l Y) N P (.up ℤ)
  have hr' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor _))).2 hr
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr', hr'⟩

/-- The complex of `ℓ`-adic sheaves underlying a K-flat complex of pro-étale Weil sheaves is
K-flat (`AlgebraicGeometry.ProEtaleWeilSheaf.native_two_sided_kflat_forget`). -/
theorem kFlat_forget_of_nativeIsKFlat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj P) :=
  kFlat_of_nativeOrdinaryKFlat l _ _ (native_two_sided_kflat_forget k₀ l X P hP)

end AlgebraicGeometry.ProEtaleWeilSheaf
