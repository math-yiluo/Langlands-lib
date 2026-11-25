/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization
public import WeilConjectures.WeilSheaf.Native.NativeForgetTotalTensor
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.Monoidal.KFlatBifunctorTransport
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorRightIsoNaturality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor

/-!
# The condensed realization and the native tensor product

* `AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_condensedTensorIso`: the condensed model
  `AdicSheaf ℓ ≌ Mod_{Λ}` carries the ordinary relative tensor to the tensor of module objects.
* `AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_condensedRealizationTensorIso`: the condensed
  realization carries the native tensor of pro-étale Weil sheaves to the tensor of module objects.
* `AlgebraicGeometry.ProEtaleWeilSheaf.kFlat_condensedRealization_mapHomologicalComplex`: the
  condensed realization of a native K-flat complex is a K-flat complex.
* `AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_of_kFlat_condensedRealization`: conversely,
  a complex whose condensed realization is K-flat is native K-flat.
* `AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_mapHomologicalComplex_obj_of_iso`: the
  same, for the image of a complex under a functor compatible with the condensed realizations.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

section Ordinary

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

/-- The condensed model `AdicSheaf ℓ ≌ Mod_{Λ}` carries the ordinary relative tensor product of
`ℓ`-adic sheaves to the tensor product of module objects over `Λ`. -/
theorem nonempty_condensedTensorIso :
    Nonempty ((Functor.postcompose₂.obj (adicSheafEquivCondensedMod l S).functor).obj
        (ordinaryTensorBifunctor l S).flip ≅
      (((Functor.whiskeringLeft₂ _).obj (adicSheafEquivCondensedMod l S).functor).obj
        (adicSheafEquivCondensedMod l S).functor).obj (curriedTensor _)) := by
  obtain ⟨m⟩ := nativeScalarForgetting_monoidal l S
  let : (adicSheafEquivCondensedMod l S).functor.Monoidal :=
    inferInstanceAs
      (AdicSheaf.forgetAb l S ⋙ Mod.comap (condensedRingObjIsoForgetAb l S).hom).Monoidal
  exact ⟨(Functor.postcompose₂.obj _).mapIso (ordinaryTensorBifunctorFlipIso l S) ≪≫
    Functor.Monoidal.postcomposeCurriedTensorIso _⟩

end Ordinary

section Weil

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The condensed realization carries the native tensor product of pro-étale Weil sheaves (left
factor first) to the tensor product of module objects over `Λ` on the geometric fiber. -/
theorem nonempty_condensedRealizationTensorIso :
    Nonempty ((Functor.postcompose₂.obj (condensedRealization k₀ l X)).obj
        (nativeTensorBifunctor k₀ l X).flip ≅
      (((Functor.whiskeringLeft₂ _).obj (condensedRealization k₀ l X)).obj
        (condensedRealization k₀ l X)).obj (curriedTensor _)) := by
  obtain ⟨τ⟩ := nonempty_condensedTensorIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  exact ⟨Functor.postcompose₂CompIso
    (Functor.postcompose₂FlipIsoOfUncurry (tensorBifunctorForget k₀ l X)) τ⟩

/-- The condensed realization of a native K-flat complex of pro-étale Weil sheaves is a K-flat
complex of module objects. -/
theorem kFlat_condensedRealization_mapHomologicalComplex
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hP : NativeIsKFlat k₀ l X P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj P) := by
  have (A B : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) : A.HasTensor B := by
    intro n
    infer_instance
  obtain ⟨τ⟩ := nonempty_condensedTensorIso l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have h := native_two_sided_kflat_forget k₀ l X P hP
  have := Functor.flip_additive
    (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  have := Functor.flip_obj_additive
    (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  refine ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (condensedRealization k₀ l X))
      (.up ℤ)).app P)
    (CochainComplex.kFlat_of_acyclic_tensor _ (Functor.acyclic_tensor_of_isEquivalence τ _ ?_))
  intro N hN i
  exact (h N hN i).of_iso (HomologicalComplex.mapBifunctorFlipIso _ _ _ _).symm

-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology _) Ab) _`
/-- A complex of pro-étale Weil sheaves whose condensed realization is K-flat is native K-flat:
the condensed realization is exact, conservative and carries the native tensor to the tensor of
module objects, so the quasi-isomorphism tests can be checked after realization. -/
theorem nativeIsKFlat_of_kFlat_condensedRealization
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj P)) :
    NativeIsKFlat k₀ l X P := by
  obtain ⟨τ⟩ := nonempty_condensedRealizationTensorIso k₀ l X
  have h := fun {Q Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (s : Q ⟶ Q') hs ↦
    Functor.quasiIso_mapBifunctorMap_of_kFlat τ P hP s hs
  refine ⟨fun s hs ↦ (h s hs).1, fun s hs ↦ ?_⟩
  rw [Functor.flip_obj_map]
  unfold nativeTensorTotal
  exact (h s hs).2

end Weil

section Transport

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology _) Ab) _`
/-- Let `F` be an additive functor between pro-étale Weil sheaves on `Y` and on `X` which is
compatible, through the condensed realizations, with an additive functor `G` of module objects.
If the image under `G` of the condensed realization of a complex `P` is K-flat, then `F P` is
native K-flat. -/
theorem nativeIsKFlat_mapHomologicalComplex_obj_of_iso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (F : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l X) [F.Additive]
    (G : Mod (Sheaf (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) [G.Additive]
    (e : F ⋙ condensedRealization k₀ l X ≅ condensedRealization k₀ l Y ⋙ G)
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat ((G.mapHomologicalComplex (.up ℤ)).obj
      (((condensedRealization k₀ l Y).mapHomologicalComplex (.up ℤ)).obj P))) :
    NativeIsKFlat k₀ l X ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  nativeIsKFlat_of_kFlat_condensedRealization k₀ l X _
    (Functor.prop_mapHomologicalComplex_obj_of_iso e _ _ P hP)

end Transport

end AlgebraicGeometry.ProEtaleWeilSheaf
