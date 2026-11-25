/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Normalized scalar tensor sections and their adjunction unit

Source: Stacks Project, Tag 03EK. These are proved tensor-section helpers for
ramified finite pullback, separated to keep individual module compile times small.
(blueprint: lem-weil-ramified-finite-tensor-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback

namespace TensorProof
universe v r
section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
variable
  (F : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
  (hm : ∀ {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N'), F.map f = eqToHom (h N) ≫
    SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (h N').symm)
/-- Section tensor in a functor identified with sheafified scalar extension.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
noncomputable def tensorSection
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :=
  (eqToHom (h N).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
/-- Unit tensor sections detect equality of maps out of scalar extension.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
theorem tensorSection_ext
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (f g : F.obj N ⟶ T)
    (he : ∀ (U : Cᵒᵖ) (x : N.val.obj U),
      f.val.app U (tensorSection φ F h N U 1 x) =
        g.val.app U (tensorSection φ F h N U 1 x)) : f = g := by
  let e := eqToIso (h N)
  apply (cancel_epi e.inv).mp
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  ext1 U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact he U x

include hm in
/-- Naturality of section tensors for a specified scalar-extension functor.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
theorem tensorSection_map
    {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N') (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : N.val.obj U) :
    (F.map f).val.app U (tensorSection φ F h N U s x) =
      tensorSection φ F h N' U s (f.val.app U x) := by
  let a : SheafOfModules.changeOfRingsPresheaf φ N ⟶
      SheafOfModules.changeOfRingsPresheaf φ N' :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ N f }
  have hn := congrArg (fun t ↦ t.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
    (CategoryTheory.toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map a))
  rw [hm]
  change (eqToHom (h N').symm).val.app U
    ((SheafOfModules.changeOfRingsHom φ N f).val.app U
      ((eqToHom (h N)).val.app U (tensorSection φ F h N U s x))) = _
  dsimp only [tensorSection]
  have hc {A B : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
      (e : A = B) (z : B.val.obj U) :
      (eqToHom e).val.app U ((eqToHom e.symm).val.app U z) = z := by
    cases e
    rfl
  rw [hc]
  congr 1
  exact hn.symm

include hm in
/-- The specified tensor functor is naturally isomorphic to the standard extension functor.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
noncomputable def tensorPresentation [EssentiallySmall.{r} C] :
    F ≅ CategoryTheory.CochainPullback.extensionFunctor φ :=
  NatIso.ofComponents (fun N ↦ eqToIso (h N)) (by
    intro N N' f
    rw [hm]
    simp [CategoryTheory.CochainPullback.extensionFunctor])

/-- The adjunction transported along a tensor presentation has the normalized unit.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
theorem tensorAdjunction_unit [EssentiallySmall.{r} C]
    (N : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : N.val.obj U) :
    ((((CategoryTheory.CochainPullback.extensionAdjunction φ).ofNatIsoLeft
      (tensorPresentation φ F h hm).symm).unit.app N).val.app U x) =
        tensorSection φ F h N U 1 x := by
  have hunit := (Classical.choose_spec
    (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique φ)).1 N U x
  rw [Adjunction.ofNatIsoLeft_unit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    tensorPresentation, Iso.symm_hom, NatIso.ofComponents_inv_app, eqToIso.inv]
  change (eqToHom (h N).symm).val.app U
    (((CategoryTheory.CochainPullback.extensionAdjunction φ).unit.app N).val.app U x) = _
  erw [hunit]
  unfold CategoryTheory.CochainPullback.extensionTmul tensorSection
  have hη := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
    (SheafOfModules.changeOfRingsPresheaf φ N)
  with_unfolding_all exact congrArg (fun f ↦ (eqToHom (h N).symm).val.app U
    (f.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) hη

end
end TensorProof

attribute [local irreducible] HasDerivedCategory.standard scalarWitness

/-- Scalar tensor sections are natural in the module.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
theorem scalar_map_tensor {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    {M N : Mod R} (f : M ⟶ N) (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((scalar.{t, u} c).map f).val.app U (tensor.{t, u} c M U s x) =
      tensor.{t, u} c N U s (f.val.app U x) := by
  with_unfolding_all
    exact TensorProof.tensorSection_map c (scalar.{t, u} c)
      (scalarWitness.{t, u} c).choose_spec.choose
      (fun {M N : Mod.{t, u} R} (a : M ⟶ N) ↦
        (scalarWitness.{t, u} c).choose_spec.choose_spec.choose a) f U s x

/-- The scalar adjunction transported through its actual sheafified tensor presentation.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections). -/
@[irreducible] noncomputable def scalarAdjunction {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S) :
    scalar.{t, u} c ⊣ SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c) :=
  (CategoryTheory.CochainPullback.extensionAdjunction c).ofNatIsoLeft
    (TensorProof.tensorPresentation c (scalar.{t, u} c) (scalarWitness.{t, u} c).choose_spec.choose
      (fun {A B : Mod.{t, u} R} (f : A ⟶ B) ↦
        (scalarWitness.{t, u} c).choose_spec.choose_spec.choose f)).symm

/-- The scalar adjunction unit is the section tensor with coefficient one.
Source: Stacks 03EK (blueprint: lem-weil-ramified-finite-tensor-sections).

Proof: transport the extension-of-scalars adjunction along the object and map
identifications of the specified scalar functor with sheafified balanced tensor.
The sheafification adjunction unit sends x to the image of 1 tensor x. Applying
the transported object identification gives the asserted normalized section.
The same tensor presentation proves map naturality, and its universal property
makes maps out of it equal when they agree on these unit tensors. -/
theorem scalarAdjunction_unit {W : Scheme.{t}}
    {R S : Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}} (c : R ⟶ S)
    (M : Mod.{t, u} R) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarAdjunction.{t, u} c).unit.app M).val.app U x = tensor.{t, u} c M U 1 x := by
  with_unfolding_all
    exact TensorProof.tensorAdjunction_unit c (scalar.{t, u} c)
      (scalarWitness.{t, u} c).choose_spec.choose
      (fun {A B : Mod.{t, u} R} (f : A ⟶ B) ↦
        (scalarWitness.{t, u} c).choose_spec.choose_spec.choose f) M U x

end WeilConjectures.RamifiedPullback
