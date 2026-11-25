/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorData
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal

/-! # Derived tensor equation from the ordinary coefficient square

Source: Stacks Project, Tag 07A4; derived composition step of
`lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-derived-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap upperStar internalScalarMonoidal
  Functor.leftDerivedFunctorCompNatIso Functor.leftDerivedTensorComparison
  leftDerivedUpperStarTensor upperStarFromPoint
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal

-- Keep the monoidal data abstract until the square has been specialized.
private structure TensorSquare
    {C : Type*} [Category* C] [MonoidalCategory C]
    {D : Type*} [Category* D] [MonoidalCategory D]
    {E : Type*} [Category* E] [MonoidalCategory E]
    {D' : Type*} [Category* D'] [MonoidalCategory D']
    (F₁ : C ⥤ D) (F₂ : D ⥤ E) (G₁ : C ⥤ D') (G₂ : D' ⥤ E)
    (θ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (d₁ : (Functor.postcompose₂.obj F₁).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₁).obj (curriedTensor D))
    (d₂ : (Functor.postcompose₂.obj F₂).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ E).obj F₂).obj F₂).obj (curriedTensor E))
    (e₁ : (Functor.postcompose₂.obj G₁).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D').obj G₁).obj G₁).obj (curriedTensor D'))
    (e₂ : (Functor.postcompose₂.obj G₂).obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ E).obj G₂).obj G₂).obj (curriedTensor E)) : Prop where
  square (A B : C) :
    F₂.map ((d₁.app A).app B) ≫ (d₂.app (F₁.obj A)).app (F₁.obj B) =
      θ.inv.app (A ⊗ B) ≫ G₂.map ((e₁.app A).app B) ≫
        (e₂.app (G₁.obj A)).app (G₁.obj B) ≫ (θ.hom.app A ⊗ₘ θ.hom.app B)

-- Boxing the generic equation avoids reducing concrete tensor constructions when
-- matching the module-object instances of the derived monoidal structures.
private theorem canonical_tensor_square
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type*} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    {E : Type*} [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
    [MonoidalClosed E] [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
    {D' : Type*} [Category.{u + 1} D'] [Abelian D']
    [IsGrothendieckAbelian.{u + 1} D'] [MonoidalCategory D'] [MonoidalPreadditive D']
    [MonoidalClosed D'] [BraidedCategory D'] [Abelian.HasFunctorialFlatResolution D']
    (F₁ : C ⥤ D) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
    (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
    (G₁ : C ⥤ D') [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
    (G₂ : D' ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]
    (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom] :
    TensorSquare F₁.leftDerivedFunctor F₂.leftDerivedFunctor
      G₁.leftDerivedFunctor G₂.leftDerivedFunctor
      (Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ)
      F₁.leftDerivedTensorComparison F₂.leftDerivedTensorComparison
      G₁.leftDerivedTensorComparison G₂.leftDerivedTensorComparison := by
  exact ⟨Functor.map_leftDerivedTensorComparison_comp_eq_of_iso F₁ F₂ G₁ G₂ τ⟩

private theorem tensor_square_from_inv
    {C : Type*} [Category* C] {P Q U V W Z T : C}
    (i i' : P ≅ Q) (hi : i = i')
    {r r' : Q ⟶ U} {s s' : U ⟶ T} {a a' : P ⟶ V} {b b' : V ⟶ W}
    {c : W ⟶ Z} {d : Z ⟶ T} {k : W ⟶ T}
    (hr : r = r') (hs : s = s') (ha : a = a') (hb : b = b') (hk : c ≫ d = k)
    (h : r' ≫ s' = i'.inv ≫ a' ≫ b' ≫ k) :
    a ≫ b ≫ c ≫ d = i.hom ≫ r ≫ s := by
  cases hi
  cases hr
  cases hs
  cases ha
  cases hb
  have h' := congrArg (fun t ↦ i.hom ≫ t) h
  simp only [Iso.hom_inv_id_assoc] at h'
  rw [hk]
  exact h'.symm

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]
set_option linter.unusedSectionVars false in
/-- The monoidal ordinary coefficient square induces the specified derived tensor equation.

Source: Stacks Project, Cohomology on Sites, Tag 07A4, compatibility of composite
pullbacks and tensor products; step 4--5 of
`lem-sfb-coefficient-scalar-tensor-realization`.
(blueprint: lem-sfb-coefficient-scalar-derived-tensor-square).

Proof: apply Functor.map_leftDerivedTensorComparison_comp_eq_of_iso to
F1 = upperStar R f, F2 = extendScalars a_X, G1 = extendScalars a_Y,
G2 = upperStar S f and tau = (pullIso a f).symm. All four functors are exact,
additive, preserve flat objects and are left adjoints. The hypothesis supplies the
ordinary monoidality required by that theorem. Its derived comparison is exactly
coefficientScalarPathIso. The scalar comparisons are internalScalarTensorComparison
by the definition using asIso of leftDerivedTensorComparison. The geometric comparison
is leftDerivedTensorComparison by leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison.
Precompose the theorem's equality by the hom component of coefficientScalarPathIso at
A tensor B and cancel its adjacent inverse. Reverse the equality and expand tensorHom
as whiskerRight followed by whiskerLeft. The result is the displayed equation. This
argument takes place in the unbounded derived categories and uses no geometric
finiteness assumptions. -/
theorem coefficientScalarDerivedTensorSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hmono : letI := internalScalarMonoidal a X
      letI := internalScalarMonoidal a Y
      letI := monoidal_upperStar R f
      letI := monoidal_upperStar S f
      NatTrans.IsMonoidal (pullIso a f).symm.hom) :
    ∀ A B : DerivedCategory (ModuleRingedComparison.internalModules R Y),
      (moduleObjectDerivedPullback S f).map
          (((internalScalarTensorComparison a Y).app A).app B) ≫
        coefficientGeometricTensorComparison S f
          ((internalScalarExtension a Y).obj A)
          ((internalScalarExtension a Y).obj B) ≫
        ((derivedTensor S X).map ((coefficientScalarPathIso a f).hom.app A)).app
          ((moduleObjectDerivedPullback S f).obj
            ((internalScalarExtension a Y).obj B)) ≫
        ((derivedTensor S X).obj
          ((internalScalarExtension a X).obj
            ((moduleObjectDerivedPullback R f).obj A))).map
              ((coefficientScalarPathIso a f).hom.app B) =
      (coefficientScalarPathIso a f).hom.app (((derivedTensor R Y).obj A).obj B) ≫
        (internalScalarExtension a X).map
          (coefficientGeometricTensorComparison R f A B) ≫
        ((internalScalarTensorComparison a X).app
          ((moduleObjectDerivedPullback R f).obj A)).app
            ((moduleObjectDerivedPullback R f).obj B) := by
  let := internalScalarMonoidal a X
  let := internalScalarMonoidal a Y
  let := monoidal_upperStar R f
  let := monoidal_upperStar S f
  let := hmono
  intro A B
  have hPack := canonical_tensor_square
    (upperStar R f) (Mod.extendScalars (coefficientMap a X))
    (Mod.extendScalars (coefficientMap a Y)) (upperStar S f) (pullIso a f).symm
  have hR := congr_app (congr_app
    (leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison R f) A) B
  have hS := congr_app (congr_app
    (leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison S f)
    ((internalScalarExtension a Y).obj A)) ((internalScalarExtension a Y).obj B)
  have hX₀ : internalScalarTensorComparison a X =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedTensorComparison := by rfl
  have hY₀ : internalScalarTensorComparison a Y =
      (Mod.extendScalars (coefficientMap a Y)).leftDerivedTensorComparison := by rfl
  have hX := congr_app (congr_app hX₀
    ((moduleObjectDerivedPullback R f).obj A)) ((moduleObjectDerivedPullback R f).obj B)
  have hY := congr_app (congr_app hY₀ A) B
  have hθ : coefficientScalarPathIso a f =
      Functor.leftDerivedFunctorCompNatIso
        (upperStar R f) (Mod.extendScalars (coefficientMap a X))
        (Mod.extendScalars (coefficientMap a Y)) (upperStar S f) (pullIso a f).symm := by
    rfl
  let θ' : internalScalarExtension a Y ⋙ moduleObjectDerivedPullback S f ≅
      moduleObjectDerivedPullback R f ⋙ internalScalarExtension a X :=
    Functor.leftDerivedFunctorCompNatIso
      (upperStar R f) (Mod.extendScalars (coefficientMap a X))
      (Mod.extendScalars (coefficientMap a Y)) (upperStar S f) (pullIso a f).symm
  let δR : leftDerivedUpperStarTensorLeft R f ⟶ leftDerivedUpperStarTensorRight R f :=
    (upperStar R f).leftDerivedTensorComparison
  let δS : leftDerivedUpperStarTensorLeft S f ⟶ leftDerivedUpperStarTensorRight S f :=
    (upperStar S f).leftDerivedTensorComparison
  let δX : (Functor.postcompose₂.obj (internalScalarExtension a X)).obj (derivedTensor R X) ⟶
      (((Functor.whiskeringLeft₂ _).obj (internalScalarExtension a X)).obj
        (internalScalarExtension a X)).obj (derivedTensor S X) :=
    (Mod.extendScalars (coefficientMap a X)).leftDerivedTensorComparison
  let δY : (Functor.postcompose₂.obj (internalScalarExtension a Y)).obj (derivedTensor R Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (internalScalarExtension a Y)).obj
        (internalScalarExtension a Y)).obj (derivedTensor S Y) :=
    (Mod.extendScalars (coefficientMap a Y)).leftDerivedTensorComparison
  have hSquare : TensorSquare (moduleObjectDerivedPullback R f) (internalScalarExtension a X)
      (internalScalarExtension a Y) (moduleObjectDerivedPullback S f) θ' δR δX δY δS := hPack
  let P := ((derivedTensor R Y).obj A).obj B
  let i := (coefficientScalarPathIso a f).app P
  let i' := θ'.app P
  let r := (internalScalarExtension a X).map (coefficientGeometricTensorComparison R f A B)
  let r' := (internalScalarExtension a X).map
    ((δR.app A).app B)
  let s := ((internalScalarTensorComparison a X).app
    ((moduleObjectDerivedPullback R f).obj A)).app ((moduleObjectDerivedPullback R f).obj B)
  let s' := (δX.app ((moduleObjectDerivedPullback R f).obj A)).app
    ((moduleObjectDerivedPullback R f).obj B)
  let a₀ := (moduleObjectDerivedPullback S f).map
    (((internalScalarTensorComparison a Y).app A).app B)
  let a' := (moduleObjectDerivedPullback S f).map ((δY.app A).app B)
  let b := coefficientGeometricTensorComparison S f
    ((internalScalarExtension a Y).obj A) ((internalScalarExtension a Y).obj B)
  let b' := (δS.app ((internalScalarExtension a Y).obj A)).app
    ((internalScalarExtension a Y).obj B)
  let c := ((derivedTensor S X).map ((coefficientScalarPathIso a f).hom.app A)).app
    ((moduleObjectDerivedPullback S f).obj ((internalScalarExtension a Y).obj B))
  let d := ((derivedTensor S X).obj
    ((internalScalarExtension a X).obj ((moduleObjectDerivedPullback R f).obj A))).map
      ((coefficientScalarPathIso a f).hom.app B)
  let k := θ'.hom.app A ⊗ₘ θ'.hom.app B
  have hi : i = i' := congrArg (fun τ ↦ τ.app P) hθ
  have hr : r = r' := congrArg (internalScalarExtension a X).map hR
  have hs : s = s' := hX
  have ha : a₀ = a' := congrArg (moduleObjectDerivedPullback S f).map hY
  have hb : b = b' := hS
  have hk₁ := congrArg (fun τ ↦ τ.hom.app A ⊗ₘ τ.hom.app B) hθ
  have hk₂ : c ≫ d =
      (coefficientScalarPathIso a f).hom.app A ⊗ₘ
        (coefficientScalarPathIso a f).hom.app B := by
    exact (MonoidalCategory.tensorHom_def _ _).symm
  have hk : c ≫ d = k := hk₂.trans hk₁
  have hh : r' ≫ s' = i'.inv ≫ a' ≫ b' ≫ k := hSquare.square A B
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact tensor_square_from_inv i i' hi
    (r := r) (r' := r') (s := s) (s' := s') (a := a₀) (a' := a')
    (b := b) (b' := b') (c := c) (d := d) (k := k) hr hs ha hb hk hh

end AlgebraicGeometry.ProEtale.CondensedRing
