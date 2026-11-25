/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels

/-! # Homogeneous total-tensor generator calculations

Source: Stacks Tags 03EL and 07A4.
(blueprint: lem-pur-coefficient-total-tensor-map-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open MonoidalCategory TensorProduct
namespace WeilConjectures
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso CategoryTheory.Functor.mapBifunctorHomologicalComplex
  HomologicalComplex₂.total
attribute [local instance] SheafOfModules.monoidalCategory

private theorem total_map_ι (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    {P Q P' Q' : CochainComplex (proEtaleRingModules W R) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') (p q i : ℤ) (h : p + q = i) :
    CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor W R) p q i h ≫
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W) R).map
        (Prod.mkHom a b)).f i =
    ((SheafOfModules.monoidalCategory R).tensorHom (a.f p) (b.f q)) ≫
      CochainComplex.ιMapBifunctor P' Q' (proEtaleOrdinaryTensor W R) p q i h := by
  simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
    Functor.map₂HomologicalComplex, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc]
  simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight]
  erw [Category.id_comp, Category.id_comp]

private theorem tensor_natural {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N')
    {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B')
    (eM : A ⟶ F.obj M) (eM' : A' ⟶ F.obj M')
    (eN : B ⟶ F.obj N) (eN' : B' ⟶ F.obj N')
    (hf : f ≫ eM' = eM ≫ F.map a) (hg : g ≫ eN' = eN ≫ F.map b) :
    (f ⊗ₘ g) ≫ (eM' ⊗ₘ eN') ≫ Functor.LaxMonoidal.μ F M' N' =
      (eM ⊗ₘ eN) ≫ Functor.LaxMonoidal.μ F M N ≫ F.map (a ⊗ₘ b) := by
  rw [← Functor.LaxMonoidal.μ_natural]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]

private theorem tensorPair_map (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    {M M' N N' : proEtaleRingModules W R} (f : M ⟶ M') (g : N ⟶ N')
    (V : W.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((SheafOfModules.monoidalCategory R).tensorHom f g).val.app V
        (proEtaleTensorPair W R M N V x y) =
      proEtaleTensorPair W R M' N' V (f.val.app V x) (g.val.app V y) := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  have ht : (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification.{u + 1} (𝟙 _)).map (f.val ⊗ₘ g.val) := by
    let sh := PresheafOfModules.sheafification.{u + 1} (𝟙
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
    let ε := asIso adj.counit
    have hf : f ≫ (ε.app M').inv = (ε.app M).inv ≫ sh.map f.val :=
      ε.inv.naturality f
    have hg : g ≫ (ε.app N').inv = (ε.app N).inv ≫ sh.map g.val :=
      ε.inv.naturality g
    change (f ⊗ₘ g) ≫ ((ε.app M').inv ⊗ₘ (ε.app N').inv) ≫
        Functor.LaxMonoidal.μ sh M'.val N'.val =
      ((ε.app M).inv ⊗ₘ (ε.app N).inv) ≫
        Functor.LaxMonoidal.μ sh M.val N.val ≫ sh.map (f.val ⊗ₘ g.val)
    exact tensor_natural sh f.val g.val f g (ε.app M).inv (ε.app M').inv
      (ε.app N).inv (ε.app N').inv hf hg
  have hi : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification.{u + 1} (𝟙 _)).map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ht, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun h ↦ h.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y))) hi
  have hη := congrArg (fun h ↦ h.app V (x ⊗ₜ[R.obj.obj V] y))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  exact hh.trans (congrArg
    ((SheafOfModules.tensorObjIsoSheafification M' N').inv.val.app V) hη.symm)

private theorem generator_ι {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P Q : CochainComplex (proEtaleRingModules W R) ℤ)
    (p q i : ℤ) (h : p + q = i) (V : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W) R P Q p q i h V x y =
      (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor W R) p q i h).val.app V
        (proEtaleTensorPair W R (P.X p) (Q.X q) V x y) := by
  rfl

/-- Total tensor maps act on homogeneous generators by applying the two input maps.
Source: Stacks 03EK and 07A4
(blueprint: lem-pur-coefficient-total-tensor-map-generators).
Proof: precompose the total map with the inclusion of bidegree (p,q). The defining
map of the totalization is tensorHom of the two component maps on this summand.
Naturality of tensor sheafification sends the pure tensor to the pure tensor of
its images. Apply the target summand inclusion. This calculation has no boundedness
or flatness assumption and preserves the two degrees, hence introduces no sign. -/
theorem coefficientTotalTensor_map_generator (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    {P Q P' Q' : CochainComplex (proEtaleRingModules W R) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') (p q i : ℤ) (h : p + q = i) (V : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W) R).map
      (Prod.mkHom a b)).f i).val.app V
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W) R P Q p q i h V x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W) R P' Q' p q i h V
        ((a.f p).val.app V x) ((b.f q).val.app V y) := by
  rw [generator_ι, generator_ι]
  change (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor W R) p q i h ≫
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W) R).map
      (Prod.mkHom a b)).f i).val.app V _ = _
  erw [total_map_ι]
  change (CochainComplex.ιMapBifunctor P' Q' (proEtaleOrdinaryTensor W R) p q i h).val.app V
    (((SheafOfModules.monoidalCategory R).tensorHom (a.f p) (b.f q)).val.app V
      (proEtaleTensorPair W R (P.X p) (Q.X q) V x y)) = _
  erw [tensorPair_map]

end WeilConjectures
