/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Braiding compatibility of the ordinary scalar tensor comparison

Source: the pure-tensor calculation in the finite intrinsic tensor symmetry proof;
Stacks Project, Tags 00YV, 06YL and 0FPT.
(blueprint: lem-sf-finite-scalar-ordinary-tensor-braiding).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

attribute [local irreducible] AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence

attribute [local irreducible] PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local implicit_reducible] WeilConjectures.finiteScalarPresheafMonoidal
  PresheafOfModules.monoidalCategory PresheafOfModules.monoidalCategoryStruct
  AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf

attribute [local instance 20000] ProEtale.sheafBraidedCategory

namespace WeilConjectures

private theorem scalar_sheafification_braiding
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {O : Cᵒᵖ ⥤ CommRingCat.{u + 1}} {R : Sheaf J CommRingCat.{u + 1}}
    (α : (O ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (M N : PresheafOfModules.{u + 1} (O ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :
    let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
    let := SheafOfModules.symmetricCategory.{u, u + 1, u + 1} R
    let e := (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses α).choose
    (PresheafOfModules.sheafification.{u + 1} α).map (β_ M N).hom ≫ e.inv.app (N, M) =
      e.inv.app (M, N) ≫
        (β_ ((PresheafOfModules.sheafification.{u + 1} α).obj M)
          ((PresheafOfModules.sheafification.{u + 1} α).obj N)).hom := by
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.symmetricCategory.{u, u + 1, u + 1} R
  let S := PresheafOfModules.sheafification.{u + 1} α
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} α
  let e := (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses α).choose
  have he := (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses α).choose_spec
  apply PresheafOfModules.sheafifiedTensor_hom_ext α M N
  intro V x y
  have hn := congrArg (fun f ↦ (f.app V).hom (x ⊗ₜ[O.obj V] y))
    (adj.unit.naturality (β_ M N).hom)
  change ((adj.unit.app (N ⊗ M)).app V) (y ⊗ₜ[O.obj V] x) =
    (S.map (β_ M N).hom).val.app V
      (((adj.unit.app (M ⊗ N)).app V) (x ⊗ₜ[O.obj V] y)) at hn
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [← hn]
  erw [he N M V y x, he M N V x y]
  exact (CochainPullback.moduleTmul_braiding.{u + 1, u + 1, u}
    (R := R) (S.obj M) (S.obj N) V _ _).symm

/-- The constructed ordinary scalar tensor comparison preserves the sheaf braiding.
Source: Stacks Tags 00YV and 0GMW; the ordinary pure-tensor comparison in
lem-sf-finite-intrinsic-tensor-symmetry, proof step 2.
Proof: expand the comparison as its four defining natural isomorphisms. The
fixed-scalar sheafification tensorator is braided. The realization factorization
isomorphism commutes with the braiding by naturality. Encoding fixed-scalar
presheaves as module presheaves commutes sectionwise with the tensor swap.
Finally the module-sheafification tensor comparison commutes with the swap:
precompose with its adjunction unit and evaluate on a pure tensor. Its stated
normalization and moduleTmul_braiding send both routes to the tensor of the two
unit sections in reversed order. The sheafification adjunction and the tensor
universal property detect equality. Compose these four squares.
(blueprint: lem-sf-finite-scalar-ordinary-tensor-braiding). -/
theorem finiteScalarOrdinaryTensorIso_braiding
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    let := SheafOfModules.monoidalCategory (proEtaleConstantRing X B)
    let := SheafOfModules.symmetricCategory (proEtaleConstantRing X B)
    (sfIntrinsicModuleEquivalence X B).functor.map (β_ M N).hom ≫
      (finiteScalarOrdinaryTensorIso X B).hom.app (N, M) =
    (finiteScalarOrdinaryTensorIso X B).hom.app (M, N) ≫
      (β_ ((sfIntrinsicModuleEquivalence X B).functor.obj M)
        ((sfIntrinsicModuleEquivalence X B).functor.obj N)).hom := by
  let J := ProEt.topology X
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  let E := ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1} B)
  let S := PresheafOfModules.sheafification.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X B)
  let U := sheafToPresheaf J A
  let L := presheafToSheaf J A
  let F := ProEtale.finiteCoefficientIntrinsicRealization X B
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing X B)
  let := SheafOfModules.symmetricCategory (proEtaleConstantRing X B)
  let := finiteScalarPresheafMonoidal X B
  let t : E ⋙ S ⟶ L ⋙ F :=
    Functor.whiskerRight (sheafificationAdjunction J A).unit (E ⋙ S)
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact finiteScalarModuleSheafificationUnit_isIso X B P
  let h : E ⋙ S ≅ L ⋙ F := asIso t
  let c := asIso (sheafificationAdjunction J A).counit
  let e : U.prod U ⋙ tensor _ ⋙ L ≅ tensor _ :=
    isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
      isoWhiskerRight (NatIso.prod c c) (tensor _)
  let eS := Classical.choose
    (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
      (O := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))
      (ProEtale.finiteCoefficientIntrinsicScalarMap X B))
  have he : L.map (β_ (U.obj M) (U.obj N)).hom ≫ e.hom.app (N, M) =
      e.hom.app (M, N) ≫ (β_ M N).hom := by
    change L.map (β_ (U.obj M) (U.obj N)).hom ≫
        (Functor.OplaxMonoidal.δ L (U.obj N) (U.obj M) ≫
          (c.hom.app N ⊗ₘ c.hom.app M)) =
      (Functor.OplaxMonoidal.δ L (U.obj M) (U.obj N) ≫
        (c.hom.app M ⊗ₘ c.hom.app N)) ≫ (β_ M N).hom
    rw [Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
    rw [← BraidedCategory.braiding_naturality]
    rfl
  have he' : (β_ M N).hom ≫ e.inv.app (N, M) =
      e.inv.app (M, N) ≫ L.map (β_ (U.obj M) (U.obj N)).hom := by
    apply (cancel_epi (e.hom.app (M, N))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [← he, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hh := h.inv.naturality (β_ (U.obj M) (U.obj N)).hom
  have hs := scalar_sheafification_braiding
    (O := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))
    (R := proEtaleConstantRing X B)
    (ProEtale.finiteCoefficientIntrinsicScalarMap X B) (E.obj (U.obj M)) (E.obj (U.obj N))
  change (E ⋙ S).map (β_ (U.obj M) (U.obj N)).hom ≫
      eS.inv.app (E.obj (U.obj N), E.obj (U.obj M)) =
    eS.inv.app (E.obj (U.obj M), E.obj (U.obj N)) ≫
      (β_ (F.obj M) (F.obj N)).hom at hs
  unfold finiteScalarOrdinaryTensorIso sfIntrinsicModuleEquivalence
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app, Category.assoc]
  erw [S.map_id, Category.id_comp, S.map_id, Category.id_comp]
  change F.map (β_ M N).hom ≫
      F.map (e.inv.app (N, M)) ≫ h.inv.app (U.obj N ⊗ U.obj M) ≫
        eS.inv.app (E.obj (U.obj N), E.obj (U.obj M)) =
    F.map (e.inv.app (M, N)) ≫ h.inv.app (U.obj M ⊗ U.obj N) ≫
      eS.inv.app (E.obj (U.obj M), E.obj (U.obj N)) ≫
        (β_ (F.obj M) (F.obj N)).hom
  rw [← F.map_comp_assoc, he', F.map_comp, Category.assoc]
  change F.map (e.inv.app (M, N)) ≫ (L ⋙ F).map _ ≫ _ = _
  erw [reassoc_of% hh]
  erw [hs]

end WeilConjectures
