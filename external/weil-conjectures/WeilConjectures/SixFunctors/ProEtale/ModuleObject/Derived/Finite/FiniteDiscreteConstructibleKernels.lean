/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodedPresentation
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleKernels

/-! # Kernels of constructible internal modules with finite discrete coefficients

Source: Bhatt--Scholze, Section 5.1 and Lemma 5.4.1, and the noetherian constructible
Serre theorem. Finite presentations are compared before passing to derived categories.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Maps from the internal regular module are determined by the image of one.
private noncomputable def regularHomEquiv
    {R : Type (u + 1)} [CommRing R]
    (M : Mod Ab.{u + 1} (AddCommGrpCat.of R)) :
    (Mod.regular (AddCommGrpCat.of R) ⟶ M) ≃ M.X :=
  { toFun := fun f ↦ ((MonObj.one : MonoidalCategoryStruct.tensorUnit Ab.{u + 1} ⟶
      AddCommGrpCat.of R) ≫ f.hom) (ULift.up 1)
    invFun := fun x ↦ Mod.regularLift M (AddCommGrpCat.ofHom (uliftZMultiplesHom M.X x))
    left_inv := by
      intro f
      apply Mod.regular_hom_ext
      rw [Mod.one_comp_regularLift]
      apply (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.X).symm).injective
      simp [Equiv.trans_apply, ConcreteCategory.homEquiv, uliftZMultiplesHom]
      rfl
    right_inv := by
      intro x
      change ((MonObj.one : MonoidalCategoryStruct.tensorUnit Ab.{u + 1} ⟶ AddCommGrpCat.of R) ≫
        (Mod.regularLift M (AddCommGrpCat.ofHom (uliftZMultiplesHom M.X x))).hom)
          (ULift.up 1) = x
      rw [Mod.one_comp_regularLift]
      change (1 : ℤ) • x = x
      exact one_zsmul x }

-- The specified equivalence G need not fix the regular module definitionally.
-- Identify the two representing objects using hG and fully faithful coyoneda.
private noncomputable def scalarRegularIso
    {R : Type (u + 1)} [CommRing R]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of R) ⥤ ModuleCat.{u + 1} R)
    [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of R)) :
    G.obj (Mod.regular (AddCommGrpCat.of R)) ≅ ModuleCat.of R R := by
  let e (M : Mod Ab.{u + 1} (AddCommGrpCat.of R)) :
      (Mod.regular (AddCommGrpCat.of R) ⟶ M) ≃ (ModuleCat.of R R ⟶ G.obj M) :=
    (regularHomEquiv M).trans
      (((forget Ab.{u + 1}).mapIso ((eqToIso hG).app M).symm).toEquiv.trans
        ((LinearMap.ringLmapEquivSelf R ℤ (G.obj M)).toEquiv.symm.trans
          (ModuleCat.homEquiv (M := ModuleCat.of R R) (N := G.obj M)).symm))
  have he (M : Mod Ab.{u + 1} (AddCommGrpCat.of R))
      (h : Mod.regular (AddCommGrpCat.of R) ⟶ M) :
      e M h 1 = ((eqToIso hG).inv.app M) (regularHomEquiv M h) := by
    let y : G.obj M := ((eqToIso hG).inv.app M) (regularHomEquiv M h)
    change (1 : R) • y = y
    exact one_smul _ _
  let i : G ⋙ CategoryTheory.coyoneda.obj
      (Opposite.op (G.obj (Mod.regular (AddCommGrpCat.of R)))) ≅
      G ⋙ CategoryTheory.coyoneda.obj (Opposite.op (ModuleCat.of R R)) :=
    NatIso.ofComponents
      (fun M ↦ ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans (e M)).toIso) (by
        intro M N f
        ext g
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        change e N (G.preimage (g ≫ G.map f)) 1 = (e M (G.preimage g) ≫ G.map f) 1
        rw [G.preimage_comp, G.preimage_map]
        let x := ((MonObj.one : MonoidalCategoryStruct.tensorUnit Ab.{u + 1} ⟶ AddCommGrpCat.of R) ≫
          (G.preimage g).hom) (ULift.up 1)
        have hn := ConcreteCategory.congr_hom ((eqToIso hG).inv.naturality f) x
        change ((eqToIso hG).inv.app N) (f.hom x) =
          (G.map f) (((eqToIso hG).inv.app M) x) at hn
        rw [he]
        change ((eqToIso hG).inv.app N) (f.hom x) =
          (G.map f) (e M (G.preimage g) 1)
        rw [he]
        exact hn)
  let j := (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ _).obj G)).preimageIso i
  exact (CategoryTheory.Coyoneda.fullyFaithful.preimageIso j).unop.symm

-- A finite presentation over B sheafifies to a finite internal presentation.
private lemma encodedConstantFP
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Finite B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (T : Scheme.{u}) (P : ModuleCat.{u + 1} (ULift.{u + 1} B)) [Finite P] :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
        ((constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P)) := by
  let R := ULift.{u + 1} B
  let J := Scheme.ProEt.topology T
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncoding J R G hG
  let S := constantSheaf J (ModuleCat.{u + 1} R)
  have : H.IsEquivalence :=
    CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingIsEquivalence J R G hG
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  let A := (presheafToSheaf J Ab.{u + 1}).obj
    (CategoryTheory.ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) R)
  let c (n : ℕ) : H.obj (Mod.finiteFree A n) ≅
      S.obj (ModuleCat.of R (Fin n → R)) :=
    CategoryTheory.ConstantInternalModuleSheafEncoding.encFiniteFreeIso J R G hG n ≪≫
      S.mapIso (biproduct.mapIso (fun _ ↦ scalarRegularIso G hG) ≪≫
        ModuleCat.biproductIsoPi _)
  have : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R P
  let f' : ModuleCat.of R (Fin n → R) ⟶ P := ModuleCat.ofHom f
  let g' : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) :=
    ModuleCat.ofHom g
  let ec : P ≅ cokernel g' :=
    (ModuleCat.isColimitCokernelCofork g' f' hg hf).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let d : Mod.finiteFree A m ⟶ Mod.finiteFree A n :=
    H.preimage ((c m).hom ≫ S.map g' ≫ (c n).inv)
  have hc : Mod.IsFinitelyPresented A (H.inv.obj (S.obj P)) := by
    refine ⟨n, m, d, ⟨?_⟩⟩
    apply H.preimageIso
    exact H.asEquivalence.counitIso.app _ ≪≫ S.mapIso ec ≪≫
      PreservesCokernel.iso S g' ≪≫
      cokernel.mapIso _ (H.map d) (c m).symm (c n).symm (by simp [d]) ≪≫
      (PreservesCokernel.iso H d).symm
  unfold finiteDiscreteCoefficientEquivalence
  exact finitePresentation_comap (inv (finiteDiscreteSchemeRingIso B T eR).hom) hc

private lemma internalLisseFP
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Finite B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (M : FiniteDiscreteInternalModules B T)
    (e : (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).obj F) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
      M := by
  classical
  obtain ⟨⟨C₀, hC⟩⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  -- On a nonempty cover member, finiteness of a constant sheaf implies finiteness
  -- of its value. Empty members carry no local finite-presentation obligation.
  let C := C₀.nonemptyMembers
  let D : Scheme.Cover.{u} Scheme.proetalePrecoverage T :=
    ⟨C.toPreZeroHypercover, Scheme.etalePrecoverage_le_proetalePrecoverage _ C.mem₀⟩
  refine ⟨D, ?_⟩
  rintro ⟨i, hi⟩
  have hc : ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.f i)).obj F).IsConstant
      (C₀.X i).smallEtaleTopology :=
    (Scheme.isConstant_over_iff_upperStar _ (C₀.etalePrecoverageToEtale i) F).mp (hC i)
  obtain ⟨P, ⟨eP⟩⟩ :=
    (((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
      (C₀.f i)).obj F).mem_essImage_of_isConstant)
  have : Scheme.IsFiniteSheaf
      ((constantSheaf (C₀.X i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P) := by
    have := Scheme.IsFiniteSheaf.upperStar (C₀.f i) F
    exact Scheme.IsFiniteSheaf.of_iso eP.symm
  have : Nonempty (C₀.X i) := hi
  have : Module.Finite (ULift.{u + 1} B) P :=
    Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf (Y := C₀.X i) P
  have : Finite P := Module.finite_of_finite (ULift.{u + 1} B)
  let α := condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) (C₀.f i)
  let raw := ((ProEtale.upperStar Ab.{u + 1} (C₀.f i)).mapMod
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M
  let norm := (Mod.comap (inv α)).obj raw
  let E := finiteDiscreteCoefficientEquivalence B eR G hG (C₀.X i)
  let eN : E.inverse.obj norm ≅
      (constantSheaf (Scheme.ProEt.topology (C₀.X i))
        (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P :=
    (finiteDiscreteCoefficient_restrictionEncoding B eR G hG T (C₀.X i) (C₀.f i) M).some.symm ≪≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.f i)).mapIso e) ≪≫
      (comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.f i)).app F ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.X i)).mapIso eP.symm ≪≫
      (comparisonUpperStarConstantSheafIso (ULift.{u + 1} B) (C₀.X i)).app P
  have hp := encodedConstantFP B eR G hG (C₀.X i) P
  have hn := finitePresentation_of_iso
    ((E.counitIso.app norm).symm ≪≫ E.functor.mapIso eN).symm hp
  exact finitePresentation_of_comap (inv α) hn

private lemma internalComparisonConstructible
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Finite B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    [Scheme.IsConstructibleSheaf F] :
    IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).obj F)) := by
  obtain ⟨S, hS⟩ := Scheme.IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} B) ↦ M →ₗ[ULift.{u + 1} B] N)
    (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} B) ↦ M) (F := F)
  refine ⟨S, fun a ↦ ?_⟩
  have := hS a
  let E := finiteDiscreteCoefficientEquivalence B eR G hG T
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T
  let α := condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) (S.immersion a)
  apply localFinitePresentation_of_comap (inv α)
  apply internalLisseFP B eR G hG (S.domain a)
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (S.immersion a)).obj F)
  exact
    (finiteDiscreteCoefficient_restrictionEncoding B eR G hG T (S.domain a)
      (S.immersion a) (E.functor.obj (N.obj F))).some.symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (S.immersion a)).mapIso
      (E.unitIso.app (N.obj F)).symm ≪≫
    (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) (S.immersion a)).app F

/-- Constructible internal modules over a finite discrete coefficient ring are closed
under kernels. Source: Bhatt--Scholze, Section 5.1 and Lemma 5.4.1,
and the constructible Serre theorem in ConstructibleSheaf/KernelCokernel.lean.
(blueprint: lem-sfb-finite-discrete-internal-constructible-kernels)

Proof: encode internal modules as ordinary module-valued sheaves. Their local finite
presentations become finite locally constant sheaves, so the constructible objects descend
to the etale site. Full faithfulness lifts the given morphism. Its etale kernel is
constructible because a finite ring is noetherian. Exact comparison and the coefficient
equivalence identify its image with the original kernel. Conversely, a finite constant
module has a finite presentation, and encoding preserves finite sums and cokernels.
Apply this on each stratum to recover internal constructibility of the image kernel. -/
theorem finiteDiscrete_constructible_kernel
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [DiscreteTopology B] [Finite B] (T : Scheme.{u})
    (M N : FiniteDiscreteInternalModules B T) (f : M ⟶ N)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj B) T) M)
    (hN : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj B) T) N) :
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj B) T) (kernel f) := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  have : IsMonHom eR.hom := heR
  obtain ⟨G, hG, hforget⟩ := CategoryTheory.internalModuleAb_equivalence (ULift.{u + 1} B)
  have : G.IsEquivalence := hG
  let E := finiteDiscreteCoefficientEquivalence B eR G hforget T
  let H := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T ⋙ E.functor
  obtain ⟨F₁, h₁, ⟨e₁⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1} B) (finiteDiscreteCoefficient_constructible B eR G hforget T M hM)
  obtain ⟨F₂, h₂, ⟨e₂⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1} B) (finiteDiscreteCoefficient_constructible B eR G hforget T N hN)
  have : Scheme.IsConstructibleSheaf F₁ := h₁
  have : Scheme.IsConstructibleSheaf F₂ := h₂
  let i₁ : H.obj F₁ ≅ M := E.functor.mapIso e₁ ≪≫ E.counitIso.app M
  let i₂ : H.obj F₂ ≅ N := E.functor.mapIso e₂ ≪≫ E.counitIso.app N
  let f' : F₁ ⟶ F₂ := H.preimage (i₁.hom ≫ f ≫ i₂.inv)
  have : Scheme.IsConstructibleSheaf (kernel f') := Scheme.IsConstructibleSheaf.kernel f'
  let i : H.obj (kernel f') ≅ kernel f := PreservesKernel.iso H f' ≪≫
    kernel.mapIso (H.map f') f i₁ i₂ (by simp [f'])
  exact _root_.constructible_of_iso i
    (internalComparisonConstructible B eR G hforget T (kernel f'))

end AlgebraicGeometry.ProEtale.CondensedRing
