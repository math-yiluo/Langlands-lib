/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.WeilSheaf.DerivedHom
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.BifunctorHomCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Native Hom and source quasi-isomorphisms

Source: Stacks Tag 0A95, specialized to the native coefficient modules and Weil structure.
The proof uses a flat separator and the signed source-cone comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf.PrecompositionAux
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
open Mod
/-- The quotient map defining the relative tensor product is linear in its first factor. -/
private noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
private noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
private noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

private noncomputable def tensorComponent (M N : Mod C R) :
    (Mod.tensorLeft N).obj M ≅ M ⊗ N :=
  HasColimit.isoOfNatIso
    (diagramIsoParallelPair ((Mod.tensorLeftDiagram R N).flip.obj M)) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitRelativeTensorCofork M N)

omit [MonoidalPreadditive C] in
private lemma tensorComponent_π (M N : Mod C R) :
    Mod.tensorπ M N ≫ (tensorComponent M N).hom.hom = Mod.tensorObjπ M N := by
  have h := congrArg Mod.Hom.hom
    (show colimit.ι ((Mod.tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
        (tensorComponent M N).hom = relativeTensorπ M N by
      simp [tensorComponent, HasColimit.ι_isoOfNatIso_hom_assoc, relativeTensorCofork])
  exact h

private noncomputable def tensorIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents (fun M ↦ tensorComponent M N) (by
    intro M M' f
    apply Mod.tensorLeft_obj_hom_ext
    simp only [Mod.comp_hom', Mod.tensorπ_map_assoc]
    rw [tensorComponent_π, ← Category.assoc, tensorComponent_π]
    exact (Mod.tensorObjπ_whiskerRight f).symm)

private instance tensorAdditive (M : Mod C R) : (Mod.tensorLeft M).Additive :=
  (Mod.ihomAdjunction M).left_adjoint_additive

private lemma uncurry_add {P M N : Mod C R} (a b : P ⟶ (Mod.ihom M).obj N) :
    Mod.uncurryHom (a + b) = Mod.uncurryHom a + Mod.uncurryHom b := by
  simp only [Mod.uncurryHom, Mod.add_hom, MonoidalPreadditive.add_whiskerRight,
    Preadditive.add_comp]

private noncomputable def transposeAdd (P M N : Mod C R) :
    (P ⟶ (Mod.ihom M).obj N) ≃+ (M ⟶ (Mod.ihom P).obj N) :=
  { Mod.transposeEquiv with
    map_add' := by
      intro a b
      apply Mod.uncurryHom_injective
      change Mod.uncurryHom (Mod.transpose (a + b)) =
        Mod.uncurryHom (Mod.transpose a + Mod.transpose b)
      rw [uncurry_add, Mod.uncurryHom_transpose, Mod.uncurryHom_transpose,
        Mod.uncurryHom_transpose, uncurry_add, Preadditive.comp_add] }

private noncomputable def homEquiv (P M N : Mod C R) :
    (P ⟶ (Mod.ihom M).obj N) ≃+ ((Mod.tensorLeft P).obj M ⟶ N) :=
  (transposeAdd P M N).trans ((Mod.ihomAdjunction P).homAddEquiv M N).symm

private noncomputable def H : (Mod C R)ᵒᵖ ⥤ Mod C R ⥤ Mod C R where
  obj M := Mod.ihom M.unop
  map a := Mod.ihomMap a.unop
  map_id M := Mod.ihomMap_id M.unop
  map_comp a b := Mod.ihomMap_comp b.unop a.unop

private instance : (H (R := R)).Additive :=
  ⟨fun {_M _N} a b ↦ Mod.ihomMap_add a.unop b.unop⟩

private instance (M : (Mod C R)ᵒᵖ) : ((H (R := R)).obj M).Additive :=
  inferInstanceAs (Mod.ihom M.unop).Additive

private lemma homEquiv_right (P M N N' : Mod C R)
    (φ : P ⟶ (Mod.ihom M).obj N) (g : N ⟶ N') :
    homEquiv P M N' (φ ≫ (Mod.ihom M).map g) = homEquiv P M N φ ≫ g := by
  dsimp only [homEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  change ((Mod.ihomAdjunction P).homEquiv M N').symm
      (Mod.transpose (φ ≫ (Mod.ihom M).map g)) = _
  rw [Mod.transpose_comp_ihom_map]
  exact (Mod.ihomAdjunction P).homEquiv_naturality_right_symm _ _

private lemma homEquiv_left (P M M' N : Mod C R)
    (φ : P ⟶ (Mod.ihom M).obj N) (a : M' ⟶ M) :
    homEquiv P M' N (φ ≫ (Mod.ihomMap a).app N) =
      (Mod.tensorLeft P).map a ≫ homEquiv P M N φ := by
  change ((Mod.ihomAdjunction P).homEquiv M' N).symm
      (Mod.transpose (φ ≫ (Mod.ihomMap a).app N)) = _
  rw [Mod.transpose_comp_ihomMap]
  exact (Mod.ihomAdjunction P).homEquiv_naturality_left_symm _ _

private lemma acyclic_of_lifts {D : Type*} [Category D] [Abelian D]
    (P : D) (hP : IsSeparator P) (K : CochainComplex D ℤ)
    (hlift : ∀ (n : ℤ) (φ : P ⟶ K.X n), φ ≫ K.d n (n + 1) = 0 →
      ∃ ψ : P ⟶ K.X (n - 1), ψ ≫ K.d (n - 1) n = φ) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' K (n - 1) n (n + 1) (by simp) (by simp),
    ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  apply hP.def
  intro t
  obtain ⟨ψ, hψ⟩ := hlift n (t ≫ kernel.ι (K.d n (n + 1))) (by simp)
  change t ≫ kernel.ι (K.d n (n + 1)) ≫ cokernel.π (K.d (n - 1) n) = t ≫ 0
  rw [← Category.assoc, ← hψ]
  simp

private lemma ordinaryAcyclic [Abelian.HasFunctorialFlatResolution (Mod C R)]
    (K I : CochainComplex (Mod C R) ℤ)
    (hK : K.Acyclic) [I.IsKInjective] :
    (CochainComplex.bifunctorHomObj H K I).Acyclic := by
  obtain ⟨P, hP, hflat⟩ :=
    Abelian.exists_flat_separator_of_hasFunctorialFlatResolution (Mod C R)
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight P) :=
    hflat.tensorRight.preservesFiniteLimits
  have : PreservesFiniteLimits (Mod.tensorLeft P) :=
    preservesFiniteLimits_of_natIso (tensorIso P).symm
  have : (Mod.tensorLeft P).IsLeftAdjoint := (Mod.ihomAdjunction P).isLeftAdjoint
  have hT : (((Mod.tensorLeft P).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
    intro n
    change ((K.sc n).map (Mod.tensorLeft P)).Exact
    exact (hK n).map (Mod.tensorLeft P)
  apply acyclic_of_lifts P hP
  intro n φ hφ
  exact CochainComplex.BifunctorHom.exists_comp_d_eq P (Mod.tensorLeft P)
    (homEquiv P) (homEquiv_right P) (homEquiv_left P) n (n - 1) (by omega)
    (fun z hz ↦ CochainComplex.HomComplex.exists_δ_eq_of_isKInjective hT z hz
      (n - 1) (by omega)) φ hφ

private lemma ordinaryQuasiIso [Abelian.HasFunctorialFlatResolution (Mod C R)]
    {K L I : CochainComplex (Mod C R) ℤ}
    (a : K ⟶ L) [QuasiIso a] [I.IsKInjective] :
    QuasiIso (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a) := by
  let θ := (CochainComplex.exists_signedBifunctorConeIso (H (R := R)) I).choose
  have hc := ordinaryAcyclic (CochainComplex.mappingCone a) I
    ((CochainComplex.mappingCone.quasiIso_iff_acyclic a).1 inferInstance)
  have hs := HomologicalComplex.Acyclic.of_iso hc (θ K L a)
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hs ⊢
  have ht := (HomotopyCategory.subcategoryAcyclic (Mod C R)).prop_of_iso
    (((HomotopyCategory.quotient (Mod C R) (.up ℤ)).commShiftIso (-1)).app _) hs
  exact ((HomotopyCategory.subcategoryAcyclic (Mod C R)).prop_shift_iff_of_isStableUnderShift
    _ (-1 : ℤ)).1 ht

end AlgebraicGeometry.ProEtaleWeilSheaf.PrecompositionAux

namespace AlgebraicGeometry.ProEtaleWeilSheaf.PrecompositionTransport
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasCountableProducts C] [HasCountableProducts D]
  (U : C ⥤ D) [U.Additive]
  [∀ n : ℤ, PreservesLimitsOfShape (Discrete (CochainComplex.HomComplex.Triplet n)) U]
  (HC : Cᵒᵖ ⥤ C ⥤ C) [HC.Additive] [∀ M, (HC.obj M).Additive]
  (HD : Dᵒᵖ ⥤ D ⥤ D) [HD.Additive] [∀ M, (HD.obj M).Additive]
  (e : ∀ M N, U.obj ((HC.obj (op M)).obj N) ≅ (HD.obj (op (U.obj M))).obj (U.obj N))
  (er : ∀ M N N' (f : N ⟶ N'), U.map ((HC.obj (op M)).map f) ≫ (e M N').hom =
    (e M N).hom ≫ (HD.obj (op (U.obj M))).map (U.map f))
  (el : ∀ M M' N (f : M' ⟶ M), U.map ((HC.map f.op).app N) ≫ (e M' N).hom =
    (e M N).hom ≫ (HD.map (U.map f).op).app (U.obj N))
set_option quotPrecheck false
local notation "Uc" => U.mapHomologicalComplex (.up ℤ)
private noncomputable def component (K I : CochainComplex C ℤ) (n : ℤ) :
    U.obj ((CochainComplex.bifunctorHomObj HC K I).X n) ≅
      (CochainComplex.bifunctorHomObj HD ((Uc).obj K) ((Uc).obj I)).X n :=
  PreservesProduct.iso U _ ≪≫ Pi.mapIso (fun t : CochainComplex.HomComplex.Triplet n ↦
    e (K.X t.p) (I.X t.q))
@[reassoc]
private lemma component_π (K I : CochainComplex C ℤ)
    (n p q : ℤ) (hpq : p + n = q) :
    (component U HC HD e K I n).hom ≫
      CochainComplex.bifunctorHomπ HD ((Uc).obj K) ((Uc).obj I) n p q hpq =
    U.map (CochainComplex.bifunctorHomπ HC K I n p q hpq) ≫
      (e (K.X p) (I.X q)).hom := by
  dsimp only [component, Iso.trans_hom, CochainComplex.bifunctorHomπ]
  rw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc,
    PreservesProduct.iso_hom, piComparison_comp_π]

private noncomputable def complexIso (K I : CochainComplex C ℤ) :
    (Uc).obj (CochainComplex.bifunctorHomObj HC K I) ≅
      CochainComplex.bifunctorHomObj HD ((Uc).obj K) ((Uc).obj I) :=
  HomologicalComplex.Hom.isoOfComponents (component U HC HD e K I) (by
    intro n m hnm
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    rw [Category.assoc, CochainComplex.bifunctorHomObj_d_π _ _ _ n m p q hpq
      (p+n) (q-n) rfl (by omega)]
    simp only [Linear.comp_units_smul, Preadditive.comp_sub,
      component_π_assoc]
    rw [Category.assoc, component_π]
    change _ = U.map ((CochainComplex.bifunctorHomObj HC K I).d n m) ≫
      (U.map (CochainComplex.bifunctorHomπ HC K I m p q hpq) ≫ _)
    rw [← Functor.map_comp_assoc,
      CochainComplex.bifunctorHomObj_d_π _ _ _ n m p q hpq
        (p+n) (q-n) rfl (by omega)]
    simp only [Functor.map_units_smul, Functor.map_sub, Functor.map_comp,
      Linear.units_smul_comp, Preadditive.sub_comp, Category.assoc]
    rw [er, el]
    rfl)

include er el in
private lemma complexIso_left {K L I : CochainComplex C ℤ} (a : K ⟶ L) :
    (Uc).map (CochainComplex.bifunctorHomMapLeft (H := HC) (Y := I) a) ≫
      (complexIso U HC HD e er el K I).hom =
    (complexIso U HC HD e er el L I).hom ≫
      CochainComplex.bifunctorHomMapLeft (H := HD) (Y := (Uc).obj I) ((Uc).map a) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.bifunctorHomObj_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Category.assoc]
  change U.map ((CochainComplex.bifunctorHomMapLeft (H := HC) (Y := I) a).f n) ≫
      (component U HC HD e K I n).hom ≫ _ =
    (component U HC HD e L I n).hom ≫
      (CochainComplex.bifunctorHomMapLeft (H := HD) (Y := (Uc).obj I)
        ((Uc).map a)).f n ≫ _
  rw [component_π, CochainComplex.bifunctorHomMapLeft_f_π, component_π_assoc]
  rw [← Functor.map_comp_assoc,
    CochainComplex.bifunctorHomMapLeft_f_π, Functor.map_comp, Category.assoc, el]
  rfl
end AlgebraicGeometry.ProEtaleWeilSheaf.PrecompositionTransport

namespace AlgebraicGeometry.ProEtaleWeilSheaf.PrecompositionAux
open AlgebraicGeometry CategoryTheory.Endofunctor
attribute [local instance] Sheaf.symmetricCategory
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
set_option quotPrecheck false
local notation "U" => IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
local notation "Uc" => (U).mapHomologicalComplex (.up ℤ)
local notation "HW" => ProEtaleWeilSheaf.ihomBifunctor k₀ l X
local notation "HO" => H (C := Sheaf
  (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (WeilCoefficients l))
  (R := ProEtale.adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

private instance preservesProducts (n : ℤ) :
    PreservesLimitsOfShape (Discrete (CochainComplex.HomComplex.Triplet n)) (U) := by
  let A := ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
  exact
    (IsoAlgebra.Free.adjunction (WeilSheaf.frobeniusPullback k₀ l X)).rightAdjoint_preservesLimits
      |>.preservesLimitsOfShape

private noncomputable def forgetIhom (M N : ProEtaleWeilSheaf k₀ l X) :
    (U).obj (((HW).obj (op M)).obj N) ≅ ((HO).obj (op ((U).obj M))).obj ((U).obj N) :=
  Iso.refl _

private lemma forgetIhom_right (M N N' : ProEtaleWeilSheaf k₀ l X) (f : N ⟶ N') :
    (U).map (((HW).obj (op M)).map f) ≫ (forgetIhom M N').hom =
      (forgetIhom M N).hom ≫ ((HO).obj (op ((U).obj M))).map ((U).map f) := by
  simp only [forgetIhom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rfl

private lemma forgetIhom_left (M M' N : ProEtaleWeilSheaf k₀ l X) (f : M' ⟶ M) :
    (U).map (((HW).map f.op).app N) ≫ (forgetIhom M' N).hom =
      (forgetIhom M N).hom ≫ ((HO).map ((U).map f).op).app ((U).obj N) := by
  simp only [forgetIhom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rfl

private noncomputable def forgetHomIso
    (K I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (Uc).obj (CochainComplex.bifunctorHomObj HW K I) ≅
      CochainComplex.bifunctorHomObj HO ((Uc).obj K) ((Uc).obj I) :=
  PrecompositionTransport.complexIso (U) HW HO forgetIhom forgetIhom_right forgetIhom_left K I

private lemma forgetHomIso_left
    {K L I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (a : K ⟶ L) :
    (Uc).map (CochainComplex.bifunctorHomMapLeft (H := HW) (Y := I) a) ≫
        (forgetHomIso K I).hom =
      (forgetHomIso L I).hom ≫
        CochainComplex.bifunctorHomMapLeft (H := HO) (Y := (Uc).obj I) ((Uc).map a) :=
  PrecompositionTransport.complexIso_left (U) HW HO forgetIhom forgetIhom_right forgetIhom_left a

private lemma nativeQuasiIso
    {K L I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ}
    (a : K ⟶ L) [QuasiIso a] [I.IsKInjective] :
    QuasiIso (CochainComplex.bifunctorHomMapLeft (H := HW) (Y := I) a) := by
  let A := ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
  have : HasCoproducts.{u + 1} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{0} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : AB4OfSize.{u + 1} A := inferInstance
  have : AB4OfSize.{0} A := AB4OfSize_shrink.{0, u + 1} A
  have : HasExactColimitsOfShape (Discrete ℤ) A := inferInstance
  have : (U).PreservesKInjectiveComplexes :=
    IsoAlgebra.preservesKInjectiveComplexes_forget _
  have : CochainComplex.IsKInjective ((Uc).obj I) := inferInstance
  have : QuasiIso ((Uc).map a) := inferInstance
  have ho := ordinaryQuasiIso (I := (Uc).obj I) ((Uc).map a)
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (U)).mp
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (forgetHomIso L I) (forgetHomIso K I)
      (forgetHomIso_left (I := I) a).symm)).2 ho

end AlgebraicGeometry.ProEtaleWeilSheaf.PrecompositionAux

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Precomposition with a quasi-isomorphism is a quasi-isomorphism of native Hom complexes
into a K-injective Weil complex.

Source: Stacks Project, Tag 0A95, equivariant analogue, and Tag 08BJ
(used for `proposition-six-operations-dctf--15`).

Proof: forgetting Frobenius is right adjoint to exact integer-orbit induction, so
preserves K-injective complexes. It is exact and conservative and preserves products.
The product comparison identifies the forgotten native Hom complex and its
precomposition map with the ordinary coefficient-module Hom complex and its map.

Choose a flat separator P in the category of ordinary coefficient modules. Such a
separator exists by the sheaf flat-resolution theorem and its inheritance by internal
modules. The coequalizer definitions identify Mod.tensorLeft P with relative tensor
by P, which is exact. Transposition and tensor-Hom adjunction identify maps from P to
Hom(K,I) with cochains from K tensor P to I, using the sign (-1)^(p*n). If K is
acyclic, so is K tensor P; K-injectivity makes each such cocycle a coboundary. Thus
every map from P to a cycle lifts to the previous degree. The separator property
then kills the map kernel(d) to cokernel(previous d), proving Hom(K,I) acyclic.

Apply this to Cone(a). The signed source-cone isomorphism identifies Hom(Cone(a),I)
with Cone(Hom(a,I))[-1]. Shift stability and the cone criterion imply the ordinary
precomposition map is a quasi-isomorphism. Forgetting reflects this property,
proving the assertion for the actual native map, with no boundedness or monomorphism
assumption. -/
theorem quasiIso_bifunctorHomMapLeft
    {K L I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ}
    (a : K ⟶ L) [QuasiIso a] [I.IsKInjective] :
    QuasiIso (CochainComplex.bifunctorHomMapLeft
      (H := ihomBifunctor k₀ l X) (Y := I) a) := by
  exact PrecompositionAux.nativeQuasiIso a

end AlgebraicGeometry.ProEtaleWeilSheaf
