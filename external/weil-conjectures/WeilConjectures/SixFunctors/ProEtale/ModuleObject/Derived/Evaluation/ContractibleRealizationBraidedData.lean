/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.TerminalScalarRealization
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleOrdinaryRealization
import all WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! Braided structure of the terminal scalar realization.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2), Remark 3.2.
(blueprint: new-lem-zl-contractible-realization-braided-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

@[instance_reducible] private noncomputable def braidedTransport
    {B D : Type*} [Category* B] [Category* D]
    [MonoidalCategory B] [MonoidalCategory D] [BraidedCategory B] [BraidedCategory D]
    {F G : B ⥤ D} [F.Braided] (e : F ≅ G) : G.Braided := by
  let m : G.Monoidal := Functor.Monoidal.transport e
  let : NatTrans.IsMonoidal e.hom := Functor.Monoidal.natTransIsMonoidal_of_transport e
  exact { toMonoidal := m, braided := (Functor.LaxBraided.ofNatIso e).braided }

@[instance_reducible] private noncomputable def braidedInverse
    {B D : Type*} [Category* B] [Category* D]
    [MonoidalCategory B] [MonoidalCategory D] [BraidedCategory B] [BraidedCategory D]
    (e : B ≌ D) [e.functor.Braided] : e.inverse.Braided := by
  let m := e.inverseMonoidal
  exact
    { toMonoidal := m
      braided := e.toAdjunction.rightAdjointLaxMonoidal_μ_comp_map_braiding }

section Constant
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B]

private noncomputable def constantFixedUnit (M : ModuleCat.{u + 1} B) :
    (Functor.const Cᵒᵖ).obj M ⟶
      ((ConstantScalarRestriction.restriction J B).obj
        ((commutativeSiteConstantModuleFunctor J B).obj M)).obj where
  app U := ModuleCat.ofHom
    (X := M)
    (Y := ((ConstantScalarRestriction.restriction J B).obj
      ((commutativeSiteConstantModuleFunctor J B).obj M)).obj.obj U)
    { toFun := (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of M))).app U
      map_add' := map_add _
      map_smul' := by
        intro a x
        apply Eq.trans _
          (CategoryTheory.ConstantModuleDerivedProjection.restriction_scalar
            ((commutativeSiteConstantModuleFunctor J B).obj M) U a _).symm
        have := (realizationRingUnit_locallyBijective J B).1
        have := (realizationRingUnit_locallyBijective J B).2
        exact ((PresheafOfModules.sheafificationAdjunction
          (realizationRingUnit J B)).unit.app
            ((siteConstantModulePresheafGeneral (C := C) B).obj M)).app U
              |>.hom.map_smul a x }
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of M))).naturality f) x

private noncomputable def constantFixedMap (M : ModuleCat.{u + 1} B) :
    (constantSheaf J (ModuleCat.{u + 1} B)).obj M ⟶
      (ConstantScalarRestriction.restriction J B).obj
        ((commutativeSiteConstantModuleFunctor J B).obj M) :=
  { hom := sheafifyLift J (constantFixedUnit J B M)
      ((ConstantScalarRestriction.restriction J B).obj
        ((commutativeSiteConstantModuleFunctor J B).obj M)).property }

private theorem constantFixedMap_isIso (M : ModuleCat.{u + 1} B) :
    IsIso (constantFixedMap J B M) := by
  let f := constantFixedMap J B M
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj M)
  let α := constantFixedUnit J B M
  have hfac : η ≫ f.hom = α := toSheafify_sheafifyLift _ _ _
  have : Presheaf.IsLocallyInjective J α := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of M))) x y h
  have : Presheaf.IsLocallySurjective J α := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of M))) x
  have : Presheaf.IsLocallySurjective J η := inferInstance
  have : Presheaf.IsLocallyInjective J f.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J α hfac
  have : Presheaf.IsLocallySurjective J f.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  exact (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨inferInstance, inferInstance⟩

private noncomputable def constantFixedIso :
    constantSheaf J (ModuleCat.{u + 1} B) ≅ commutativeSiteConstantModuleFunctor J B ⋙
      ConstantScalarRestriction.restriction J B := by
  have (M : ModuleCat.{u + 1} B) := constantFixedMap_isIso J B M
  refine NatIso.ofComponents (fun M ↦ asIso (constantFixedMap J B M)) ?_
  intro M N f
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    (((commutativeSiteConstantModuleFunctor J B ⋙
      ConstantScalarRestriction.restriction J B).obj N).property)
  change toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
      sheafifyMap J ((Functor.const Cᵒᵖ).map f) ≫ (constantFixedMap J B N).hom =
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ (constantFixedMap J B M).hom ≫
      ((ConstantScalarRestriction.restriction J B).map
        ((commutativeSiteConstantModuleFunctor J B).map f)).hom
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, constantFixedMap, toSheafify_sheafifyLift]
  rw [← Category.assoc, toSheafify_sheafifyLift]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const Cᵒᵖ).map (AddCommGrpCat.ofHom f.hom.toAddMonoidHom))) U) x

private theorem constantBraided : Nonempty (commutativeSiteConstantModuleFunctor J B).Braided := by
  let e := (ConstantScalarRestriction.restriction J B).asEquivalence
  let : e.functor.Braided := ConstantScalarRestriction.restrictionBraided J B
  let := braidedInverse e
  let : (presheafToSheaf J (ModuleCat.{u + 1} B)).Braided :=
    (sfbSheafTensorStructure (A := ModuleCat.{u + 1} B) J).sheafificationBraided
  let : (Functor.const Cᵒᵖ : ModuleCat.{u + 1} B ⥤ Cᵒᵖ ⥤ ModuleCat.{u + 1} B).Braided :=
    { braided M N := by
        apply NatTrans.ext
        funext V
        change 𝟙 (M ⊗ N) ≫ (β_ M N).hom = (β_ M N).hom ≫ 𝟙 (N ⊗ M)
        simp only [Category.id_comp, Category.comp_id] }
  let : (constantSheaf J (ModuleCat.{u + 1} B)).Braided :=
    inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{u + 1} B)).Braided
  let i : constantSheaf J (ModuleCat.{u + 1} B) ⋙ e.inverse ≅
      commutativeSiteConstantModuleFunctor J B :=
    Functor.isoWhiskerRight (constantFixedIso J B) e.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  exact ⟨braidedTransport i⟩
end Constant

section Scalars
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {B : Type (u + 1)} [CommRing B] {R : Sheaf J CommRingCat.{u + 1}}
  (a : realizationRing J B ⟶ R)

-- Comparing the concrete sheaf tensor and scalar-extension structures needs extra reduction.
private theorem scalarBraided : Nonempty (SheafOfModules.flatScalarExtension J a).Braided := by
  let E := CategoryTheory.CochainPullback.extensionFunctor.{u + 1, u + 1, u} (J := J) a
  obtain ⟨d⟩ :=
    SheafOfModules.scalarExtension_constraint_coherence.{u + 1, u, u + 1}
      (realizationRing J B) R a
  let m := (CategoryTheory.ScalarMonoidalProof.scalarModuleCore.{u + 1, u, u + 1} J a d).toMonoidal
  have hb (M N : realizationModules J B) :
      E.map (β_ M N).hom ≫ (d.tensorIso N M).hom =
        (d.tensorIso M N).hom ≫ (β_ (E.obj M) (E.obj N)).hom := by
    dsimp only [E, CategoryTheory.CochainPullback.extensionFunctor]
    apply SheafOfModules.extensionTensor_ext.{u + 1, u, u + 1} (J := J) a M N _
    intro V x y
    change (d.tensorIso N M).hom.val.app V
        ((SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          (J := J) a (M ⊗ N) (β_ M N).hom).val.app V _) =
      (β_ (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := J) a M)
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := J) a N)).hom.val.app V
        ((d.tensorIso M N).hom.val.app V _)
    rw [SheafOfModules.extension_map_tmul.{u + 1, u, u + 1} (J := J)]
    have hp : (β_ M N).hom.val.app V
        (SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1}
          (J := J) _ M N V x y) =
        SheafOfModules.scalarExtensionConstraintPureTensor.{u + 1, u, u + 1} (J := J) _ N M V y x :=
      CategoryTheory.CochainPullback.moduleTmul_braiding.{u + 1, u + 1, u} (J := J) M N V x y
    rw [hp, d.insertion, d.insertion]
    exact (CategoryTheory.CochainPullback.moduleTmul_braiding.{u + 1, u + 1, u} (J := J)
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := J) a M)
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := J) a N) V _ _).symm
  let b : E.Braided :=
    { toMonoidal := m
      braided M N := by
        apply (cancel_mono (d.tensorIso N M).hom).mp
        change ((d.tensorIso M N).inv ≫ E.map (β_ M N).hom) ≫
            (d.tensorIso N M).hom =
          ((β_ (E.obj M) (E.obj N)).hom ≫ (d.tensorIso N M).inv) ≫
            (d.tensorIso N M).hom
        rw [Category.assoc, hb, Iso.inv_hom_id_assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id] }
  have hE : E = SheafOfModules.flatScalarExtension J a := by
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  exact hE ▸ ⟨b⟩
end Scalars

private theorem sectionBraided
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O] :
    Nonempty (InternalAbelianSheafModule.sectionModuleEquivalence J O).inverse.Braided := by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence J O
  obtain ⟨_, t, z, _, _, hn, ha, hl, hr, hb, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison J O
  let c : E.functor.CoreMonoidal :=
    Functor.CoreMonoidal.mk' z.symm (fun M N ↦ (t M N).symm)
      (by
        intro M N f P
        simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, tensorHom_id] using
          (hn M N P P f (𝟙 P)).symm)
      (by
        intro M N P f
        simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, id_tensorHom] using
          (hn P P M N (𝟙 P) f).symm)
      ha
      (by
        intro M
        apply (cancel_mono (λ_ _).hom).mp
        simp only [Iso.symm_inv, Category.assoc, Iso.inv_hom_id]
        rw [hl, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id])
      (by
        intro M
        apply (cancel_mono (ρ_ _).hom).mp
        simp only [Iso.symm_inv, Category.assoc, Iso.inv_hom_id]
        rw [hr, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id])
  let : E.functor.Braided :=
    { toMonoidal := c.toMonoidal
      braided M N := by
        apply (cancel_mono (t N M).hom).mp
        change ((t M N).inv ≫ E.functor.map (β_ M N).hom) ≫ (t N M).hom =
          ((β_ (E.functor.obj M) (E.functor.obj N)).hom ≫ (t N M).inv) ≫
            (t N M).hom
        rw [Category.assoc, ← hb, Iso.inv_hom_id_assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id] }
  exact ⟨braidedInverse E⟩

/-- The terminal scalar realization `L` admits a strong braided monoidal structure.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2), Remark 3.2.
(blueprint: new-lem-zl-contractible-realization-braided-data).

Proof: write `A = O_sec(U)` and `E` for the internal/section module equivalence. By
definition `L` is the composite of the constant-module functor `M ↦ M_J` over the constant
ring sheaf `A_J`, scalar extension along `A_J → O_sec`, and `E⁻¹`; a composite of braided
functors is braided, so it suffices to braid each factor.
(1) Constant modules: the sheafified additive unit `const M → M_J` is `A`-linear by the
constant-scalar action formula and locally bijective, so it gives a natural isomorphism
from the fixed-coefficient constant sheaf functor `Mod_A → Sh(C, Mod_A)` to the
constant-module functor followed by the constant-scalar restriction equivalence
`Mod(A_J) ≃ Sh(C, Mod_A)`. Constant presheaves are braided pointwise and sheafification is
braided; the restriction equivalence is braided, hence so is its inverse (adjoint braiding
equation), and transport along the isomorphism braids the constant-module functor.
(2) Scalar extension: the scalar-extension tensor and unit isomorphisms with their proved
coherence give a strong monoidal structure; the braiding equation holds on the generators
`(1 ⊗ m) ⊗ (1 ⊗ n)`, since both sides send them to `(1 ⊗ n) ⊗ (1 ⊗ m)`, hence holds.
(3) The internal/section tensor comparison (naturality, associativity, unit and symmetry
clauses) makes `E` braided, and its inverse is braided by the adjoint braiding equation. -/
theorem contractible_realization_braided_data
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U) :
    Nonempty (terminalScalarRealization J O U hU).Braided := by
  obtain ⟨c⟩ := constantBraided J (A J O U)
  obtain ⟨s⟩ := scalarBraided J (scalarMap J O U hU)
  obtain ⟨e⟩ := sectionBraided J O
  let := c
  let := s
  let := e
  exact ⟨inferInstanceAs
    ((commutativeSiteConstantModuleFunctor J (A J O U) ⋙
      SheafOfModules.flatScalarExtension J (scalarMap J O U hU)) ⋙
        (InternalAbelianSheafModule.sectionModuleEquivalence J O).inverse).Braided⟩

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
